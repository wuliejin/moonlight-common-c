#include "Limelight-internal.h"

#define FIRST_FRAME_MAX 1500
#define FIRST_FRAME_TIMEOUT_SEC 10

#define FIRST_FRAME_PORT 47996

static RTP_VIDEO_QUEUE rtpQueue;

static SOCKET rtpSocket = INVALID_SOCKET;
static SOCKET firstFrameSocket = INVALID_SOCKET;

static PPLT_CRYPTO_CONTEXT decryptionCtx;

#define VIDEO_TCP_MAX_CONNECTIONS 16
#define VIDEO_TCP_BUFFER_SIZE 65536
static SOCKET tcpSockets[VIDEO_TCP_MAX_CONNECTIONS];
static int tcpSocketCount;

static PLT_THREAD udpPingThread;
static PLT_THREAD receiveThread;
static PLT_THREAD decoderThread;

static bool receivedDataFromPeer;
static uint64_t firstDataTimeMs;
static bool receivedFullFrame;

// We can't request an IDR frame until the depacketizer knows
// that a packet was lost. This timeout bounds the time that
// the RTP queue will wait for missing/reordered packets.
#define RTP_QUEUE_DELAY 10

// This is the desired number of video packets that can be
// stored in the socket's receive buffer. 2048 is chosen
// because it should be large enough for all reasonable
// frame sizes (probably 2 or 3 frames) without using too
// much kernel memory with larger packet sizes. It also
// can smooth over transient pauses in network traffic
// and subsequent packet/frame bursts that follow.
#define RTP_RECV_PACKETS_BUFFERED 2048

// Initialize the video stream
void initializeVideoStream(void) {
    initializeVideoDepacketizer(StreamConfig.packetSize);
    RtpvInitializeQueue(&rtpQueue);
    decryptionCtx = PltCreateCryptoContext();
    receivedDataFromPeer = false;
    firstDataTimeMs = 0;
    receivedFullFrame = false;
}

// Clean up the video stream
void destroyVideoStream(void) {
    PltDestroyCryptoContext(decryptionCtx);
    destroyVideoDepacketizer();
    RtpvCleanupQueue(&rtpQueue);
}

// UDP Ping proc
static void VideoPingThreadProc(void* context) {
    char legacyPingData[] = { 0x50, 0x49, 0x4E, 0x47 };
    LC_SOCKADDR saddr;

    LC_ASSERT(VideoPortNumber != 0);

    memcpy(&saddr, &RemoteAddr, sizeof(saddr));
    SET_PORT(&saddr, VideoPortNumber);

    // We do not check for errors here. Socket errors will be handled
    // on the read-side in ReceiveThreadProc(). This avoids potential
    // issues related to receiving ICMP port unreachable messages due
    // to sending a packet prior to the host PC binding to that port.
    int pingCount = 0;
    while (!PltIsThreadInterrupted(&udpPingThread)) {
        if (VideoPingPayload.payload[0] != 0) {
            pingCount++;
            VideoPingPayload.sequenceNumber = BE32(pingCount);

            sendto(rtpSocket, (char*)&VideoPingPayload, sizeof(VideoPingPayload), 0, (struct sockaddr*)&saddr, AddrLen);
        }
        else {
            sendto(rtpSocket, legacyPingData, sizeof(legacyPingData), 0, (struct sockaddr*)&saddr, AddrLen);
        }

        PltSleepMsInterruptible(&udpPingThread, 500);
    }
}

// Receive state shared by the UDP and TCP paths. Only the receive thread touches it.
static int recvDecryptedSize, recvMinSize, recvReceiveSize, recvBufferSize;
static bool recvEncrypted;
static int waitingForVideoMs;

// Called when no video arrived for UDP_RECV_POLL_TIMEOUT_MS. Returns false to end the stream.
static bool handleVideoReceiveTimeout(void) {
    if (!receivedDataFromPeer) {
        // If we wait many seconds without ever receiving a video packet,
        // assume something is broken and terminate the connection.
        waitingForVideoMs += UDP_RECV_POLL_TIMEOUT_MS;
        if (waitingForVideoMs >= FIRST_FRAME_TIMEOUT_SEC * 1000) {
            Limelog("Terminating connection due to lack of video traffic\n");
            ListenerCallbacks.connectionTerminated(ML_ERROR_NO_VIDEO_TRAFFIC);
            return false;
        }
    }
    return true;
}

// Process one received packet of 'length' bytes that sits in encryptedBuffer (if video
// encryption is on) or in *buffer. The RTP queue may take ownership of *buffer, in which
// case *buffer is set to NULL. Returns false to end the stream.
static bool handleVideoPacket(char** buffer, char* encryptedBuffer, int length) {
    PRTP_PACKET packet;
    int queueStatus;
    int err = length;

    if (!receivedDataFromPeer) {
        receivedDataFromPeer = true;
        Limelog("Received first video packet after %d ms\n", waitingForVideoMs);

        firstDataTimeMs = PltGetMillis();
    }

#ifndef LC_FUZZING
    if (!receivedFullFrame) {
        if (PltGetMillis() - firstDataTimeMs >= FIRST_FRAME_TIMEOUT_SEC * 1000) {
            Limelog("Terminating connection due to lack of a successful video frame\n");
            ListenerCallbacks.connectionTerminated(ML_ERROR_NO_VIDEO_FRAME);
            return false;
        }
    }
#endif

    if (err < recvMinSize) {
        // Runt packet
        return true;
    }

    // Decrypt the packet into the buffer if encryption is enabled
    if (recvEncrypted) {
        PENC_VIDEO_HEADER encHeader = (PENC_VIDEO_HEADER)encryptedBuffer;

        // If this frame is below our current frame number, discard it before decryption
        // to save CPU cycles decrypting FEC shards for a frame we already reassembled.
        //
        // Since this is happening _before_ decryption, this packet is not trusted yet.
        // It's imperative that we do not mutate any state based on this packet until
        // after it has been decrypted successfully!
        //
        // It's possible for an attacker to inject a fake packet that has any value of
        // header fields they want, however this provides them no benefit because we will
        // simply drop said packet here (if it's below the current frame number) or it
        // will pass this check and be dropped during decryption (if contents is tampered)
        // or after decryption in the RTP queue (if it's a replay of a previous authentic
        // packet from the host).
        //
        // In short, an attacker spoofing this value via MITM or sending malicious values
        // impersonating the host from off-link doesn't gain them anything. If they have
        // a true MITM, they can DoS our connection by just dropping all our traffic, so
        // tampering with packets to fail this check doesn't accomplish anything they
        // couldn't already do. If they're not on-link, we just throw their malicious
        // traffic away (as mentioned in the paragraph above) and continue accepting
        // legitmate video traffic.
        if (encHeader->frameNumber && LE32(encHeader->frameNumber) < RtpvGetCurrentFrameNumber(&rtpQueue)) {
            return true;
        }

        if (!PltDecryptMessage(decryptionCtx, ALGORITHM_AES_GCM, 0,
                               (unsigned char*)StreamConfig.remoteInputAesKey, sizeof(StreamConfig.remoteInputAesKey),
                               encHeader->iv, sizeof(encHeader->iv),
                               encHeader->tag, sizeof(encHeader->tag),
                               ((unsigned char*)(encHeader + 1)), err - sizeof(ENC_VIDEO_HEADER), // The ciphertext is after the header
                               (unsigned char*)*buffer, &err)) {
            Limelog("Failed to decrypt video packet!\n");
            return true;
        }
    }

    // Convert fields to host byte-order
    packet = (PRTP_PACKET)&(*buffer)[0];
    packet->sequenceNumber = BE16(packet->sequenceNumber);
    packet->timestamp = BE32(packet->timestamp);
    packet->ssrc = BE32(packet->ssrc);

    queueStatus = RtpvAddPacket(&rtpQueue, packet, err, (PRTPV_QUEUE_ENTRY)&(*buffer)[recvDecryptedSize]);

    if (queueStatus == RTPF_RET_QUEUED) {
        // The queue owns the buffer
        *buffer = NULL;
    }

    return true;
}

// Open the TCP video connections offered by the host. Failures are not fatal: video keeps
// arriving over UDP until (and unless) a connection is attached on the host side.
static void connectVideoTcpSockets(void) {
    int i;

    tcpSocketCount = 0;
    if (VideoTcpConnections <= 0 || VideoTcpPortNumber == 0 || VideoPingPayload.payload[0] == 0) {
        return;
    }

    for (i = 0; i < VideoTcpConnections && i < VIDEO_TCP_MAX_CONNECTIONS; i++) {
        char hello[24];
        char reply[4];
        int got = 0;
        SOCKET s;

        s = connectTcpSocket(&RemoteAddr, AddrLen, VideoTcpPortNumber, 3);
        if (s == INVALID_SOCKET) {
            Limelog("Video TCP: connection %d to port %u failed: %d\n", i, VideoTcpPortNumber, (int)LastSocketError());
            break;
        }

        {
            int rcvbuf = 1024 * 1024;
            setsockopt(s, SOL_SOCKET, SO_RCVBUF, (char*)&rcvbuf, sizeof(rcvbuf));
        }

        // "SSVT", version, connection index, 2 reserved bytes, ping payload
        memset(hello, 0, sizeof(hello));
        memcpy(hello, "SSVT", 4);
        hello[4] = 2;
        hello[5] = (char)i;
        memcpy(&hello[8], VideoPingPayload.payload, sizeof(VideoPingPayload.payload));
        if (send(s, hello, sizeof(hello), 0) != sizeof(hello)) {
            Limelog("Video TCP: hello on connection %d failed: %d\n", i, (int)LastSocketError());
            closeSocket(s);
            break;
        }

        setNonFatalRecvTimeoutMs(s, 3000);
        while (got < (int)sizeof(reply)) {
            int r = (int)recv(s, &reply[got], sizeof(reply) - got, 0);
            if (r <= 0) {
                break;
            }
            got += r;
        }
        if (got != (int)sizeof(reply) || memcmp(reply, "SSVK", 4) != 0) {
            Limelog("Video TCP: host did not accept connection %d\n", i);
            closeSocket(s);
            break;
        }

        tcpSockets[tcpSocketCount++] = s;
    }

    Limelog("Video TCP: %d of %d connections attached\n", tcpSocketCount, VideoTcpConnections);
}

static void closeVideoTcpSockets(void) {
    int i;

    for (i = 0; i < tcpSocketCount; i++) {
        if (tcpSockets[i] != INVALID_SOCKET) {
            closeSocket(tcpSockets[i]);
            tcpSockets[i] = INVALID_SOCKET;
        }
    }
    tcpSocketCount = 0;
}

// Packets from different TCP connections are put back in send order before they reach the
// RTP queue, which treats any packet of a newer frame as the end of the current frame.
// A sequence gap is waited on for at most VIDEO_TCP_REORDER_TIMEOUT_MS (a connection that
// is retransmitting) before the missing packets are given up on.
#define VIDEO_TCP_REORDER_SLOTS 4096
#define VIDEO_TCP_REORDER_TIMEOUT_MS 40
static char* reorderData;
static int reorderLength[VIDEO_TCP_REORDER_SLOTS];
static uint32_t reorderSeq[VIDEO_TCP_REORDER_SLOTS];
static bool reorderUsed[VIDEO_TCP_REORDER_SLOTS];
static int reorderCount;
static uint32_t reorderNextSeq;
static uint64_t reorderGapStartMs;
static uint32_t reorderLatePackets;
static uint32_t reorderSkippedPackets;

static void resetReorderBuffer(void) {
    memset(reorderUsed, 0, sizeof(reorderUsed));
    reorderCount = 0;
    reorderNextSeq = 0;
    reorderGapStartMs = 0;
    reorderLatePackets = 0;
    reorderSkippedPackets = 0;
}

// Hand one packet to handleVideoPacket(). Returns false to end the stream.
static bool deliverTcpPacket(char** buffer, char* encryptedBuffer, const char* data, int length) {
    if (*buffer == NULL) {
        *buffer = (char*)malloc(recvBufferSize);
        if (*buffer == NULL) {
            Limelog("Video Receive: malloc() failed\n");
            ListenerCallbacks.connectionTerminated(-1);
            return false;
        }
    }
    memcpy(recvEncrypted ? encryptedBuffer : *buffer, data, length);
    return handleVideoPacket(buffer, encryptedBuffer, length);
}

// Deliver every buffered packet that is now in sequence. Returns false to end the stream.
static bool drainReorderBuffer(char** buffer, char* encryptedBuffer) {
    bool progressed = false;

    while (reorderCount > 0) {
        int slot = reorderNextSeq % VIDEO_TCP_REORDER_SLOTS;
        if (!reorderUsed[slot] || reorderSeq[slot] != reorderNextSeq) {
            break;
        }
        reorderUsed[slot] = false;
        reorderCount--;
        reorderNextSeq++;
        progressed = true;
        if (!deliverTcpPacket(buffer, encryptedBuffer, &reorderData[slot * recvReceiveSize], reorderLength[slot])) {
            return false;
        }
    }

    if (reorderCount == 0) {
        reorderGapStartMs = 0;
    }
    else if (progressed || reorderGapStartMs == 0) {
        // A new gap starts now
        reorderGapStartMs = PltGetMillis();
    }
    return true;
}

// Give up on the current gap and continue from the oldest buffered packet
static bool skipReorderGap(char** buffer, char* encryptedBuffer) {
    uint32_t seq = reorderNextSeq;

    // Every buffered packet lies within VIDEO_TCP_REORDER_SLOTS of reorderNextSeq
    while (!(reorderUsed[seq % VIDEO_TCP_REORDER_SLOTS] && reorderSeq[seq % VIDEO_TCP_REORDER_SLOTS] == seq)) {
        seq++;
    }
    reorderSkippedPackets += seq - reorderNextSeq;
    reorderNextSeq = seq;
    reorderGapStartMs = 0;
    return drainReorderBuffer(buffer, encryptedBuffer);
}

static bool checkReorderTimeout(char** buffer, char* encryptedBuffer) {
    if (reorderCount == 0 || PltGetMillis() - reorderGapStartMs < VIDEO_TCP_REORDER_TIMEOUT_MS) {
        return true;
    }
    return skipReorderGap(buffer, encryptedBuffer);
}

// Accept one packet from a TCP connection. Returns false to end the stream.
static bool insertTcpPacket(char** buffer, char* encryptedBuffer, uint32_t seq, const char* data, int length) {
    int32_t ahead = (int32_t)(seq - reorderNextSeq);
    int slot;

    if (ahead < 0) {
        // Its gap was already skipped
        reorderLatePackets++;
        return true;
    }

    if (ahead == 0 && reorderCount == 0) {
        reorderNextSeq++;
        return deliverTcpPacket(buffer, encryptedBuffer, data, length);
    }

    if (ahead >= VIDEO_TCP_REORDER_SLOTS) {
        // Far ahead of everything buffered: flush it all and resynchronize on this packet
        while (reorderCount > 0) {
            if (!skipReorderGap(buffer, encryptedBuffer)) {
                return false;
            }
        }
        reorderSkippedPackets += seq - reorderNextSeq;
        reorderNextSeq = seq + 1;
        return deliverTcpPacket(buffer, encryptedBuffer, data, length);
    }

    slot = seq % VIDEO_TCP_REORDER_SLOTS;
    if (reorderUsed[slot]) {
        return true;
    }
    memcpy(&reorderData[slot * recvReceiveSize], data, length);
    reorderLength[slot] = length;
    reorderSeq[slot] = seq;
    reorderUsed[slot] = true;
    reorderCount++;

    if (ahead == 0) {
        return drainReorderBuffer(buffer, encryptedBuffer);
    }
    if (reorderGapStartMs == 0) {
        reorderGapStartMs = PltGetMillis();
    }
    return true;
}

// Receive thread proc
static void VideoReceiveThreadProc(void* context) {
    int err;
    char* buffer;
    char* encryptedBuffer;
    bool useSelect;
    bool tcpMode;
    char* tcpBuffers[VIDEO_TCP_MAX_CONNECTIONS];
    int tcpFill[VIDEO_TCP_MAX_CONNECTIONS];
    int i;

    recvEncrypted = !!(EncryptionFeaturesEnabled & SS_ENC_VIDEO);
    recvDecryptedSize = StreamConfig.packetSize + MAX_RTP_HEADER_SIZE;
    recvMinSize = sizeof(RTP_PACKET) + ((EncryptionFeaturesEnabled & SS_ENC_VIDEO) ? sizeof(ENC_VIDEO_HEADER) : 0);
    recvReceiveSize = recvDecryptedSize + ((EncryptionFeaturesEnabled & SS_ENC_VIDEO) ? sizeof(ENC_VIDEO_HEADER) : 0);
    recvBufferSize = recvDecryptedSize + sizeof(RTPV_QUEUE_ENTRY);
    buffer = NULL;

    if (setNonFatalRecvTimeoutMs(rtpSocket, UDP_RECV_POLL_TIMEOUT_MS) < 0) {
        // SO_RCVTIMEO failed, so use select() to wait
        useSelect = true;
    }
    else {
        // SO_RCVTIMEO timeout set for recv()
        useSelect = false;
    }

    // Allocate a staging buffer to use for each received packet
    if (recvEncrypted) {
        encryptedBuffer = (char*)malloc(recvReceiveSize);
        if (encryptedBuffer == NULL) {
            Limelog("Video Receive: malloc() failed\n");
            ListenerCallbacks.connectionTerminated(-1);
            return;
        }
    }
    else {
        encryptedBuffer = NULL;
    }

    tcpMode = tcpSocketCount > 0;
    for (i = 0; i < VIDEO_TCP_MAX_CONNECTIONS; i++) {
        tcpFill[i] = 0;
        tcpBuffers[i] = NULL;
    }
    resetReorderBuffer();
    reorderData = NULL;
    if (tcpMode) {
        reorderData = (char*)malloc((size_t)VIDEO_TCP_REORDER_SLOTS * recvReceiveSize);
        if (reorderData == NULL) {
            Limelog("Video Receive: malloc() failed\n");
            ListenerCallbacks.connectionTerminated(-1);
            goto Exit;
        }
    }
    for (i = 0; i < tcpSocketCount; i++) {
        tcpBuffers[i] = (char*)malloc(VIDEO_TCP_BUFFER_SIZE);
        if (tcpBuffers[i] == NULL) {
            Limelog("Video Receive: malloc() failed\n");
            ListenerCallbacks.connectionTerminated(-1);
            goto Exit;
        }
    }

    waitingForVideoMs = 0;
    while (!PltIsThreadInterrupted(&receiveThread)) {
        struct pollfd pfds[VIDEO_TCP_MAX_CONNECTIONS + 1];
        int pfdSocket[VIDEO_TCP_MAX_CONNECTIONS + 1];
        int pfdCount;

        if (buffer == NULL) {
            buffer = (char*)malloc(recvBufferSize);
            if (buffer == NULL) {
                Limelog("Video Receive: malloc() failed\n");
                ListenerCallbacks.connectionTerminated(-1);
                break;
            }
        }

        if (!tcpMode) {
            err = recvUdpSocket(rtpSocket,
                                recvEncrypted ? encryptedBuffer : buffer,
                                recvReceiveSize,
                                useSelect);
            if (err < 0) {
                Limelog("Video Receive: recvUdpSocket() failed: %d\n", (int)LastSocketError());
                ListenerCallbacks.connectionTerminated(LastSocketFail());
                break;
            }
            else if (err == 0) {
                // Receive timed out; try again
                if (!handleVideoReceiveTimeout()) {
                    break;
                }
                continue;
            }

            if (!handleVideoPacket(&buffer, encryptedBuffer, err)) {
                break;
            }
            continue;
        }

        // TCP mode: wait on the UDP socket (packets sent before the TCP connections were
        // attached on the host) and every live TCP connection at once.
        pfdCount = 0;
        pfds[pfdCount].fd = rtpSocket;
        pfds[pfdCount].events = POLLIN;
        pfdSocket[pfdCount++] = -1;
        for (i = 0; i < tcpSocketCount; i++) {
            if (tcpSockets[i] != INVALID_SOCKET) {
                pfds[pfdCount].fd = tcpSockets[i];
                pfds[pfdCount].events = POLLIN;
                pfdSocket[pfdCount++] = i;
            }
        }
        if (pfdCount == 1) {
            Limelog("Video TCP: all connections lost, continuing on UDP\n");
            tcpMode = false;
            continue;
        }

        // Wake up often enough to notice a reorder gap timing out
        err = pollSockets(pfds, pfdCount, reorderCount > 0 ? 5 : UDP_RECV_POLL_TIMEOUT_MS);
        if (err < 0) {
            Limelog("Video Receive: pollSockets() failed: %d\n", (int)LastSocketError());
            ListenerCallbacks.connectionTerminated(LastSocketFail());
            break;
        }
        if (!checkReorderTimeout(&buffer, encryptedBuffer)) {
            break;
        }
        if (err == 0) {
            if (reorderCount == 0 && !handleVideoReceiveTimeout()) {
                break;
            }
            continue;
        }

        for (int p = 0; p < pfdCount; p++) {
            if (pfds[p].revents == 0) {
                continue;
            }

            if (pfdSocket[p] < 0) {
                // This won't block since the socket is readable. Errors here are ICMP
                // leftovers from before the host bound its port, so they're ignored.
                err = (int)recvfrom(rtpSocket, recvEncrypted ? encryptedBuffer : buffer, recvReceiveSize, 0, NULL, NULL);
                if (err > 0 && !handleVideoPacket(&buffer, encryptedBuffer, err)) {
                    goto Exit;
                }
            }
            else {
                int c = pfdSocket[p];
                int pos = 0;

                err = (int)recv(tcpSockets[c], tcpBuffers[c] + tcpFill[c], VIDEO_TCP_BUFFER_SIZE - tcpFill[c], 0);
                if (err <= 0) {
                    Limelog("Video TCP: connection %d closed: %d\n", c, err < 0 ? (int)LastSocketError() : 0);
                    closeSocket(tcpSockets[c]);
                    tcpSockets[c] = INVALID_SOCKET;
                    continue;
                }
                tcpFill[c] += err;

                // Each packet is preceded by its 16-bit length and 32-bit sequence number (big-endian)
                while (tcpFill[c] - pos >= 6) {
                    const unsigned char* hdr = (const unsigned char*)&tcpBuffers[c][pos];
                    int length = (hdr[0] << 8) | hdr[1];
                    uint32_t seq = ((uint32_t)hdr[2] << 24) | ((uint32_t)hdr[3] << 16) | ((uint32_t)hdr[4] << 8) | hdr[5];
                    if (length == 0 || length > recvReceiveSize) {
                        Limelog("Video TCP: bad packet length %d on connection %d\n", length, c);
                        closeSocket(tcpSockets[c]);
                        tcpSockets[c] = INVALID_SOCKET;
                        pos = tcpFill[c];
                        break;
                    }
                    if (tcpFill[c] - pos - 6 < length) {
                        break;
                    }

                    if (!insertTcpPacket(&buffer, encryptedBuffer, seq, &tcpBuffers[c][pos + 6], length)) {
                        goto Exit;
                    }
                    pos += 6 + length;
                }

                memmove(tcpBuffers[c], tcpBuffers[c] + pos, tcpFill[c] - pos);
                tcpFill[c] -= pos;
            }

            if (buffer == NULL) {
                buffer = (char*)malloc(recvBufferSize);
                if (buffer == NULL) {
                    Limelog("Video Receive: malloc() failed\n");
                    ListenerCallbacks.connectionTerminated(-1);
                    goto Exit;
                }
            }
        }
    }

Exit:
    if (reorderData != NULL) {
        Limelog("Video TCP: %u packets skipped after reorder timeouts, %u arrived too late\n",
                reorderSkippedPackets, reorderLatePackets);
        free(reorderData);
        reorderData = NULL;
    }
    for (i = 0; i < VIDEO_TCP_MAX_CONNECTIONS; i++) {
        if (tcpBuffers[i] != NULL) {
            free(tcpBuffers[i]);
        }
    }

    if (buffer != NULL) {
        free(buffer);
    }

    if (encryptedBuffer != NULL) {
        free(encryptedBuffer);
    }
}

void notifyKeyFrameReceived(void) {
    // Remember that we got a full frame successfully
    receivedFullFrame = true;
}

// Decoder thread proc
static void VideoDecoderThreadProc(void* context) {
    while (!PltIsThreadInterrupted(&decoderThread)) {
        VIDEO_FRAME_HANDLE frameHandle;
        PDECODE_UNIT decodeUnit;

        if (!LiWaitForNextVideoFrame(&frameHandle, &decodeUnit)) {
            return;
        }

        LiCompleteVideoFrame(frameHandle, VideoCallbacks.submitDecodeUnit(decodeUnit));
    }
}

// Read the first frame of the video stream
int readFirstFrame(void) {
    // All that matters is that we close this socket.
    // This starts the flow of video on Gen 3 servers.

    closeSocket(firstFrameSocket);
    firstFrameSocket = INVALID_SOCKET;

    return 0;
}

// Terminate the video stream
void stopVideoStream(void) {
    if (!receivedDataFromPeer) {
        Limelog("No video traffic was ever received from the host!\n");
    }

    VideoCallbacks.stop();

    // Wake up client code that may be waiting on the decode unit queue
    stopVideoDepacketizer();

    PltInterruptThread(&udpPingThread);
    PltInterruptThread(&receiveThread);
    if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
        PltInterruptThread(&decoderThread);
    }

    if (firstFrameSocket != INVALID_SOCKET) {
        shutdownTcpSocket(firstFrameSocket);
    }

    PltJoinThread(&udpPingThread);
    PltJoinThread(&receiveThread);
    if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
        PltJoinThread(&decoderThread);
    }

    if (firstFrameSocket != INVALID_SOCKET) {
        closeSocket(firstFrameSocket);
        firstFrameSocket = INVALID_SOCKET;
    }
    if (rtpSocket != INVALID_SOCKET) {
        closeSocket(rtpSocket);
        rtpSocket = INVALID_SOCKET;
    }
    closeVideoTcpSockets();

    VideoCallbacks.cleanup();
}

// Start the video stream
int startVideoStream(void* rendererContext, int drFlags) {
    int err;

    firstFrameSocket = INVALID_SOCKET;

    // This must be called before the decoder thread starts submitting
    // decode units
    LC_ASSERT(NegotiatedVideoFormat != 0);
    err = VideoCallbacks.setup(NegotiatedVideoFormat, StreamConfig.width,
        StreamConfig.height, StreamConfig.fps, rendererContext, drFlags);
    if (err != 0) {
        return err;
    }

    rtpSocket = bindUdpSocket(RemoteAddr.ss_family, &LocalAddr, AddrLen,
                              RTP_RECV_PACKETS_BUFFERED * (StreamConfig.packetSize + MAX_RTP_HEADER_SIZE),
                              SOCK_QOS_TYPE_VIDEO);
    if (rtpSocket == INVALID_SOCKET) {
        VideoCallbacks.cleanup();
        return LastSocketError();
    }

    VideoCallbacks.start();

    connectVideoTcpSockets();

    err = PltCreateThread("VideoRecv", VideoReceiveThreadProc, NULL, &receiveThread);
    if (err != 0) {
        VideoCallbacks.stop();
        closeSocket(rtpSocket);
        closeVideoTcpSockets();
        VideoCallbacks.cleanup();
        return err;
    }

    if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
        err = PltCreateThread("VideoDec", VideoDecoderThreadProc, NULL, &decoderThread);
        if (err != 0) {
            VideoCallbacks.stop();
            PltInterruptThread(&receiveThread);
            PltJoinThread(&receiveThread);
            closeSocket(rtpSocket);
            VideoCallbacks.cleanup();
            return err;
        }
    }

    if (AppVersionQuad[0] == 3) {
        // Connect this socket to open port 47998 for our ping thread
        firstFrameSocket = connectTcpSocket(&RemoteAddr, AddrLen,
                                            FIRST_FRAME_PORT, FIRST_FRAME_TIMEOUT_SEC);
        if (firstFrameSocket == INVALID_SOCKET) {
            VideoCallbacks.stop();
            stopVideoDepacketizer();
            PltInterruptThread(&receiveThread);
            if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
                PltInterruptThread(&decoderThread);
            }
            PltJoinThread(&receiveThread);
            if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
                PltJoinThread(&decoderThread);
            }
            closeSocket(rtpSocket);
            VideoCallbacks.cleanup();
            return LastSocketError();
        }
    }

    // Start pinging before reading the first frame so GFE knows where
    // to send UDP data
    err = PltCreateThread("VideoPing", VideoPingThreadProc, NULL, &udpPingThread);
    if (err != 0) {
        VideoCallbacks.stop();
        stopVideoDepacketizer();
        PltInterruptThread(&receiveThread);
        if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
            PltInterruptThread(&decoderThread);
        }
        PltJoinThread(&receiveThread);
        if ((VideoCallbacks.capabilities & (CAPABILITY_DIRECT_SUBMIT | CAPABILITY_PULL_RENDERER)) == 0) {
            PltJoinThread(&decoderThread);
        }
        closeSocket(rtpSocket);
        if (firstFrameSocket != INVALID_SOCKET) {
            closeSocket(firstFrameSocket);
            firstFrameSocket = INVALID_SOCKET;
        }
        VideoCallbacks.cleanup();
        return err;
    }

    if (AppVersionQuad[0] == 3) {
        // Read the first frame to start the flow of video
        err = readFirstFrame();
        if (err != 0) {
            stopVideoStream();
            return err;
        }
    }

    return 0;
}

const RTP_VIDEO_STATS* LiGetRTPVideoStats(void) {
    return &rtpQueue.stats;
}
