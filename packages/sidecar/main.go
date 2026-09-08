package main

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
	"github.com/pion/interceptor"
	"github.com/pion/interceptor/pkg/intervalpli"
	"github.com/pion/logging"
	"github.com/pion/rtcp"
	"github.com/pion/rtp"
	"github.com/pion/webrtc/v4"
)

// The previous defaults were a handful of individually-run community STUN
// servers; all 8 stopped responding at some point (verified via a direct
// STUN binding request), which is why ICE connectivity regressed even
// though nothing in this repo's code or Docker networking changed.
// These are established, highly-available public STUN services instead.
var defaultStunServers = []string{
	"stun:stun.l.google.com:19302",
	"stun:stun1.l.google.com:19302",
	"stun:stun.cloudflare.com:3478",
	"stun:global.stun.twilio.com:3478",
}

func getStunServers() []string {
	if env := os.Getenv("STUN_SERVERS"); env != "" {
		return strings.Split(env, ",")
	}
	return defaultStunServers
}

func envOrDefault(key, def string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return def
}

func envIntOrDefault(key string, def int) int {
	if v := os.Getenv(key); v != "" {
		if n, err := strconv.Atoi(v); err == nil {
			return n
		}
	}
	return def
}

// clampToPowerOfTwo rounds n down to the nearest power of two within [min, max].
// libvpx's VP8 token partitions (-slices) only accept 1/2/4/8.
func clampToPowerOfTwo(n, min, max int) int {
	if n < min {
		return min
	}
	if n > max {
		return max
	}
	p := min
	for p*2 <= n {
		p *= 2
	}
	return p
}

func getFfmpegPath() string {
	return envOrDefault("FFMPEG_PATH", "ffmpeg")
}

// parseBitrateBps parses an ffmpeg-style bitrate string ("4500k", "128k",
// "1200000") into bits per second. Returns 0 if it can't be parsed, so
// callers should treat that as "unknown" rather than a real zero bitrate.
func parseBitrateBps(s string) int {
	s = strings.TrimSpace(strings.ToLower(s))
	mult := 1
	if strings.HasSuffix(s, "k") {
		mult = 1000
		s = strings.TrimSuffix(s, "k")
	} else if strings.HasSuffix(s, "m") {
		mult = 1000000
		s = strings.TrimSuffix(s, "m")
	}
	n, err := strconv.Atoi(s)
	if err != nil {
		return 0
	}
	return n * mult
}

func debugLogsEnabled() bool {
	return os.Getenv("SIDECAR_DEBUG_LOGS") == "1"
}

func debugf(format string, args ...any) {
	if debugLogsEnabled() {
		log.Printf(format, args...)
	}
}

// NTP epoch offset: seconds between 1900-01-01 and 1970-01-01
const ntpEpochOffset = 2208988800

func toNTPTime(t time.Time) uint64 {
	secs := uint64(t.Unix()) + ntpEpochOffset
	frac := uint64(t.Nanosecond()) * (1 << 32) / 1e9
	return secs<<32 | frac
}

func isVP8KeyframeStart(payload []byte) bool {
	if len(payload) < 2 {
		return false
	}
	i := 0

	// VP8 payload descriptor
	b0 := payload[i]
	x := (b0 & 0x80) != 0
	s := (b0 & 0x10) != 0
	pid := b0 & 0x0F
	i++

	if !s || pid != 0 {
		return false
	}

	if x {
		if len(payload) <= i {
			return false
		}
		ext := payload[i]
		i++

		if (ext & 0x80) != 0 {
			if len(payload) <= i {
				return false
			}

			// M bit => 16-bit PictureID, else 8-bit
			if (payload[i] & 0x80) != 0 {
				i += 2
			} else {
				i += 1
			}
		}

		// L: TL0PICIDX present
		if (ext & 0x40) != 0 {
			i += 1
		}

		// T or K => one extra octet
		if (ext&0x20) != 0 || (ext&0x10) != 0 {
			i += 1
		}
	}
	if len(payload) <= i {
		return false
	}
	// VP8 frame tag: bit 0 == frame type
	// 0 = keyframe, 1 = interframe
	return (payload[i] & 0x01) == 0
}

func rtpElapsed(ts, base, clockRate uint32) time.Duration {
	return time.Duration((uint64(ts-base) * uint64(time.Second)) / uint64(clockRate))
}

func smoothDuration(prev, sample time.Duration) time.Duration {
	if prev <= 0 {
		return sample
	}
	return (prev*9 + sample) / 10
}

func maxDuration(a, b time.Duration) time.Duration {
	if a > b {
		return a
	}
	return b
}

func (s *Sidecar) resetSyncTiming() {
	s.timingMu.Lock()
	defer s.timingMu.Unlock()

	s.streamBaseWall = time.Time{}
	s.streamBaseSet = false
	s.videoTiming = TrackTiming{}
	s.audioTiming = TrackTiming{}
}

func (s *Sidecar) drainRTPQueues() {
	for {
		select {
		case <-s.videoQueue:
		default:
			goto drainAudio
		}
	}

drainAudio:
	for {
		select {
		case <-s.audioQueue:
		default:
			return
		}
	}
}

func (s *Sidecar) resetPeerStreamState() {
	s.peersLock.RLock()
	defer s.peersLock.RUnlock()

	for _, peer := range s.peers {
		peer.mu.Lock()
		peer.Started = false
		peer.mu.Unlock()
	}
}

func (s *Sidecar) computeTrackDelay(kind string, ts uint32, now time.Time) time.Duration {
	s.timingMu.Lock()
	defer s.timingMu.Unlock()

	if !s.streamBaseSet {
		s.streamBaseSet = true
		s.streamBaseWall = now
	}

	var current *TrackTiming
	var other *TrackTiming
	var clockRate uint32

	switch kind {
	case "video":
		current = &s.videoTiming
		other = &s.audioTiming
		clockRate = 90000
	case "audio":
		current = &s.audioTiming
		other = &s.videoTiming
		clockRate = 48000
	default:
		return 0
	}

	if !current.initialized {
		current.initialized = true
		current.baseRTP = ts
	}

	mediaElapsed := rtpElapsed(ts, current.baseRTP, clockRate)
	expectedWall := s.streamBaseWall.Add(mediaElapsed)

	observedLatency := now.Sub(expectedWall)
	if observedLatency < 0 {
		observedLatency = 0
	}

	current.latency = smoothDuration(current.latency, observedLatency)

	// Only video chases audio's latency to keep lip-sync, never the other
	// way around: a real deployment showed video's latency climbing during
	// its known congestion ceiling (queue-full drops, climbing RTCP
	// packetsLost) even with a 150ms cap on how much it could pull audio
	// down -- video revisits that ceiling every few seconds under load, so
	// audio kept hitting the cap over and over, which was still audible as
	// stutter. Audio has effectively zero tolerance for that; video, being
	// already visibly degraded under congestion, has much more. So audio is
	// paced only by its own latency here, immune to whatever video is doing.
	targetLatency := current.latency
	if kind == "video" && other.initialized {
		targetLatency = maxDuration(targetLatency, other.latency)
	}

	targetWall := expectedWall.Add(targetLatency).Add(s.syncBuffer)
	if kind == "video" {
		targetWall = targetWall.Add(s.videoBias)
	}

	delay := targetWall.Sub(now)
	if delay < 0 {
		return 0
	}

	return delay
}

func cloneRTPPacket(src *rtp.Packet) *rtp.Packet {
	raw, err := src.Marshal()
	if err != nil {
		return nil
	}

	dst := &rtp.Packet{}
	if err := dst.Unmarshal(raw); err != nil {
		return nil
	}

	return dst
}

type TrackTiming struct {
	initialized bool
	baseRTP     uint32
	latency     time.Duration
}

type createInFlight struct {
	done chan struct{}
	sdp  string
	err  error
}

type Peer struct {
	ID              string
	PC              *webrtc.PeerConnection
	VideoTrack      *webrtc.TrackLocalStaticRTP
	AudioTrack      *webrtc.TrackLocalStaticRTP
	VideoSSRC       uint32
	AudioSSRC       uint32
	Active          bool
	Started         bool
	mu              sync.Mutex
	stopSR          chan struct{}

	// Per-peer outbound queues, drained by this peer's own writer goroutine
	// (see peerWriteLoop). Forwarding used to call WriteRTP for every peer
	// synchronously (via a shared sync.WaitGroup) from within the single
	// shared processVideoRTP/processAudioRTP loop, so ONE peer with a slow
	// WriteRTP -- e.g. a real client over a congested/lossy internet path,
	// where SRTP-write latency can spike well above a real client on a local
	// Docker bridge -- stalled delivery to every other peer too, and stalled
	// the shared pacing clock computing the next packet's delay. Giving each
	// peer its own buffered channel and writer goroutine means a slow peer
	// only ever backs up (and drops from) its own queue. Never closed (see
	// peerWriteLoop) -- its writer goroutine exits via stopSR instead.
	videoOut chan *rtp.Packet
	audioOut chan *rtp.Packet
	// Trickle ICE candidates that arrive before the remote description is
	// set can't be applied yet (pion rejects them with "remote description
	// is not set"); buffer them here and flush once SetAnswer succeeds.
	pendingCandidates []webrtc.ICECandidateInit

	// Real packet loss/jitter as reported back by this peer over RTCP
	// Receiver Reports -- guarded by mu, filled in by readSenderRTCP. pion
	// v4.0.5's own GetStats() doesn't collect these for RTP senders, so we
	// read the RTCP feedback channel directly instead.
	videoPacketsLost uint32
	videoJitter      float64 // seconds
	audioPacketsLost uint32
	audioJitter      float64 // seconds
}

// RTP clock rates for the tracks created in CreatePeer -- needed to convert
// RTCP jitter (reported in RTP timestamp units, RFC 3550 6.4.1) to seconds.
const (
	videoClockRate = 90000
	audioClockRate = 48000
)

// readSenderRTCP reads RTCP Receiver Reports sent back by the peer for the
// track this sender is sending, and records the latest packet-loss/jitter
// figures on peer. This is real feedback from the actual network path to
// that peer (e.g. a TS6 client's connection), not anything visible from
// ffmpeg's own output -- see the RTP-read-gap diagnostic for that side.
func readSenderRTCP(peer *Peer, sender *webrtc.RTPSender, kind string) {
	clockRate := float64(videoClockRate)
	if kind == "audio" {
		clockRate = audioClockRate
	}

	for {
		packets, _, err := sender.ReadRTCP()
		if err != nil {
			return
		}
		for _, pkt := range packets {
			rr, ok := pkt.(*rtcp.ReceiverReport)
			if !ok || len(rr.Reports) == 0 {
				continue
			}
			report := rr.Reports[0]
			jitterSeconds := float64(report.Jitter) / clockRate
			peer.mu.Lock()
			if kind == "video" {
				peer.videoPacketsLost = report.TotalLost
				peer.videoJitter = jitterSeconds
			} else {
				peer.audioPacketsLost = report.TotalLost
				peer.audioJitter = jitterSeconds
			}
			peer.mu.Unlock()
		}
	}
}

// peerWriteLoop serializes RTP writes to one peer's track, fed by that
// peer's own buffered channel. Running one of these per peer per track is
// what lets a single congested/slow peer fall behind (and drop packets from
// its own queue) without affecting any other peer or the shared pacing loop
// that feeds these channels -- see the comment on Peer.videoOut/audioOut.
// Stops on stopSR (the same peer-teardown signal used elsewhere) rather than
// on the channel being closed -- processVideoRTP/processAudioRTP send into
// ch without holding any lock, so closing it here could race a send from
// there and panic; stopSR is only ever closed once, under s.peersLock, by
// whichever teardown path removes this peer.
func peerWriteLoop(ch chan *rtp.Packet, track *webrtc.TrackLocalStaticRTP, stop <-chan struct{}) {
	for {
		select {
		case <-stop:
			return
		case pkt := <-ch:
			_ = track.WriteRTP(pkt)
		}
	}
}

type Sidecar struct {
	peers     map[string]*Peer
	peersLock sync.RWMutex
	creating  map[string]*createInFlight

	videoPort int
	audioPort int
	videoConn *net.UDPConn
	audioConn *net.UDPConn

	ffmpeg     *exec.Cmd
	ffmpegLock sync.Mutex
	source     string
	running    bool
	prefetches []*prefetchStream

	// Atomic timestamps for RTCP Sender Report generation
	lastVideoRTPTs uint64 // atomic: latest video RTP timestamp seen
	lastAudioRTPTs uint64 // atomic: latest audio RTP timestamp seen
	videoPktCount  uint64 // atomic
	videOctetCount uint64 // atomic
	audioPktCount  uint64 // atomic
	audioOctetCount uint64 // atomic
	
	videoQueue chan *rtp.Packet
	audioQueue chan *rtp.Packet

	// Stream pacing / A/V alignment state
	timingMu       sync.Mutex
	streamBaseWall time.Time
	streamBaseSet  bool
	videoTiming    TrackTiming
	audioTiming    TrackTiming
	syncBuffer     time.Duration
	videoBias      time.Duration
}

func NewSidecar() *Sidecar {
	return &Sidecar{
		peers:      make(map[string]*Peer),
		creating:   make(map[string]*createInFlight),
		syncBuffer: time.Duration(envIntOrDefault("SYNC_PLAYOUT_BUFFER_MS", 50)) * time.Millisecond,
		videoBias:  time.Duration(envIntOrDefault("SYNC_VIDEO_BIAS_MS", 0)) * time.Millisecond,
		videoQueue: make(chan *rtp.Packet, envIntOrDefault("VIDEO_QUEUE_SIZE", 1024)),
		audioQueue: make(chan *rtp.Packet, envIntOrDefault("AUDIO_QUEUE_SIZE", 2048)),
	}
}


func (s *Sidecar) StartRTP() error {
	var err error

	s.videoConn, err = net.ListenUDP("udp4", &net.UDPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 0})
	if err != nil {
		return fmt.Errorf("bind video UDP: %w", err)
	}
	_ = s.videoConn.SetReadBuffer(envIntOrDefault("VIDEO_RTP_READ_BUFFER", 4*1024*1024))
	s.videoPort = s.videoConn.LocalAddr().(*net.UDPAddr).Port

	s.audioConn, err = net.ListenUDP("udp4", &net.UDPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 0})
	if err != nil {
		return fmt.Errorf("bind audio UDP: %w", err)
	}
	_ = s.audioConn.SetReadBuffer(envIntOrDefault("AUDIO_RTP_READ_BUFFER", 1*1024*1024))
	s.audioPort = s.audioConn.LocalAddr().(*net.UDPAddr).Port

	log.Printf("[RTP] Video port: %d, Audio port: %d", s.videoPort, s.audioPort)
	s.running = true

	go s.readVideoRTP()
	go s.readAudioRTP()
	go s.processVideoRTP()
	go s.processAudioRTP()

	return nil
}

func (s *Sidecar) readVideoRTP() {
	buf := make([]byte, 1500)
	pkt := &rtp.Packet{}
	count := 0
	var lastReadWall time.Time

	for s.running {
		n, err := s.videoConn.Read(buf)
		readWall := time.Now()
		if err != nil {
			if s.running {
				log.Printf("[RTP] Video read error: %v", err)
			}
			return
		}

		if err := pkt.Unmarshal(buf[:n]); err != nil {
			continue
		}

		// Diagnostic: a gap here means ffmpeg itself went quiet on the
		// video RTP output for a while (source read stall, encoder
		// hiccup, CPU contention from e.g. a peer joining, etc) -- as
		// opposed to a gap only appearing further downstream (queueing,
		// WebRTC send, network), which would point at the sidecar or
		// the network instead of ffmpeg.
		if !lastReadWall.IsZero() {
			if gap := readWall.Sub(lastReadWall); gap > 150*time.Millisecond {
				log.Printf("[VIDEO] gap of %v between ffmpeg RTP reads (ts=%d)", gap, pkt.Timestamp)
			}
		}
		lastReadWall = readWall

		// Track RTP stats used by optional debug / legacy reporting paths
		atomic.StoreUint64(&s.lastVideoRTPTs, uint64(pkt.Timestamp))
		atomic.AddUint64(&s.videoPktCount, 1)
		atomic.AddUint64(&s.videOctetCount, uint64(len(pkt.Payload)))

		count++
		if count <= 3 || count%600 == 0 {
			debugf("[VIDEO] #%d ts=%d (%.3fs) marker=%v", count, pkt.Timestamp, float64(pkt.Timestamp)/90000.0, pkt.Marker)
		}

		cloned := cloneRTPPacket(pkt)
		if cloned == nil {
			continue
		}

		select {
		case s.videoQueue <- cloned:
		default:
			if count%120 == 0 {
				log.Printf("[VIDEO] queue full, dropping packet ts=%d", cloned.Timestamp)
			}
		}
	}
}

func (s *Sidecar) readAudioRTP() {
	buf := make([]byte, 1500)
	pkt := &rtp.Packet{}
	count := 0
	var lastReadWall time.Time

	for s.running {
		n, err := s.audioConn.Read(buf)
		readWall := time.Now()
		if err != nil {
			if s.running {
				log.Printf("[RTP] Audio read error: %v", err)
			}
			return
		}

		if err := pkt.Unmarshal(buf[:n]); err != nil {
			continue
		}

		// Diagnostic: a gap here means ffmpeg itself went quiet on the
		// audio RTP output for a while (source read stall, encoder
		// hiccup, etc) -- as opposed to a gap only appearing further
		// downstream (queueing, WebRTC send, network), which would
		// point at the sidecar or the network instead of ffmpeg/source.
		if !lastReadWall.IsZero() {
			if gap := readWall.Sub(lastReadWall); gap > 150*time.Millisecond {
				log.Printf("[AUDIO] gap of %v between ffmpeg RTP reads (ts=%d)", gap, pkt.Timestamp)
			}
		}
		lastReadWall = readWall

		// Track latest timestamp for RTCP Sender Reports
		atomic.StoreUint64(&s.lastAudioRTPTs, uint64(pkt.Timestamp))
		atomic.AddUint64(&s.audioPktCount, 1)
		atomic.AddUint64(&s.audioOctetCount, uint64(len(pkt.Payload)))

		count++
		if count <= 3 || count%1000 == 0 {
			debugf("[AUDIO] #%d ts=%d (%.3fs)", count, pkt.Timestamp, float64(pkt.Timestamp)/48000.0)
		}

		cloned := cloneRTPPacket(pkt)
		if cloned == nil {
			continue
		}

		select {
		case s.audioQueue <- cloned:
		default:
			if count%200 == 0 {
				log.Printf("[AUDIO] queue full, dropping packet ts=%d", cloned.Timestamp)
			}
		}
	}
}

func (s *Sidecar) processVideoRTP() {
	var lastTS uint32
	haveTS := false
	dropCount := 0

	for pkt := range s.videoQueue {
		if !haveTS || pkt.Timestamp != lastTS {
			now := time.Now()
			extraDelay := s.computeTrackDelay("video", pkt.Timestamp, now)
			if extraDelay > 0 {
				time.Sleep(extraDelay)
			}
			lastTS = pkt.Timestamp
			haveTS = true
		}

		s.peersLock.RLock()
		peers := make([]*Peer, 0, len(s.peers))
		for _, peer := range s.peers {
			peers = append(peers, peer)
		}
		s.peersLock.RUnlock()

		// Hand off to each peer's own outbound queue instead of writing (and
		// waiting on) all peers synchronously here -- see the comment on
		// Peer.videoOut/audioOut for why. Only the gate check (fast,
		// in-memory) stays inline.
		for _, peer := range peers {
			peer.mu.Lock()
			active := peer.Active
			started := peer.Started

			if active && !started && isVP8KeyframeStart(pkt.Payload) {
				peer.Started = true
				started = true
				log.Printf("[Peer %s] First VP8 keyframe seen at ts=%d - opening stream gate", peer.ID, pkt.Timestamp)
			}

			peer.mu.Unlock()

			if active && started {
				select {
				case peer.videoOut <- pkt:
				default:
					dropCount++
					if dropCount%120 == 1 {
						log.Printf("[VIDEO] peer %s outbound queue full, dropping packet ts=%d", peer.ID, pkt.Timestamp)
					}
				}
			}
		}
	}
}

func (s *Sidecar) processAudioRTP() {
	var lastTS uint32
	haveTS := false
	dropCount := 0

	for pkt := range s.audioQueue {
		if !haveTS || pkt.Timestamp != lastTS {
			now := time.Now()
			extraDelay := s.computeTrackDelay("audio", pkt.Timestamp, now)
			if extraDelay > 0 {
				time.Sleep(extraDelay)
			}
			lastTS = pkt.Timestamp
			haveTS = true
		}

		s.peersLock.RLock()
		peers := make([]*Peer, 0, len(s.peers))
		for _, peer := range s.peers {
			peers = append(peers, peer)
		}
		s.peersLock.RUnlock()

		for _, peer := range peers {
			peer.mu.Lock()
			active := peer.Active
			started := peer.Started
			peer.mu.Unlock()

			if active && started {
				select {
				case peer.audioOut <- pkt:
				default:
					dropCount++
					if dropCount%200 == 1 {
						log.Printf("[AUDIO] peer %s outbound queue full, dropping packet ts=%d", peer.ID, pkt.Timestamp)
					}
				}
			}
		}
	}
}

func (s *Sidecar) CreatePeer(id string) (sdp string, err error) {
	s.peersLock.Lock()

	// If a create for this ID is already in progress, wait for it FIRST.
	if inflight, exists := s.creating[id]; exists {
		s.peersLock.Unlock()
		debugf("[API] Waiting for in-flight peer creation: %s", id)
		<-inflight.done
		return inflight.sdp, inflight.err
	}

	// Reuse existing peer/offer only when no create is currently in flight.
	if existing, exists := s.peers[id]; exists {
		state := existing.PC.ICEConnectionState()
		if state != webrtc.ICEConnectionStateClosed &&
			state != webrtc.ICEConnectionStateFailed &&
			state != webrtc.ICEConnectionStateDisconnected {
			if ld := existing.PC.LocalDescription(); ld != nil {
				s.peersLock.Unlock()
				debugf("[API] Reusing existing peer offer: %s", id)
				return ld.SDP, nil
			}
		}
	}

	inflight := &createInFlight{done: make(chan struct{})}
	s.creating[id] = inflight
	s.peersLock.Unlock()

	log.Printf("[API] Creating NEW peer: %s", id)

	defer func() {
		s.peersLock.Lock()
		inflight.sdp = sdp
		inflight.err = err
		delete(s.creating, id)
		close(inflight.done)
		s.peersLock.Unlock()
	}()

	iceServers := []webrtc.ICEServer{}
    
	for _, stun := range getStunServers() {
		iceServers = append(iceServers, webrtc.ICEServer{URLs: []string{stun}})
	}

	m := &webrtc.MediaEngine{}
	if err := m.RegisterCodec(webrtc.RTPCodecParameters{
		RTPCodecCapability: webrtc.RTPCodecCapability{
			MimeType:    webrtc.MimeTypeVP8,
			ClockRate:   90000,
			SDPFmtpLine: "",
		},
		PayloadType: 96,
	}, webrtc.RTPCodecTypeVideo); err != nil {
		return "", err
	}
	if err := m.RegisterCodec(webrtc.RTPCodecParameters{
		RTPCodecCapability: webrtc.RTPCodecCapability{
			MimeType:  webrtc.MimeTypeOpus,
			ClockRate: 48000,
			Channels:  2,
		},
		PayloadType: 111,
	}, webrtc.RTPCodecTypeAudio); err != nil {
		return "", err
	}

	i := &interceptor.Registry{}
	intervalPliFactory, err := intervalpli.NewReceiverInterceptor()
	if err != nil {
		return "", err
	}
	i.Add(intervalPliFactory)
	if err := webrtc.RegisterDefaultInterceptors(m, i); err != nil {
		return "", err
	}

	// Pin ICE candidate gathering to a fixed UDP range so it can actually be
	// firewalled -- the server's firewall was rebuilt at some point after
	// video streaming last worked and only allows explicitly listed ports;
	// pion's default random ephemeral ports can't be opened one by one.
	se := webrtc.SettingEngine{}
	portMin := uint16(envIntOrDefault("ICE_UDP_PORT_MIN", 50000))
	portMax := uint16(envIntOrDefault("ICE_UDP_PORT_MAX", 50100))
	if err := se.SetEphemeralUDPPortRange(portMin, portMax); err != nil {
		return "", fmt.Errorf("set ICE UDP port range: %w", err)
	}
	if debugLogsEnabled() {
		lf := logging.NewDefaultLoggerFactory()
		lf.DefaultLogLevel = logging.LogLevelTrace
		se.LoggerFactory = lf
	}

	api := webrtc.NewAPI(webrtc.WithMediaEngine(m), webrtc.WithInterceptorRegistry(i), webrtc.WithSettingEngine(se))

	pc, err := api.NewPeerConnection(webrtc.Configuration{
		ICEServers: iceServers,
	})
	if err != nil {
		return "", fmt.Errorf("create PeerConnection: %w", err)
	}

	videoTrack, err := webrtc.NewTrackLocalStaticRTP(
		webrtc.RTPCodecCapability{MimeType: webrtc.MimeTypeVP8, ClockRate: 90000},
		"video", "ts6-stream",
	)
	if err != nil {
		pc.Close()
		return "", err
	}

	audioTrack, err := webrtc.NewTrackLocalStaticRTP(
		webrtc.RTPCodecCapability{MimeType: webrtc.MimeTypeOpus, ClockRate: 48000, Channels: 2},
		"audio", "ts6-stream",
	)
	if err != nil {
		pc.Close()
		return "", err
	}

	videoSender, err := pc.AddTrack(videoTrack)
	if err != nil {
		pc.Close()
		return "", err
	}
	audioSender, err := pc.AddTrack(audioTrack)
	if err != nil {
		pc.Close()
		return "", err
	}

	peer := &Peer{
		ID:         id,
		PC:         pc,
		VideoTrack: videoTrack,
		AudioTrack: audioTrack,
		Active:     false,
		stopSR:     make(chan struct{}),
		videoOut:   make(chan *rtp.Packet, envIntOrDefault("PEER_VIDEO_QUEUE_SIZE", 256)),
		audioOut:   make(chan *rtp.Packet, envIntOrDefault("PEER_AUDIO_QUEUE_SIZE", 512)),
	}

	go readSenderRTCP(peer, videoSender, "video")
	go readSenderRTCP(peer, audioSender, "audio")
	go peerWriteLoop(peer.videoOut, videoTrack, peer.stopSR)
	go peerWriteLoop(peer.audioOut, audioTrack, peer.stopSR)

	pc.OnICEConnectionStateChange(func(state webrtc.ICEConnectionState) {
		log.Printf("[Peer %s] ICE: %s", id, state.String())
		switch state {
		case webrtc.ICEConnectionStateConnected:
			peer.mu.Lock()
			peer.Active = true
			peer.Started = false
			peer.mu.Unlock()
			// Resolve SSRCs NOW — they are only valid after negotiation
			for _, sender := range pc.GetSenders() {
				params := sender.GetParameters()
				if len(params.Encodings) > 0 {
					ssrc := uint32(params.Encodings[0].SSRC)
					if sender.Track() == videoTrack {
						peer.VideoSSRC = ssrc
						log.Printf("[Peer %s] Video SSRC resolved: %d", id, ssrc)
					} else if sender.Track() == audioTrack {
						peer.AudioSSRC = ssrc
						log.Printf("[Peer %s] Audio SSRC resolved: %d", id, ssrc)
					}
				}
			}
		case webrtc.ICEConnectionStateDisconnected, webrtc.ICEConnectionStateFailed, webrtc.ICEConnectionStateClosed:
			peer.mu.Lock()
			peer.Active = false
			peer.Started = false
			peer.mu.Unlock()
		}
	})

	offer, err := pc.CreateOffer(nil)
	if err != nil {
		return "", fmt.Errorf("create offer: %w", err)
	}
	if err := pc.SetLocalDescription(offer); err != nil {
		return "", fmt.Errorf("set local desc: %w", err)
	}

	gatherComplete := webrtc.GatheringCompletePromise(pc)
	<-gatherComplete

	s.peersLock.Lock()
	if old, exists := s.peers[id]; exists {
		old.Active = false
		close(old.stopSR)
		old.PC.Close()
	}
	s.peers[id] = peer
	s.peersLock.Unlock()

	sdp = pc.LocalDescription().SDP
	return sdp, nil
}

// sendSenderReports periodically sends RTCP Sender Reports with synchronized
// NTP timestamps for both audio and video, enabling the browser to correlate
// the two RTP clocks and maintain lip-sync.
func (s *Sidecar) sendSenderReports(peer *Peer) {
	ticker := time.NewTicker(1 * time.Second)
	defer ticker.Stop()

	cname := "ts6-stream"
	srCount := 0

	for {
		select {
		case <-peer.stopSR:
			return
		case <-ticker.C:
			if !peer.Active {
				continue
			}

			now := time.Now()
			ntpNow := toNTPTime(now)

			videoTs := uint32(atomic.LoadUint64(&s.lastVideoRTPTs))
			audioTs := uint32(atomic.LoadUint64(&s.lastAudioRTPTs))
			vidPkts := uint32(atomic.LoadUint64(&s.videoPktCount))
			vidOctets := uint32(atomic.LoadUint64(&s.videOctetCount))
			audPkts := uint32(atomic.LoadUint64(&s.audioPktCount))
			audOctets := uint32(atomic.LoadUint64(&s.audioOctetCount))

			if videoTs == 0 && audioTs == 0 {
				continue
			}

			srCount++

			// Send video SR + SDES
			if peer.VideoSSRC != 0 {
				err := peer.PC.WriteRTCP([]rtcp.Packet{
					&rtcp.SenderReport{
						SSRC:        peer.VideoSSRC,
						NTPTime:     ntpNow,
						RTPTime:     videoTs,
						PacketCount: vidPkts,
						OctetCount:  vidOctets,
					},
					&rtcp.SourceDescription{
						Chunks: []rtcp.SourceDescriptionChunk{{
							Source: peer.VideoSSRC,
							Items: []rtcp.SourceDescriptionItem{{
								Type: rtcp.SDESCNAME,
								Text: cname,
							}},
						}},
					},
				})
				if srCount <= 5 || srCount%30 == 0 {
					log.Printf("[SR] Peer %s video SR #%d ssrc=%d rtpTs=%d err=%v", peer.ID, srCount, peer.VideoSSRC, videoTs, err)
				}
			} else if srCount <= 5 {
				log.Printf("[SR] Peer %s video SSRC still 0 — skipping SR", peer.ID)
			}

			// Send audio SR + SDES with SAME NTP time and SAME CNAME
			if peer.AudioSSRC != 0 {
				err := peer.PC.WriteRTCP([]rtcp.Packet{
					&rtcp.SenderReport{
						SSRC:        peer.AudioSSRC,
						NTPTime:     ntpNow,
						RTPTime:     audioTs,
						PacketCount: audPkts,
						OctetCount:  audOctets,
					},
					&rtcp.SourceDescription{
						Chunks: []rtcp.SourceDescriptionChunk{{
							Source: peer.AudioSSRC,
							Items: []rtcp.SourceDescriptionItem{{
								Type: rtcp.SDESCNAME,
								Text: cname,
							}},
						}},
					},
				})
				if srCount <= 5 || srCount%30 == 0 {
					log.Printf("[SR] Peer %s audio SR #%d ssrc=%d rtpTs=%d err=%v", peer.ID, srCount, peer.AudioSSRC, audioTs, err)
				}
			} else if srCount <= 5 {
				log.Printf("[SR] Peer %s audio SSRC still 0 — skipping SR", peer.ID)
			}
		}
	}
}

func (s *Sidecar) SetAnswer(id, sdp string) error {
	s.peersLock.RLock()
	peer, exists := s.peers[id]
	s.peersLock.RUnlock()
	if !exists {
		return fmt.Errorf("peer %s not found", id)
	}

	peer.mu.Lock()
	defer peer.mu.Unlock()

	if peer.PC.RemoteDescription() != nil {
		if peer.PC.RemoteDescription().Type == webrtc.SDPTypeAnswer &&
			peer.PC.SignalingState() == webrtc.SignalingStateStable {
			debugf("[API] Ignoring duplicate answer for peer: %s", id)
			return nil
		}
	}

	if peer.PC.SignalingState() != webrtc.SignalingStateHaveLocalOffer {
		debugf("[API] Ignoring answer in signaling state %s for peer: %s", peer.PC.SignalingState(), id)
		return nil
	}

	if err := peer.PC.SetRemoteDescription(webrtc.SessionDescription{
		Type: webrtc.SDPTypeAnswer,
		SDP:  sdp,
	}); err != nil {
		return err
	}

	pending := peer.pendingCandidates
	peer.pendingCandidates = nil
	for _, c := range pending {
		if err := peer.PC.AddICECandidate(c); err != nil {
			log.Printf("[Peer %s] Failed to apply buffered ICE candidate: %v", id, err)
		}
	}
	return nil
}

func (s *Sidecar) AddICECandidate(id string, candidate string, sdpMid string, sdpMLineIndex uint16) error {
	s.peersLock.RLock()
	peer, exists := s.peers[id]
	s.peersLock.RUnlock()
	if !exists {
		return fmt.Errorf("peer %s not found", id)
	}

	init := webrtc.ICECandidateInit{
		Candidate:     candidate,
		SDPMid:        &sdpMid,
		SDPMLineIndex: &sdpMLineIndex,
	}

	peer.mu.Lock()
	if peer.PC.RemoteDescription() == nil {
		peer.pendingCandidates = append(peer.pendingCandidates, init)
		peer.mu.Unlock()
		return nil
	}
	peer.mu.Unlock()

	return peer.PC.AddICECandidate(init)
}

func (s *Sidecar) ClosePeer(id string) {
	s.peersLock.Lock()
	if peer, exists := s.peers[id]; exists {
		peer.Active = false
		close(peer.stopSR)
		peer.PC.Close()
		delete(s.peers, id)
	}
	s.peersLock.Unlock()
}

// Linux's default pipe buffer is 64KB. Direct measurement (both from this
// container's own network path and from an unrelated residential
// connection) showed some YouTube CDN edge servers deliver certain DASH
// formats in ~16KB bursts every ~450-550ms rather than smoothly -- a
// server-side throttling behavior on Google's end, not a local issue.
// 64KB drains in well under one burst interval, so ffmpeg's real-time-paced
// reads stall right along with the CDN's gaps no matter how large
// thread_queue_size is set (that only buffers packets ffmpeg has already
// read from the pipe/socket, not bytes the OS hasn't received yet).
//
// minPrefetchPipeSize is the floor even when a caller asks for a smaller
// buffer (e.g. an unparsed/zero bitrate) -- StartFFmpeg sizes the real
// buffer to hold STREAM_STARTUP_BUFFER_SECONDS of the configured bitrate.
const minPrefetchPipeSize = 1 << 20

type prefetchStream struct {
	path   string
	cancel context.CancelFunc
	done   chan struct{}
}

// startPrefetch fetches sourceURL into a named pipe using our own
// unthrottled Go HTTP client, decoupling ffmpeg's real-time-paced reads
// from the network entirely: ffmpeg reads the pipe with -re exactly as it
// would a local file, and the CDN's periodic delivery gaps just eat into
// the pipe's buffer instead of stalling the encoder. pipeSize is clamped up
// to minPrefetchPipeSize.
func startPrefetch(sourceURL string, pipeSize int) (*prefetchStream, error) {
	if pipeSize < minPrefetchPipeSize {
		pipeSize = minPrefetchPipeSize
	}

	fifoPath := filepath.Join(os.TempDir(), fmt.Sprintf("sidecar-prefetch-%d-%d.fifo", os.Getpid(), time.Now().UnixNano()))
	if err := mkfifo(fifoPath); err != nil {
		return nil, fmt.Errorf("mkfifo: %w", err)
	}

	ctx, cancel := context.WithCancel(context.Background())
	done := make(chan struct{})

	go func() {
		defer close(done)
		defer os.Remove(fifoPath)

		// Opened O_RDWR rather than O_WRONLY: on Linux (see fifo(7)) that is
		// the one open mode on a FIFO that never blocks waiting for a peer,
		// which is exactly what we need here -- an O_WRONLY open blocks
		// until ffmpeg opens its end for reading, meaning fetching couldn't
		// even start until ffmpeg was already running, so this pipe could
		// only ever smooth momentary jitter, never build a genuine
		// head-start buffer before playback begins. With O_RDWR we can
		// start pulling from the CDN and filling the (now much larger,
		// bitrate-and-STREAM_STARTUP_BUFFER_SECONDS-sized) pipe buffer
		// immediately, while StartFFmpeg deliberately delays launching
		// ffmpeg -- so by the time ffmpeg opens the read end and starts
		// consuming, several seconds of data are already sitting there
		// ready, enough to ride out the sustained ~450ms-granularity
		// delivery pacing a real deployment showed on some CDN edges.
		w, err := os.OpenFile(fifoPath, os.O_RDWR, 0)
		if err != nil {
			if ctx.Err() == nil {
				log.Printf("[Prefetch] Failed to open fifo: %v", err)
			}
			return
		}
		defer w.Close()

		growPipeBuffer(w, pipeSize)

		fetchWithResume(ctx, sourceURL, w)
	}()

	return &prefetchStream{path: fifoPath, cancel: cancel, done: done}, nil
}

// fetchWithResume streams sourceURL into w, resuming with a byte-range
// request if the connection drops partway through. This replaces the
// resilience ffmpeg's own -reconnect flags provided back when it read the
// network directly, now that it only ever sees the local pipe.
func fetchWithResume(ctx context.Context, sourceURL string, w io.Writer) {
	var written int64
	for attempt := 0; attempt < 5; attempt++ {
		req, err := http.NewRequestWithContext(ctx, http.MethodGet, sourceURL, nil)
		if err != nil {
			log.Printf("[Prefetch] Request build failed: %v", err)
			return
		}
		if written > 0 {
			req.Header.Set("Range", fmt.Sprintf("bytes=%d-", written))
		}

		resp, err := http.DefaultClient.Do(req)
		if err != nil {
			if ctx.Err() != nil {
				return
			}
			log.Printf("[Prefetch] Fetch attempt %d failed: %v", attempt+1, err)
			time.Sleep(time.Second)
			continue
		}

		n, copyErr := io.Copy(w, resp.Body)
		resp.Body.Close()
		written += n

		if copyErr == nil {
			return // EOF reached cleanly -- whole source delivered
		}
		if ctx.Err() != nil {
			return // asked to stop, not a real failure
		}
		log.Printf("[Prefetch] Copy interrupted after %d bytes (attempt %d): %v", written, attempt+1, copyErr)
		time.Sleep(time.Second)
	}
	log.Printf("[Prefetch] Giving up after repeated failures, %d bytes delivered", written)
}

func (p *prefetchStream) Stop() {
	p.cancel()
	<-p.done
}

func (s *Sidecar) StartFFmpeg(source string, width int, height int, framerate int, bitrate string, audioSource string) {
	s.ffmpegLock.Lock()
	defer s.ffmpegLock.Unlock()

	s.StopFFmpegLocked()
	s.resetSyncTiming()
	s.drainRTPQueues()
	s.resetPeerStreamState()

	s.source = source

	w := width
	h := height
	fps := framerate

	if w <= 0 {
		w = envIntOrDefault("VIDEO_WIDTH", 1280)
	}

	if h <= 0 {
		h = envIntOrDefault("VIDEO_HEIGHT", 720)
	}

	if fps <= 0 {
		fps = envIntOrDefault("VIDEO_FRAMERATE", 30)
	}

	args := []string{}

	// ffmpeg's demuxer read-ahead queue defaults to just 8 packets per
	// input, which is fine for a local file but far too little for a
	// network source: a brief stall fetching the next chunk over HTTP
	// drains it immediately, and the encoder has nothing to output on
	// schedule. That shows up downstream as WebRTC audio/video
	// concealment and interruptions even though no packets are actually
	// lost -- they just weren't queued up far enough ahead to absorb the
	// stall. Bumping it gives ffmpeg's network reader thread real slack.
	threadQueueSize := strconv.Itoa(envIntOrDefault("THREAD_QUEUE_SIZE", 4096))

	videoInput := source
	audioInput := audioSource

	vBitrate := strings.TrimSpace(bitrate)
	if vBitrate == "" {
		vBitrate = envOrDefault("VIDEO_BITRATE", "1500k")
	}
	aBitrateStr := envOrDefault("AUDIO_BITRATE", "128k")
	audioDelayMs := envIntOrDefault("AUDIO_DELAY_MS", 0)

	// How long a real deployment needs to ride out a CDN edge that paces
	// delivery close to real-time (observed as a sustained, growing
	// ffmpeg-audio-read gap that plateaued around ~450-460ms per read,
	// constant for the whole stream, independent of bitrate or whether the
	// video/audio tracks were fetched separately or combined). Buffering
	// this many seconds of the actual bitrate ahead of ffmpeg -- and
	// starting ffmpeg only once buffered -- absorbs that instead of
	// starving the encoder in real time. Costs viewers this much stream
	// start-up latency.
	startupBufferSeconds := envIntOrDefault("STREAM_STARTUP_BUFFER_SECONDS", 4)
	bufferBitrateBps := parseBitrateBps(vBitrate) + parseBitrateBps(aBitrateStr)
	prefetchPipeSize := minPrefetchPipeSize
	if bufferBitrateBps > 0 {
		if sized := (bufferBitrateBps / 8) * startupBufferSeconds; sized > prefetchPipeSize {
			prefetchPipeSize = sized
		}
	}

	prefetchStarted := false

	if source != "" {
		if strings.HasPrefix(source, "http://") || strings.HasPrefix(source, "https://") {
			if pf, err := startPrefetch(source, prefetchPipeSize); err != nil {
				log.Printf("[FFmpeg] Video prefetch setup failed, reading network directly: %v", err)
				args = append(args, "-reconnect", "1", "-reconnect_streamed", "1", "-reconnect_delay_max", "5")
			} else {
				s.prefetches = append(s.prefetches, pf)
				videoInput = pf.path
				prefetchStarted = true
			}
		} else {
			args = append(args, "-stream_loop", "-1")
		}

		args = append(args, "-thread_queue_size", threadQueueSize, "-fflags", "+genpts+discardcorrupt", "-re", "-i", videoInput)

		// Video-only and audio-only DASH streams resolved separately (e.g.
		// YouTube only serves combined formats up to ~360p; better quality
		// needs muxing two URLs), fed to ffmpeg as a second input rather
		// than upscaling the low-res combined format.
		if audioSource != "" {
			if strings.HasPrefix(audioSource, "http://") || strings.HasPrefix(audioSource, "https://") {
				if pf, err := startPrefetch(audioSource, prefetchPipeSize); err != nil {
					log.Printf("[FFmpeg] Audio prefetch setup failed, reading network directly: %v", err)
					args = append(args, "-reconnect", "1", "-reconnect_streamed", "1", "-reconnect_delay_max", "5")
				} else {
					s.prefetches = append(s.prefetches, pf)
					audioInput = pf.path
					prefetchStarted = true
				}
			}
			args = append(args, "-thread_queue_size", threadQueueSize, "-fflags", "+genpts+discardcorrupt", "-re", "-i", audioInput)
		}
	} else {
		args = append(args, "-re", "-f", "lavfi", "-i", fmt.Sprintf("color=c=black:s=%dx%d:r=1", w, h))
	}

	audioMapInput := "0"
	if audioSource != "" {
		audioMapInput = "1"
	}

	if prefetchStarted && startupBufferSeconds > 0 {
		log.Printf("[FFmpeg] Buffering %ds before starting playback (pipe size %d bytes)", startupBufferSeconds, prefetchPipeSize)
		time.Sleep(time.Duration(startupBufferSeconds) * time.Second)
	}

	if source != "" {
		// Cap the scale target at the source's own resolution (min(iw,w) x
		// min(ih,h)) instead of always scaling up to the preset -- a source
		// that's actually 640x360 encoded at a "1080p"/1280x720 preset was
		// burning CPU upscaling and encoding pixels with no real detail in
		// them, which is exactly the kind of load that tips libvpx's
		// (largely single-threaded) realtime encoder over budget once a
		// second viewer adds a bit more work on top.
		vf := fmt.Sprintf(
			"fps=%d,scale='min(iw,%d)':'min(ih,%d)':force_original_aspect_ratio=decrease,pad=%d:%d:(ow-iw)/2:(oh-ih)/2,format=yuv420p",
			fps, w, h, w, h,
		)
		args = append(args,
			"-map", "0:v:0",
			"-vf", vf,
		)
	}
	// libvpx's realtime VP8 encoder only parallelizes across CPU cores when
	// given multiple token partitions (-slices) to match -threads; without
	// both set it runs single-threaded regardless of cpu-used, which caps
	// throughput well below what a real 1080p60fps source needs. Slices
	// must be a power of two (1/2/4/8) -- see VIDEO_ENCODE_THREADS.
	encodeThreads := clampToPowerOfTwo(envIntOrDefault("VIDEO_ENCODE_THREADS", 4), 1, 8)
	args = append(args,
		"-pix_fmt", "yuv420p",
		"-c:v", "libvpx",
		"-cpu-used", "8",
		"-deadline", "realtime",
		"-slices", strconv.Itoa(encodeThreads),
		"-threads", strconv.Itoa(encodeThreads),
		"-lag-in-frames", "0",
		"-error-resilient", "1",
		"-b:v", vBitrate,
		"-maxrate", vBitrate,
		"-bufsize", envOrDefault("VIDEO_BUFSIZE", "500k"),
		"-keyint_min", "15",
		"-g", "15",
		"-auto-alt-ref", "0",
		"-payload_type", "96",
		"-ssrc", "11111111",
		"-f", "rtp",
		fmt.Sprintf("rtp://127.0.0.1:%d", s.videoPort),
	)

	if source != "" {
		args = append(args,
			"-map", fmt.Sprintf("%s:a:0?", audioMapInput),
		)

		if audioDelayMs > 0 {
			args = append(args,
				"-af", fmt.Sprintf("adelay=delays=%d:all=1", audioDelayMs),
			)
		}

		args = append(args,
			"-c:a", "libopus",
			"-b:a", aBitrateStr,
			"-ar", "48000",
			"-ac", "2",
			"-payload_type", "111",
			"-ssrc", "22222222",
			"-f", "rtp",
			fmt.Sprintf("rtp://127.0.0.1:%d", s.audioPort),
		)
	}


	log.Printf("[FFmpeg] Starting: source=%s video=:%d audio=:%d", source, s.videoPort, s.audioPort)

	cmd := exec.Command(getFfmpegPath(), args...)
	cmd.Stdout = nil
	cmd.Stderr = os.Stderr
	if err := cmd.Start(); err != nil {
		log.Printf("[FFmpeg] Start error: %v", err)
		return
	}
	s.ffmpeg = cmd

	go func() {
		err := cmd.Wait()
		log.Printf("[FFmpeg] Exited: %v", err)
	}()
}

func (s *Sidecar) StopFFmpegLocked() {
	if s.ffmpeg != nil && s.ffmpeg.Process != nil {
		s.ffmpeg.Process.Kill()
		s.ffmpeg = nil
	}
	// Kill ffmpeg before stopping the prefetchers: closing its fd on the
	// pipe is what unblocks a prefetcher goroutine that's mid-write (a
	// cancelled context alone doesn't interrupt a blocking pipe write).
	for _, pf := range s.prefetches {
		pf.Stop()
	}
	s.prefetches = nil
}

func (s *Sidecar) GetStats() map[string]interface{} {
	s.peersLock.RLock()
	defer s.peersLock.RUnlock()

	peers := map[string]interface{}{}
	for id, peer := range s.peers {
		// Real packet loss/jitter as reported back by this peer over RTCP
		// Receiver Reports (collected by readSenderRTCP) -- this is the
		// actual network path to that peer (e.g. a TS6 client's connection),
		// which none of the ffmpeg-side RTP-read diagnostics can see.
		peer.mu.Lock()
		remote := map[string]interface{}{
			"video": map[string]interface{}{
				"packetsLost": peer.videoPacketsLost,
				"jitter":      peer.videoJitter,
			},
			"audio": map[string]interface{}{
				"packetsLost": peer.audioPacketsLost,
				"jitter":      peer.audioJitter,
			},
		}
		peer.mu.Unlock()

		peers[id] = map[string]interface{}{
			"active":           peer.Active,
			"state":            peer.PC.ICEConnectionState().String(),
			"remoteInboundRTP": remote,
		}
	}

	return map[string]interface{}{
		"videoPort": s.videoPort,
		"audioPort": s.audioPort,
		"peerCount": len(s.peers),
		"peers":     peers,
		"source":    s.source,
	}
}

func (s *Sidecar) Stop() {
	s.running = false
	s.ffmpegLock.Lock()
	s.StopFFmpegLocked()
	s.ffmpegLock.Unlock()

	if s.videoConn != nil {
		s.videoConn.Close()
	}
	if s.audioConn != nil {
		s.audioConn.Close()
	}

	s.peersLock.Lock()
	for id, peer := range s.peers {
		peer.Active = false
		peer.PC.Close()
		delete(s.peers, id)
	}
	s.peersLock.Unlock()
}

func main() {
	port := 9800
	if p := os.Getenv("SIDECAR_PORT"); p != "" {
		if v, err := strconv.Atoi(p); err == nil {
			port = v
		}
	}

	sidecar := NewSidecar()
	if err := sidecar.StartRTP(); err != nil {
		log.Fatalf("Failed to start RTP: %v", err)
	}

	mux := http.NewServeMux()

	mux.HandleFunc("POST /peer/create", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			ID string `json:"id"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, err.Error(), 400)
			return
		}
		debugf("[API] Peer create requested: %s", req.ID)

		sdp, err := sidecar.CreatePeer(req.ID)
		if err != nil {
			log.Printf("[API] CreatePeer error: %v", err)
			http.Error(w, err.Error(), 500)
			return
		}

		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]string{"sdp": sdp})
	})

	mux.HandleFunc("POST /peer/answer", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			ID  string `json:"id"`
			SDP string `json:"sdp"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, err.Error(), 400)
			return
		}
		debugf("[API] Setting answer for peer: %s (%d bytes)", req.ID, len(req.SDP))

		if err := sidecar.SetAnswer(req.ID, req.SDP); err != nil {
			log.Printf("[API] SetAnswer error: %v", err)
			http.Error(w, err.Error(), 500)
			return
		}
		json.NewEncoder(w).Encode(map[string]string{"status": "ok"})
	})

	mux.HandleFunc("POST /peer/ice", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			ID            string `json:"id"`
			Candidate     string `json:"candidate"`
			SDPMid        string `json:"sdpMid"`
			SDPMLineIndex uint16 `json:"sdpMLineIndex"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, err.Error(), 400)
			return
		}

		if err := sidecar.AddICECandidate(req.ID, req.Candidate, req.SDPMid, req.SDPMLineIndex); err != nil {
			log.Printf("[API] AddICE error: %v", err)
			http.Error(w, err.Error(), 500)
			return
		}
		json.NewEncoder(w).Encode(map[string]string{"status": "ok"})
	})

	mux.HandleFunc("POST /peer/close", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			ID string `json:"id"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, err.Error(), 400)
			return
		}
		sidecar.ClosePeer(req.ID)
		json.NewEncoder(w).Encode(map[string]string{"status": "ok"})
	})

	mux.HandleFunc("POST /source", func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			Source      string `json:"source"`
			Width       int    `json:"width"`
			Height      int    `json:"height"`
			Framerate   int    `json:"framerate"`
			Bitrate     string `json:"bitrate"`
			AudioSource string `json:"audioSource"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			http.Error(w, err.Error(), 400)
			return
		}
		log.Printf("[API] Setting source: %s (%dx%d @ %dfps, %s)", req.Source, req.Width, req.Height, req.Framerate, req.Bitrate)
		sidecar.StartFFmpeg(req.Source, req.Width, req.Height, req.Framerate, req.Bitrate, req.AudioSource)
		json.NewEncoder(w).Encode(map[string]string{"status": "ok"})
	})

	mux.HandleFunc("POST /source/stop", func(w http.ResponseWriter, r *http.Request) {
		sidecar.ffmpegLock.Lock()
		sidecar.StopFFmpegLocked()
		sidecar.resetSyncTiming()
		sidecar.drainRTPQueues()
		sidecar.resetPeerStreamState()
		sidecar.ffmpegLock.Unlock()

		json.NewEncoder(w).Encode(map[string]string{"status": "ok"})
	})

	mux.HandleFunc("GET /stats", func(w http.ResponseWriter, r *http.Request) {
		json.NewEncoder(w).Encode(sidecar.GetStats())
	})

	mux.HandleFunc("GET /health", func(w http.ResponseWriter, r *http.Request) {
		json.NewEncoder(w).Encode(map[string]interface{}{
			"status":    "ok",
			"videoPort": sidecar.videoPort,
			"audioPort": sidecar.audioPort,
		})
	})

	go func() {
		sigCh := make(chan os.Signal, 1)
		signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
		<-sigCh
		log.Println("Shutting down...")
		sidecar.Stop()
		os.Exit(0)
	}()

	log.Printf("[Sidecar] HTTP API listening on :%d", port)
	if err := http.ListenAndServe(fmt.Sprintf(":%d", port), mux); err != nil {
		log.Fatalf("HTTP server error: %v", err)
	}
}
