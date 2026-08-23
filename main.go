package main

import (
	"bytes"
	"context"
	"crypto/tls"
	"crypto/x509"
	"encoding/binary"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"log"
	"math"
	"math/rand"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"regexp"
	"sort"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/oschwald/geoip2-golang"
	utls "github.com/refraction-networking/utls"
	"golang.org/x/net/http2/hpack"
	"golang.org/x/net/publicsuffix"
	"golang.org/x/sync/errgroup"
	"golang.org/x/sync/singleflight"
)

// ================= CONFIG & CONSTANTS =================

type Mode string

const (
	ModeDirect Mode = "direct"
	ModeAuto   Mode = "autonomous"

	FrameData         = 0x00
	FrameHeaders      = 0x01
	FrameRSTStream    = 0x03
	FrameSettings     = 0x04
	FrameGoAway       = 0x07
	FrameWindowUpdate = 0x08
	FrameContinuation = 0x09

	FlagEndStream  = 0x01
	FlagEndHeaders = 0x04
	FlagPadded     = 0x08
	FlagPriority   = 0x20
	FlagAck        = 0x01

	maxCTNamesPerRoot = 100
)

var (
	cdnStrong = []string{"cloudflare", "fastly", "akamai", "ddos-guard", "qrator", "sucuri"}
	cdnWeak   = []string{"x-cache", "x-served-by", "cf-ray", "x-edge"}
	junkTLDs  = []string{".xyz", ".top", ".site", ".fun", ".online", ".space", ".pw", ".cc", ".icu", ".click", ".win", ".bid", ".date"}
	dynDNS    = []string{"duckdns.org", "mooo.com", "ddns.net", "freeddns.org", "crabdance.com", "eu.org", "cloudns.cc", "hopto.org", "zapto.org", "sytes.net", "dyn.com", "no-ip.org"}

	domainRe = regexp.MustCompile(`^[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(\.[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+$`)
	numRe    = regexp.MustCompile(`(?i)(^|\.)\d+\.[a-z]{2,}$`)
)

type Config struct {
	Mode             Mode
	Workers          int
	MaxIPs           int
	TCPTimeoutMs     int
	TLSTimeoutMs     int
	H2ReadTimeoutMs  int
	H2WriteTimeoutMs int
	Seed             int64
	TargetASN        uint
	TargetCountry    string
	TargetIP         string
	DirectSNI        string
	ScanEntireASN    bool
	CIDRs            []string
	Domains          []string
	GeoIPPath        string
	ASNPath          string
}

// ================= MODELS =================

type Timings struct {
	TCP          time.Duration
	TLS          time.Duration
	H2FirstFrame time.Duration
	H2Headers    time.Duration
}

func (t Timings) TotalLatency() time.Duration {
	return t.TCP + t.TLS + t.H2Headers
}

type PeerSettingsProfile struct {
	HeaderTableSize      uint32
	EnablePush           uint32
	MaxConcurrentStreams uint32
	InitialWindowSize    uint32
	MaxFrameSize         uint32
	MaxHeaderListSize    uint32

	HasHeaderTableSize      bool
	HasEnablePush           bool
	HasMaxConcurrentStreams bool
	HasInitialWindowSize    bool
	HasMaxFrameSize         bool
	HasMaxHeaderListSize    bool
}

type RealityScore struct {
	TLSQuality     float64
	Certificate    float64
	H2Profile      float64
	ServerProfile  float64
	HTTPBehavior   float64
	DNSConsistency float64
	Latency        float64
	Total          float64
}

type Candidate struct {
	IP                string
	SNI               string
	ALPN              string
	H2HeadersReceived bool
	HTTPStatus        int
	Location          string
	BodyBytes         int
	Server            string
	ContentType       string
	Timings           Timings
	ASN               uint
	Country           string
	CDNStrong         bool
	CDNWeak           bool
	Score             float64
	DomainPenalty     float64
	RealityScore      RealityScore
	CertChainValid    bool
	EndStreamSeen     bool
	StreamReset       bool
	GoAwaySeen        bool
	DNSMatched        bool
	PTRDiscovered     bool
	SeedProvided      bool
	CTDiscovered      bool
	DomainQuality     string

	CertIssuer            string
	CertSubject           string
	CertSANCount          int
	H2SettingsReceived    bool
	H2SettingsAckSent     bool
	H2SettingsAckReceived bool
	InitialPeerSettings   PeerSettingsProfile
	LatestPeerSettings    PeerSettingsProfile
	H2DataFrames          int
}

type TargetPair struct {
	IP            string
	SNI           string
	PTRDiscovered bool
	SeedProvided  bool
	CTDiscovered  bool
}

// ================= TELEMETRY & CIRCUIT BREAKER =================

type PipelineStats struct {
	mu                    sync.Mutex
	IPSampled             int
	IPWithPTR             int
	CRTAttempts           int
	CRTSuccess            int
	CRTFailed             int
	CRTTimeouts           int
	CRTHTTP4xx            int
	CRTHTTP5xx            int
	CRTNetErr             int
	CRTDecodeErr          int
	CTFallbackAttempts    int
	CTFallbackSuccess     int
	CTFallbackFailed      int
	UniqueDiscoveredNames int
	DNSValidPairs         int
	TCPConnected          int
	TLSHandshakeOK        int
	TLSValidationErr      int
	H2HeadersOK           int
	EndStreamOK           int
	ASNFiltered           int
	CountryFiltered       int
	CDNDropped            int
}

var stats PipelineStats

type CRTCircuitBreaker struct {
	mu         sync.Mutex
	failures   int
	disabled   bool
	threshold  int
	disabledAt time.Time
	cooldown   time.Duration
}

func isCriticalCRTError(err error) bool {
	if err == nil {
		return false
	}
	if errors.Is(err, context.DeadlineExceeded) {
		return true
	}
	var netErr net.Error
	if errors.As(err, &netErr) && netErr.Timeout() {
		return true
	}
	msg := strings.ToLower(err.Error())
	return strings.Contains(msg, "connection refused") ||
		strings.Contains(msg, "no such host") ||
		strings.Contains(msg, "crt.sh http status 5xx")
}

func (cb *CRTCircuitBreaker) RecordFailure(err error) {
	if !isCriticalCRTError(err) {
		return
	}
	cb.mu.Lock()
	defer cb.mu.Unlock()

	cb.failures++
	if cb.failures >= cb.threshold && !cb.disabled {
		cb.disabled = true
		cb.disabledAt = time.Now()
		fmt.Printf("[!] CRTCircuitBreaker: crt.sh временно отключен на %v после %d сбоев.\n", cb.cooldown, cb.failures)
	}
}

func (cb *CRTCircuitBreaker) RecordSuccess() {
	cb.mu.Lock()
	defer cb.mu.Unlock()
	cb.failures = 0
	cb.disabled = false
	cb.disabledAt = time.Time{}
}

func (cb *CRTCircuitBreaker) IsDisabled() bool {
	cb.mu.Lock()
	defer cb.mu.Unlock()

	if cb.disabled {
		if time.Since(cb.disabledAt) > cb.cooldown {
			cb.disabled = false
			cb.failures = 0
			return false
		}
		return true
	}
	return false
}

var (
	crtBreaker     = &CRTCircuitBreaker{threshold: 5, cooldown: 5 * time.Minute}
	certSpotterSem = make(chan struct{}, 4)

	crtRateMu      sync.Mutex
	crtNextRequest time.Time
)

func waitCRT(ctx context.Context) error {
	for {
		crtRateMu.Lock()
		now := time.Now()
		if !now.Before(crtNextRequest) {
			crtNextRequest = now.Add(12 * time.Second)
			crtRateMu.Unlock()
			return nil
		}
		wait := time.Until(crtNextRequest)
		crtRateMu.Unlock()

		timer := time.NewTimer(wait)
		select {
		case <-ctx.Done():
			timer.Stop()
			return ctx.Err()
		case <-timer.C:
		}
	}
}

// ================= CACHES =================

type SafeCache struct {
	mu   sync.RWMutex
	data map[string][]string
}

func NewSafeCache() *SafeCache {
	return &SafeCache{data: make(map[string][]string)}
}

func (c *SafeCache) Get(key string) ([]string, bool) {
	c.mu.RLock()
	defer c.mu.RUnlock()
	v, ok := c.data[key]
	if !ok {
		return nil, false
	}
	return append([]string(nil), v...), true
}

func (c *SafeCache) Put(key string, vals []string) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.data[key] = append([]string(nil), vals...)
}

var (
	crtCache = NewSafeCache()
	crtGroup singleflight.Group
	crtSeen  sync.Map
	dnsCache = NewSafeCache()
	dnsGroup singleflight.Group
)

// ================= UTILS =================

func gcd(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

func CleanDomain(d string) string {
	d = strings.ToLower(strings.TrimSpace(d))
	d = strings.TrimPrefix(d, "*.")
	d = strings.TrimSuffix(d, ".")
	if d == "localhost" || strings.HasPrefix(d, "localhost.") {
		return ""
	}
	if !domainRe.MatchString(d) {
		return ""
	}
	return d
}

func GetRootDomain(domain string) string {
	root, err := publicsuffix.EffectiveTLDPlusOne(domain)
	if err != nil {
		return domain
	}
	return root
}

func uniqueDomains(domains []string) []string {
	seen := make(map[string]bool)
	var result []string
	for _, d := range domains {
		if !seen[d] {
			seen[d] = true
			result = append(result, d)
		}
	}
	return result
}

func classifyDomainQuality(sni string) string {
	sniLower := strings.ToLower(sni)
	for _, tld := range junkTLDs {
		if strings.HasSuffix(sniLower, tld) {
			return "JunkTLD"
		}
	}
	for _, dDNS := range dynDNS {
		if strings.HasSuffix(sniLower, dDNS) {
			return "DynDNS"
		}
	}
	if numRe.MatchString(sniLower) {
		return "Numeric"
	}
	return "Normal"
}

// ================= CT DISCOVERY =================

func gatherCrtSh(ctx context.Context, domain string, client *http.Client) ([]string, error) {
	urlStr := fmt.Sprintf("https://crt.sh/?q=%%25.%s&output=json", url.QueryEscape(domain))
	req, err := http.NewRequestWithContext(ctx, "GET", urlStr, nil)
	if err != nil {
		stats.mu.Lock()
		stats.CRTNetErr++
		stats.mu.Unlock()
		return nil, err
	}

	resp, err := client.Do(req)
	if err != nil {
		stats.mu.Lock()
		if errors.Is(err, context.DeadlineExceeded) {
			stats.CRTTimeouts++
		} else {
			stats.CRTNetErr++
		}
		stats.mu.Unlock()
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode >= 400 && resp.StatusCode < 500 {
		stats.mu.Lock()
		stats.CRTHTTP4xx++
		stats.mu.Unlock()
		return nil, fmt.Errorf("crt.sh HTTP status 4xx: %d", resp.StatusCode)
	}
	if resp.StatusCode >= 500 {
		stats.mu.Lock()
		stats.CRTHTTP5xx++
		stats.mu.Unlock()
		return nil, fmt.Errorf("crt.sh HTTP status 5xx: %d", resp.StatusCode)
	}
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("crt.sh HTTP status %d", resp.StatusCode)
	}

	var ctRes []struct {
		NameValue string `json:"name_value"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&ctRes); err != nil {
		stats.mu.Lock()
		stats.CRTDecodeErr++
		stats.mu.Unlock()
		return nil, err
	}

	seen := make(map[string]struct{})
	var subs []string
	for _, rec := range ctRes {
		for _, part := range strings.Split(rec.NameValue, "\n") {
			if d := CleanDomain(part); d != "" {
				if _, exists := seen[d]; !exists {
					seen[d] = struct{}{}
					subs = append(subs, d)
				}
			}
		}
	}
	return subs, nil
}

func gatherCertSpotter(ctx context.Context, domain string, client *http.Client) ([]string, error) {
	urlStr := fmt.Sprintf(
		"https://api.certspotter.com/v1/issuances?domain=%s&include_subdomains=true&expand=dns_names",
		url.QueryEscape(domain),
	)

	req, err := http.NewRequestWithContext(ctx, http.MethodGet, urlStr, nil)
	if err != nil {
		return nil, err
	}

	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("certspotter HTTP status %d", resp.StatusCode)
	}

	var issuances []struct {
		DNSNames []string `json:"dns_names"`
	}

	if err := json.NewDecoder(resp.Body).Decode(&issuances); err != nil {
		return nil, err
	}

	seen := make(map[string]struct{})
	var result []string

	for _, issuance := range issuances {
		for _, name := range issuance.DNSNames {
			name = strings.TrimSpace(name)
			if d := CleanDomain(name); d != "" {
				if _, exists := seen[d]; !exists {
					seen[d] = struct{}{}
					result = append(result, d)
				}
			}
		}
	}

	return result, nil
}

func gatherCertSpotterLimited(ctx context.Context, domain string, client *http.Client) ([]string, error) {
	select {
	case certSpotterSem <- struct{}{}:
		defer func() { <-certSpotterSem }()
	case <-ctx.Done():
		return nil, ctx.Err()
	}
	return gatherCertSpotter(ctx, domain, client)
}

func gatherCTDomains(ctx context.Context, domain string, client *http.Client) ([]string, error) {
	if !crtBreaker.IsDisabled() {
		if err := waitCRT(ctx); err != nil {
			if errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) {
				return nil, err
			}
		} else if !crtBreaker.IsDisabled() {
			requestCtx, cancel := context.WithTimeout(ctx, 6*time.Second)
			defer cancel()

			stats.mu.Lock()
			stats.CRTAttempts++
			stats.mu.Unlock()

			result, err := gatherCrtSh(requestCtx, domain, client)
			if err == nil {
				stats.mu.Lock()
				stats.CRTSuccess++
				stats.mu.Unlock()
				crtBreaker.RecordSuccess()
				if len(result) > maxCTNamesPerRoot {
					result = result[:maxCTNamesPerRoot]
				}
				return result, nil
			}

			stats.mu.Lock()
			stats.CRTFailed++
			stats.mu.Unlock()
			crtBreaker.RecordFailure(err)
		}
	}

	stats.mu.Lock()
	stats.CTFallbackAttempts++
	stats.mu.Unlock()

	spotCtx, cancel := context.WithTimeout(ctx, 5*time.Second)
	defer cancel()

	result, err := gatherCertSpotterLimited(spotCtx, domain, client)
	stats.mu.Lock()
	defer stats.mu.Unlock()

	if err != nil {
		stats.CTFallbackFailed++
		return nil, err
	}

	stats.CTFallbackSuccess++
	if len(result) > maxCTNamesPerRoot {
		result = result[:maxCTNamesPerRoot]
	}
	return result, nil
}

// ================= DB & IP HELPERS =================

func ensureDB(path, dbURL string) error {
	if fi, err := os.Stat(path); err == nil {
		if fi.Size() > 1024*1024 {
			if db, err := geoip2.Open(path); err == nil {
				db.Close()
				return nil
			}
		}
	}

	tempFile := path + ".tmp"
	out, err := os.Create(tempFile)
	if err != nil {
		return err
	}

	client := &http.Client{Timeout: 5 * time.Minute}
	resp, err := client.Get(dbURL)
	if err != nil {
		out.Close()
		os.Remove(tempFile)
		return err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		out.Close()
		os.Remove(tempFile)
		return fmt.Errorf("bad HTTP status: %d", resp.StatusCode)
	}

	if _, err = io.Copy(out, resp.Body); err != nil {
		out.Close()
		os.Remove(tempFile)
		return err
	}
	out.Close()

	testDB, err := geoip2.Open(tempFile)
	if err != nil {
		os.Remove(tempFile)
		return fmt.Errorf("invalid MaxMind database: %v", err)
	}
	testDB.Close()

	return os.Rename(tempFile, path)
}

func readPublicIPv4(resp *http.Response) (string, error) {
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("HTTP status %d", resp.StatusCode)
	}
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", err
	}
	ipStr := strings.TrimSpace(string(body))
	ip := net.ParseIP(ipStr)
	if ip == nil || ip.To4() == nil {
		return "", fmt.Errorf("invalid IPv4: %s", ipStr)
	}
	return ip.To4().String(), nil
}

func getPublicIP(targetIP string) (string, error) {
	if targetIP != "" {
		ip := net.ParseIP(targetIP)
		if ip == nil || ip.To4() == nil {
			return "", fmt.Errorf("invalid target IPv4: %s", targetIP)
		}
		return ip.To4().String(), nil
	}

	client := &http.Client{Timeout: 5 * time.Second}
	if resp, err := client.Get("https://api.ipify.org"); err == nil {
		if ip, err := readPublicIPv4(resp); err == nil {
			return ip, nil
		}
	}
	if resp, err := client.Get("http://ip-api.com/line/?fields=query"); err == nil {
		if ip, err := readPublicIPv4(resp); err == nil {
			return ip, nil
		}
	}
	return "", fmt.Errorf("failed to fetch valid public IPv4")
}

type RipeStatResponse struct {
	Data struct {
		Prefixes []struct {
			Prefix string `json:"prefix"`
		} `json:"prefixes"`
	} `json:"data"`
}

func fetchASNCIDRs(asn uint) ([]string, error) {
	urlStr := fmt.Sprintf("https://stat.ripe.net/data/announced-prefixes/data.json?resource=AS%d", asn)
	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Get(urlStr)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	var stat RipeStatResponse
	if err := json.NewDecoder(resp.Body).Decode(&stat); err != nil {
		return nil, err
	}

	var cidrs []string
	for _, p := range stat.Data.Prefixes {
		if !strings.Contains(p.Prefix, ":") {
			cidrs = append(cidrs, p.Prefix)
		}
	}
	return cidrs, nil
}

// ================= CIDR & SAMPLING =================

type ipRange struct {
	start uint64
	end   uint64
}

func MergeCIDRs(cidrs []string) []ipRange {
	var ranges []ipRange
	for _, c := range cidrs {
		_, ipnet, err := net.ParseCIDR(c)
		if err != nil {
			continue
		}
		ones, bits := ipnet.Mask.Size()
		if bits != 32 {
			continue
		}

		var count uint64
		if ones == 0 {
			count = 1 << 32
		} else {
			count = uint64(1) << uint(32-ones)
		}

		startInt := uint64(binary.BigEndian.Uint32(ipnet.IP))
		ranges = append(ranges, ipRange{start: startInt, end: startInt + count - 1})
	}

	if len(ranges) == 0 {
		return nil
	}
	sort.Slice(ranges, func(i, j int) bool { return ranges[i].start < ranges[j].start })

	var merged []ipRange
	for _, r := range ranges {
		if len(merged) == 0 {
			merged = append(merged, r)
			continue
		}
		last := &merged[len(merged)-1]
		if r.start <= last.end+1 {
			if r.end > last.end {
				last.end = r.end
			}
		} else {
			merged = append(merged, r)
		}
	}
	return merged
}

func SampleIPs(blocks []ipRange, maxIPs int, seed int64) []string {
	var totalIPs uint64
	for _, b := range blocks {
		totalIPs += (b.end - b.start + 1)
	}
	if totalIPs == 0 {
		return nil
	}

	var sampleSize uint64
	switch {
	case maxIPs < 0:
		sampleSize = totalIPs
	case maxIPs == 0:
		sampleSize = 1024
		if sampleSize > totalIPs {
			sampleSize = totalIPs
		}
	default:
		sampleSize = uint64(maxIPs)
		if sampleSize > totalIPs {
			sampleSize = totalIPs
		}
	}

	rng := rand.New(rand.NewSource(seed))
	startIdx := rng.Uint64() % totalIPs

	var step uint64 = 1
	if totalIPs > 1 {
		for {
			step = (rng.Uint64() % (totalIPs - 1)) + 1
			if gcd(step, totalIPs) == 1 {
				break
			}
		}
	}

	var result []string
	currIdx := startIdx

	for i := uint64(0); i < sampleSize; i++ {
		var offset uint64 = currIdx
		for _, b := range blocks {
			count := (b.end - b.start + 1)
			if offset < count {
				targetInt := uint32(b.start + offset)
				ip := make(net.IP, 4)
				binary.BigEndian.PutUint32(ip, targetInt)
				result = append(result, ip.String())
				break
			}
			offset -= count
		}
		currIdx = (currIdx + step) % totalIPs
	}
	return result
}

func resolveIPv4Cached(ctx context.Context, domain string) ([]string, error) {
	v, err, _ := dnsGroup.Do(domain, func() (interface{}, error) {
		if cached, ok := dnsCache.Get(domain); ok {
			return cached, nil
		}
		dnsCtx, cancel := context.WithTimeout(ctx, 2*time.Second)
		defer cancel()

		ips, err := net.DefaultResolver.LookupIP(dnsCtx, "ip4", domain)
		if err != nil {
			return nil, err
		}

		var res []string
		for _, ip := range ips {
			res = append(res, ip.String())
		}
		dnsCache.Put(domain, res)
		return res, nil
	})
	if err != nil {
		return nil, err
	}
	return v.([]string), nil
}

// ================= HTTP/2 PROBE =================

const clientAdvertisedMaxFrameSize = 16384

type ProbeStage int

const (
	ProbeStageTCP ProbeStage = iota
	ProbeStageTLS
	ProbeStageTLSValidation
	ProbeStageH2
	ProbeStageHeaders
	ProbeStageComplete
)

type ProbeError struct {
	Stage ProbeStage
	Err   error
}

func (e *ProbeError) Error() string {
	return e.Err.Error()
}

func writeH2(conn net.Conn, b []byte, timeout time.Duration) error {
	conn.SetWriteDeadline(time.Now().Add(timeout))
	n, err := conn.Write(b)
	if err != nil {
		return err
	}
	if n != len(b) {
		return fmt.Errorf("short write")
	}
	return nil
}

func buildH2HeadersEncoder(sni string) []byte {
	var buf bytes.Buffer
	encoder := hpack.NewEncoder(&buf)

	encoder.WriteField(hpack.HeaderField{Name: ":method", Value: "GET"})
	encoder.WriteField(hpack.HeaderField{Name: ":authority", Value: sni})
	encoder.WriteField(hpack.HeaderField{Name: ":scheme", Value: "https"})
	encoder.WriteField(hpack.HeaderField{Name: ":path", Value: "/"})
	encoder.WriteField(hpack.HeaderField{Name: "user-agent", Value: "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/151.0.0.0 Safari/537.36"})
	encoder.WriteField(hpack.HeaderField{Name: "accept", Value: "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"})
	encoder.WriteField(hpack.HeaderField{Name: "accept-encoding", Value: "gzip, deflate, br"})

	return buf.Bytes()
}

func buildH2Frame(frameType, flags byte, streamId uint32, payload []byte) []byte {
	length := len(payload)
	header := make([]byte, 9)
	header[0], header[1], header[2] = byte(length>>16), byte(length>>8), byte(length)
	header[3], header[4] = frameType, flags
	binary.BigEndian.PutUint32(header[5:9], streamId&0x7FFFFFFF)
	return append(header, payload...)
}

func buildWindowUpdateFrame(streamID uint32, increment uint32) []byte {
	payload := make([]byte, 4)
	binary.BigEndian.PutUint32(payload, increment&0x7FFFFFFF)
	return buildH2Frame(FrameWindowUpdate, 0, streamID, payload)
}

func ProbeH2(ctx context.Context, ip, sni string, ptrDiscovered, seedProvided, ctDiscovered bool, cfg Config) (*Candidate, *ProbeError) {
	cand := &Candidate{
		IP:            ip,
		SNI:           sni,
		DNSMatched:    true,
		PTRDiscovered: ptrDiscovered,
		SeedProvided:  seedProvided,
		CTDiscovered:  ctDiscovered,
		DomainQuality: classifyDomainQuality(sni),
	}

	t0 := time.Now()
	dialer := &net.Dialer{Timeout: time.Duration(cfg.TCPTimeoutMs) * time.Millisecond}
	conn, err := dialer.DialContext(ctx, "tcp", net.JoinHostPort(ip, "443"))
	if err != nil {
		return cand, &ProbeError{Stage: ProbeStageTCP, Err: err}
	}
	defer conn.Close()
	cand.Timings.TCP = time.Since(t0)

	t1 := time.Now()
	uConn := utls.UClient(conn, &utls.Config{
		ServerName:         sni,
		InsecureSkipVerify: true,
		NextProtos:         []string{"h2"},
		MinVersion:         tls.VersionTLS13,
		MaxVersion:         tls.VersionTLS13,
	}, utls.HelloChrome_Auto)

	uConn.SetDeadline(time.Now().Add(time.Duration(cfg.TLSTimeoutMs) * time.Millisecond))
	if err := uConn.HandshakeContext(ctx); err != nil {
		return cand, &ProbeError{Stage: ProbeStageTLS, Err: err}
	}
	cand.Timings.TLS = time.Since(t1)

	if uConn.ConnectionState().NegotiatedProtocol == "h2" {
		cand.ALPN = "h2"
	} else {
		cand.ALPN = "h2 (no ALPN)"
	}

	state := uConn.ConnectionState()
	if len(state.PeerCertificates) == 0 {
		return cand, &ProbeError{Stage: ProbeStageTLSValidation, Err: fmt.Errorf("no peer certificates provided")}
	}

	cert := state.PeerCertificates[0]
	now := time.Now()

	cand.CertIssuer = cert.Issuer.CommonName
	if cand.CertIssuer == "" && len(cert.Issuer.Organization) > 0 {
		cand.CertIssuer = cert.Issuer.Organization[0]
	}
	cand.CertSubject = cert.Subject.CommonName
	cand.CertSANCount = len(cert.DNSNames) + len(cert.IPAddresses)

	if now.Before(cert.NotBefore) || now.After(cert.NotAfter) {
		return cand, &ProbeError{Stage: ProbeStageTLSValidation, Err: fmt.Errorf("certificate expired or not yet valid")}
	}

	if err := cert.VerifyHostname(sni); err != nil {
		return cand, &ProbeError{Stage: ProbeStageTLSValidation, Err: fmt.Errorf("hostname validation failed: %v", err)}
	}

	opts := x509.VerifyOptions{Roots: nil, Intermediates: x509.NewCertPool()}
	for _, c := range state.PeerCertificates[1:] {
		opts.Intermediates.AddCert(c)
	}
	if _, err := cert.Verify(opts); err == nil {
		cand.CertChainValid = true
	}

	wTo := time.Duration(cfg.H2WriteTimeoutMs) * time.Millisecond

	if err := writeH2(uConn, []byte("PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"), wTo); err != nil {
		return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
	}
	if err := writeH2(uConn, buildH2Frame(FrameSettings, 0, 0, []byte{}), wTo); err != nil {
		return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
	}
	if err := writeH2(uConn, buildH2Frame(FrameHeaders, FlagEndHeaders|FlagEndStream, 1, buildH2HeadersEncoder(sni)), wTo); err != nil {
		return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
	}

	requestSent := time.Now()

	uConn.SetReadDeadline(time.Now().Add(time.Duration(cfg.H2ReadTimeoutMs) * time.Millisecond))

	const maxInboundFrameSize = uint32(clientAdvertisedMaxFrameSize)
	buf := make([]byte, 32768)
	recvBuf := bytes.Buffer{}
	headerBlocks := bytes.Buffer{}
	decoder := hpack.NewDecoder(4096, nil)

	firstFrameSeen := false
	var expectingContinuation bool
	var activeStreamID uint32

ReadLoop:
	for {
		if ctx.Err() != nil {
			return cand, &ProbeError{Stage: ProbeStageH2, Err: ctx.Err()}
		}
		n, err := uConn.Read(buf)
		if n > 0 {
			recvBuf.Write(buf[:n])
		}

		for recvBuf.Len() >= 9 {
			data := recvBuf.Bytes()
			length := uint32(data[0])<<16 | uint32(data[1])<<8 | uint32(data[2])

			if length > maxInboundFrameSize {
				return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("inbound frame exceeds limit: %d", length)}
			}
			if uint32(recvBuf.Len()) < 9+length {
				break
			}

			// Фиксация времени появления полноценного 9-байтового заголовка первого входящего H2-фрейма
			if !firstFrameSeen {
				cand.Timings.H2FirstFrame = time.Since(requestSent)
				firstFrameSeen = true
			}

			frameType, flags := data[3], data[4]
			streamID := binary.BigEndian.Uint32(data[5:9]) & 0x7FFFFFFF
			payload := data[9 : 9+length]
			recvBuf.Next(int(9 + length))

			if expectingContinuation && frameType != FrameContinuation {
				return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("expected CONTINUATION frame, got %d", frameType)}
			}

			switch frameType {
			case FrameSettings:
				if streamID != 0 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("SETTINGS on non-zero stream")}
				}
				if flags&FlagAck != 0 {
					cand.H2SettingsAckReceived = true
					if length != 0 {
						return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("SETTINGS ACK with non-zero payload")}
					}
					break
				}
				if length%6 != 0 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid SETTINGS length")}
				}

				seenSettings := make(map[uint16]bool)
				var prof PeerSettingsProfile
				if cand.H2SettingsReceived {
					prof = cand.LatestPeerSettings
				}

				for i := 0; i < int(length); i += 6 {
					id := binary.BigEndian.Uint16(payload[i : i+2])
					val := binary.BigEndian.Uint32(payload[i+2 : i+6])

					if seenSettings[id] {
						return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("duplicate SETTINGS identifier: %d", id)}
					}
					seenSettings[id] = true

					switch id {
					case 1:
						prof.HeaderTableSize = val
						prof.HasHeaderTableSize = true
					case 2:
						if val > 1 {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid SETTINGS_ENABLE_PUSH: %d", val)}
						}
						prof.EnablePush = val
						prof.HasEnablePush = true
					case 3:
						prof.MaxConcurrentStreams = val
						prof.HasMaxConcurrentStreams = true
					case 4:
						if val > 0x7fffffff {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid INITIAL_WINDOW_SIZE: %d", val)}
						}
						prof.InitialWindowSize = val
						prof.HasInitialWindowSize = true
					case 5:
						if val < 16384 || val > 16777215 {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid MAX_FRAME_SIZE: %d", val)}
						}
						prof.MaxFrameSize = val
						prof.HasMaxFrameSize = true
					case 6:
						prof.MaxHeaderListSize = val
						prof.HasMaxHeaderListSize = true
					}
				}

				cand.LatestPeerSettings = prof
				if !cand.H2SettingsReceived {
					cand.InitialPeerSettings = prof
					cand.H2SettingsReceived = true
				}

				if err := writeH2(uConn, buildH2Frame(FrameSettings, FlagAck, 0, nil), wTo); err != nil {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
				}
				cand.H2SettingsAckSent = true

			case FrameHeaders:
				if streamID == 1 {
					if (flags & FlagEndStream) != 0 {
						cand.EndStreamSeen = true
					}
					actualPayload := payload
					if flags&FlagPadded != 0 {
						if len(actualPayload) < 1 {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("PADDED flag set but payload too short")}
						}
						padLen := int(actualPayload[0])
						actualPayload = actualPayload[1:]
						if padLen > len(actualPayload) {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("padding exceeds payload")}
						}
						actualPayload = actualPayload[:len(actualPayload)-padLen]
					}
					if flags&FlagPriority != 0 {
						if len(actualPayload) < 5 {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("PRIORITY flag set but payload too short")}
						}
						actualPayload = actualPayload[5:]
					}

					headerBlocks.Write(actualPayload)

					if (flags & FlagEndHeaders) == 0 {
						expectingContinuation = true
						activeStreamID = streamID
					} else {
						expectingContinuation = false
						headers, err := decoder.DecodeFull(headerBlocks.Bytes())
						if err != nil {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
						}
						parseHeaders(cand, headers)
						headerBlocks.Reset()
						if !cand.H2HeadersReceived {
							cand.Timings.H2Headers = time.Since(requestSent)
							cand.H2HeadersReceived = true
						}
					}
				}
			case FrameContinuation:
				if !expectingContinuation || streamID != activeStreamID {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("unexpected CONTINUATION")}
				}
				headerBlocks.Write(payload)
				if (flags & FlagEndHeaders) != 0 {
					expectingContinuation = false
					headers, err := decoder.DecodeFull(headerBlocks.Bytes())
					if err != nil {
						return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
					}
					parseHeaders(cand, headers)
					headerBlocks.Reset()
					if !cand.H2HeadersReceived {
						cand.Timings.H2Headers = time.Since(requestSent)
						cand.H2HeadersReceived = true
					}
				}
			case FrameData:
				if streamID == 1 {
					cand.H2DataFrames++
					if (flags & FlagEndStream) != 0 {
						cand.EndStreamSeen = true
					}
					actualPayload := payload
					if flags&FlagPadded != 0 {
						if len(actualPayload) < 1 {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("PADDED flag set on DATA but payload too short")}
						}
						padLen := int(actualPayload[0])
						actualPayload = actualPayload[1:]
						if padLen > len(actualPayload) {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("padding exceeds DATA payload")}
						}
						actualPayload = actualPayload[:len(actualPayload)-padLen]
					}
					cand.BodyBytes += len(actualPayload)

					// RFC 9113: flow control учитывает полный payload включая padding
					inc := length
					if inc > 0 {
						if err := writeH2(uConn, buildWindowUpdateFrame(1, inc), wTo); err != nil {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
						}
						if err := writeH2(uConn, buildWindowUpdateFrame(0, inc), wTo); err != nil {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
						}
					}
				}
			case FrameWindowUpdate:
				if length != 4 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid WINDOW_UPDATE length: %d", length)}
				}
				inc := binary.BigEndian.Uint32(payload) & 0x7fffffff
				if inc == 0 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("WINDOW_UPDATE increment is zero")}
				}
			case FrameRSTStream:
				if length != 4 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid RST_STREAM length: %d", length)}
				}
				if streamID == 1 {
					cand.StreamReset = true
					break ReadLoop
				}
			case FrameGoAway:
				if length < 8 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid GOAWAY length: %d", length)}
				}
				cand.GoAwaySeen = true
			}

			if streamID == 1 && cand.EndStreamSeen && !expectingContinuation {
				break ReadLoop
			}
		}
		if err != nil {
			break
		}
	}

	if cand.HTTPStatus == 0 {
		return cand, &ProbeError{Stage: ProbeStageHeaders, Err: fmt.Errorf("no HTTP status code")}
	}
	if !cand.EndStreamSeen {
		return cand, &ProbeError{Stage: ProbeStageComplete, Err: fmt.Errorf("response did not reach END_STREAM")}
	}

	return cand, nil
}

func parseHeaders(cand *Candidate, headers []hpack.HeaderField) {
	for _, h := range headers {
		hName := strings.ToLower(h.Name)
		hVal := strings.ToLower(h.Value)

		if hName == ":status" {
			fmt.Sscanf(hVal, "%d", &cand.HTTPStatus)
		}
		if hName == "server" {
			cand.Server = h.Value
			for _, cdn := range cdnStrong {
				if strings.Contains(hVal, cdn) {
					cand.CDNStrong = true
				}
			}
		}
		if hName == "content-type" {
			cand.ContentType = hVal
		}
		if hName == "location" {
			cand.Location = h.Value
		}
		for _, cdnH := range cdnWeak {
			if hName == cdnH {
				cand.CDNWeak = true
			}
		}
	}
}

// ================= SCORING & ENRICHMENT =================

func scorePeerSettings(prof PeerSettingsProfile) float64 {
	score := 0.0
	if prof.HasInitialWindowSize && prof.InitialWindowSize >= 65535 {
		score += 2.0
	}
	if prof.HasMaxFrameSize && prof.HasMaxFrameSize >= 16384 {
		score += 2.0
	}
	if prof.HasMaxConcurrentStreams && prof.MaxConcurrentStreams > 0 {
		score += 1.0
	}
	return score
}

func scoreH2Profile(c *Candidate) float64 {
	score := 0.0
	if c.H2SettingsReceived {
		score += 5.0
	}
	if c.H2SettingsAckReceived {
		score += 3.0
	}
	if c.H2DataFrames > 0 {
		score += 3.0
	}
	if c.BodyBytes > 0 {
		score += 2.0
	}
	if c.EndStreamSeen {
		score += 2.0
	}
	score += scorePeerSettings(c.InitialPeerSettings)
	return math.Min(score, 20.0)
}

func validateAndEnrich(cand *Candidate, asnDB, countryDB *geoip2.Reader, cfg Config) bool {
	parsedIP := net.ParseIP(cand.IP)
	if parsedIP != nil {
		if asnDB != nil {
			if r, err := asnDB.ASN(parsedIP); err == nil {
				cand.ASN = uint(r.AutonomousSystemNumber)
			}
		}
		if countryDB != nil {
			if r, err := countryDB.Country(parsedIP); err == nil {
				cand.Country = r.Country.IsoCode
			}
		}
	}

	if cfg.TargetASN != 0 && cand.ASN != cfg.TargetASN {
		stats.mu.Lock()
		stats.ASNFiltered++
		stats.mu.Unlock()
		return false
	}
	if cfg.TargetCountry != "" && !strings.EqualFold(cand.Country, cfg.TargetCountry) {
		stats.mu.Lock()
		stats.CountryFiltered++
		stats.mu.Unlock()
		return false
	}
	if cand.CDNStrong {
		stats.mu.Lock()
		stats.CDNDropped++
		stats.mu.Unlock()
		return false
	}

	rs := RealityScore{}

	if cand.CertChainValid {
		rs.TLSQuality += 15
	} else {
		rs.TLSQuality += 5
	}
	if cand.ALPN == "h2" {
		rs.TLSQuality += 5
	}

	if cand.CertChainValid {
		rs.Certificate += 10
	}
	if cand.CertIssuer != "" && !strings.Contains(strings.ToLower(cand.CertIssuer), "localhost") {
		rs.Certificate += 10
	}

	rs.H2Profile = scoreH2Profile(cand)

	if cand.Server != "" && cand.Server != "-" {
		srvLower := strings.ToLower(cand.Server)
		if strings.Contains(srvLower, "nginx") || strings.Contains(srvLower, "caddy") || strings.Contains(srvLower, "apache") || strings.Contains(srvLower, "openresty") {
			rs.ServerProfile = 10
		} else {
			rs.ServerProfile = 6
		}
	} else {
		rs.ServerProfile = 3
	}

	switch cand.HTTPStatus {
	case 200:
		rs.HTTPBehavior = 10
	case 301, 302, 307, 308:
		rs.HTTPBehavior = 7
	default:
		if cand.HTTPStatus >= 400 && cand.HTTPStatus < 500 {
			rs.HTTPBehavior = 3
		} else if cand.HTTPStatus >= 500 {
			rs.HTTPBehavior = -5
		}
	}

	// Вес доверия к provenance домена
	if cand.PTRDiscovered {
		rs.DNSConsistency += 6.0
	}
	if cand.CTDiscovered {
		rs.DNSConsistency += 4.0
	}
	if !cand.PTRDiscovered && !cand.CTDiscovered && cand.SeedProvided {
		rs.DNSConsistency += 3.0
	}

	rtt := cand.Timings.TotalLatency().Milliseconds()
	if rtt <= 50 {
		rs.Latency = 10
	} else if rtt <= 150 {
		rs.Latency = 7
	} else if rtt <= 300 {
		rs.Latency = 4
	} else {
		rs.Latency = 1
	}

	rs.Total = rs.TLSQuality + rs.Certificate + rs.H2Profile + rs.ServerProfile + rs.HTTPBehavior + rs.DNSConsistency + rs.Latency

	scorePenalty := 0.0
	if cand.DomainQuality == "JunkTLD" {
		scorePenalty = 15.0
	} else if cand.DomainQuality == "DynDNS" {
		scorePenalty = 25.0
	} else if cand.DomainQuality == "Numeric" {
		scorePenalty = 30.0
	}
	if cand.CDNWeak {
		scorePenalty += 5.0
	}

	cand.RealityScore = rs
	cand.DomainPenalty = scorePenalty
	cand.Score = rs.Total - scorePenalty

	return cand.Score >= 0
}

func RunPipeline(ctx context.Context, cfg Config, sampledIPs []string, asnDB, countryDB *geoip2.Reader) []Candidate {
	var mu sync.Mutex
	var validPairs []TargetPair
	var pairSeen sync.Map
	httpClient := &http.Client{Timeout: 10 * time.Second}

	stats.IPSampled = len(sampledIPs)

	g1, gCtx1 := errgroup.WithContext(ctx)
	g1.SetLimit(cfg.Workers)

	fmt.Printf("[*] Этап 1: Сбор доменов и кэшированная проверка DNS (Pre-validation)...\n")
	for _, ip := range sampledIPs {
		ip := ip
		g1.Go(func() error {
			ptrDomains := make(map[string]struct{})
			seedDomains := make(map[string]struct{})
			ctDomains := make(map[string]struct{})

			var localDomains []string

			names, err := net.DefaultResolver.LookupAddr(gCtx1, ip)
			if err == nil {
				ptrFound := false
				for _, n := range names {
					if d := CleanDomain(n); d != "" {
						ptrDomains[d] = struct{}{}
						localDomains = append(localDomains, d)
						ptrFound = true
					}
				}
				if ptrFound {
					stats.mu.Lock()
					stats.IPWithPTR++
					stats.mu.Unlock()
				}
			}

			for _, d := range cfg.Domains {
				if cleaned := CleanDomain(d); cleaned != "" {
					seedDomains[cleaned] = struct{}{}
					localDomains = append(localDomains, cleaned)
				}
			}
			if cfg.DirectSNI != "" {
				if cleaned := CleanDomain(cfg.DirectSNI); cleaned != "" {
					seedDomains[cleaned] = struct{}{}
					localDomains = append(localDomains, cleaned)
				}
			}

			localDomains = uniqueDomains(localDomains)
			var allDomains []string
			allDomains = append(allDomains, localDomains...)

			rootDomains := make(map[string]bool)
			for _, dom := range localDomains {
				root := GetRootDomain(dom)
				if root != "" {
					rootDomains[root] = true
				}
			}

			for root := range rootDomains {
				v, err, _ := crtGroup.Do(root, func() (interface{}, error) {
					if cached, ok := crtCache.Get(root); ok {
						return cached, nil
					}

					result, err := gatherCTDomains(gCtx1, root, httpClient)
					if err != nil {
						return nil, err
					}

					crtCache.Put(root, result)

					uniqueCount := 0
					for _, d := range result {
						if _, loaded := crtSeen.LoadOrStore(d, true); !loaded {
							uniqueCount++
						}
					}
					if uniqueCount > 0 {
						stats.mu.Lock()
						stats.UniqueDiscoveredNames += uniqueCount
						stats.mu.Unlock()
					}
					return result, nil
				})
				if err == nil && v != nil {
					subs := v.([]string)
					for _, s := range subs {
						ctDomains[s] = struct{}{}
						allDomains = append(allDomains, s)
					}
				}
			}

			allDomains = uniqueDomains(allDomains)

			for _, dom := range allDomains {
				ips, err := resolveIPv4Cached(gCtx1, dom)
				if err == nil {
					for _, resolvedIP := range ips {
						if resolvedIP == ip {
							pairKey := ip + "\x00" + dom
							if _, loaded := pairSeen.LoadOrStore(pairKey, true); !loaded {
								_, isPTR := ptrDomains[dom]
								_, isSeed := seedDomains[dom]
								_, isCT := ctDomains[dom]

								mu.Lock()
								validPairs = append(validPairs, TargetPair{
									IP:            ip,
									SNI:           dom,
									PTRDiscovered: isPTR,
									SeedProvided:  isSeed,
									CTDiscovered:  isCT,
								})
								mu.Unlock()
							}
							break
						}
					}
				}
			}
			return nil
		})
	}
	_ = g1.Wait()

	stats.DNSValidPairs = len(validPairs)
	fmt.Printf("[+] Этап 1 завершен. Подтверждено DNS-пар (IP+SNI): %d\n", stats.DNSValidPairs)
	if len(validPairs) == 0 {
		return nil
	}

	fmt.Printf("[*] Этап 2: Активное сканирование HTTP/2 и анализ TLS...\n")
	var candidates []Candidate
	g2, gCtx2 := errgroup.WithContext(ctx)
	g2.SetLimit(cfg.Workers)

	for _, p := range validPairs {
		p := p
		g2.Go(func() error {
			cand, pErr := ProbeH2(gCtx2, p.IP, p.SNI, p.PTRDiscovered, p.SeedProvided, p.CTDiscovered, cfg)

			tcpOK := pErr == nil || pErr.Stage > ProbeStageTCP
			tlsOK := pErr == nil || pErr.Stage > ProbeStageTLS

			stats.mu.Lock()
			if tcpOK {
				stats.TCPConnected++
			}
			if tlsOK {
				stats.TLSHandshakeOK++
			}
			if pErr != nil && pErr.Stage == ProbeStageTLSValidation {
				stats.TLSValidationErr++
			}
			if cand.H2HeadersReceived {
				stats.H2HeadersOK++
			}
			if cand.EndStreamSeen {
				stats.EndStreamOK++
			}
			stats.mu.Unlock()

			if pErr != nil {
				return nil
			}

			if validateAndEnrich(cand, asnDB, countryDB, cfg) {
				mu.Lock()
				candidates = append(candidates, *cand)
				mu.Unlock()
			}
			return nil
		})
	}
	_ = g2.Wait()

	sort.Slice(candidates, func(i, j int) bool {
		if candidates[i].Score != candidates[j].Score {
			return candidates[i].Score > candidates[j].Score
		}
		return candidates[i].Timings.TotalLatency() < candidates[j].Timings.TotalLatency()
	})

	return candidates
}

// ================= MAIN =================

func main() {
	cfg := Config{}
	var modeStr, domainsStr string

	flag.StringVar(&modeStr, "mode", "autonomous", "autonomous | direct")
	flag.IntVar(&cfg.Workers, "w", 30, "Worker pool size")
	flag.IntVar(&cfg.MaxIPs, "max-ips", 0, "Limit for IP sampling (0 = default 1024, -1 = unlimited)")
	flag.IntVar(&cfg.TCPTimeoutMs, "tcp-timeout", 2000, "TCP timeout ms")
	flag.IntVar(&cfg.TLSTimeoutMs, "tls-timeout", 2000, "TLS timeout ms")
	flag.IntVar(&cfg.H2ReadTimeoutMs, "h2-read", 3000, "H2 Read timeout ms")
	flag.IntVar(&cfg.H2WriteTimeoutMs, "h2-write", 2000, "H2 Write timeout ms")
	flag.Int64Var(&cfg.Seed, "seed", time.Now().UnixNano(), "Random seed")
	flag.StringVar(&cfg.TargetCountry, "c", "", "Hard Filter: Target Country Code")
	flag.UintVar(&cfg.TargetASN, "asn", 0, "Hard Filter: Target ASN constraint")
	flag.StringVar(&cfg.TargetIP, "target-ip", "", "Remote Hosting target IP")
	flag.StringVar(&cfg.DirectSNI, "sni", "", "Fallback SNI for Direct mode")
	flag.BoolVar(&cfg.ScanEntireASN, "scan-all-asn", false, "Scan all ASN prefixes")
	flag.StringVar(&domainsStr, "domains", "", "Comma-separated seed domains for OSINT")
	flag.StringVar(&cfg.GeoIPPath, "geoip", "GeoLite2-Country.mmdb", "Path to Country DB")
	flag.StringVar(&cfg.ASNPath, "asn-db", "GeoLite2-ASN.mmdb", "Path to ASN DB")
	flag.Parse()

	if cfg.Workers < 1 {
		cfg.Workers = 1
	}
	cfg.Mode = Mode(modeStr)
	cfg.CIDRs = flag.Args()

	if domainsStr != "" {
		var cleanSeeds []string
		for _, d := range strings.Split(domainsStr, ",") {
			if cleaned := CleanDomain(d); cleaned != "" {
				cleanSeeds = append(cleanSeeds, cleaned)
			}
		}
		cfg.Domains = uniqueDomains(cleanSeeds)
	}
	if cfg.DirectSNI != "" {
		cfg.DirectSNI = CleanDomain(cfg.DirectSNI)
	}

	if cfg.Mode != ModeAuto && cfg.Mode != ModeDirect {
		log.Fatalf("[-] Unknown mode: %s", cfg.Mode)
	}
	if cfg.Mode == ModeDirect && len(cfg.CIDRs) == 0 {
		log.Fatal("[-] Direct mode requires at least one IPv4 CIDR")
	}

	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer cancel()

	if err := ensureDB(cfg.ASNPath, "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-ASN.mmdb"); err != nil {
		log.Fatalf("[-] Ошибка загрузки базы ASN (%s): %v", cfg.ASNPath, err)
	}
	if err := ensureDB(cfg.GeoIPPath, "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb"); err != nil {
		log.Fatalf("[-] Ошибка загрузки базы Country (%s): %v", cfg.GeoIPPath, err)
	}

	var asnDB, countryDB *geoip2.Reader
	if db, err := geoip2.Open(cfg.ASNPath); err == nil {
		asnDB = db
		defer db.Close()
	} else {
		log.Fatal("[-] Failed to open ASN DB")
	}
	if db, err := geoip2.Open(cfg.GeoIPPath); err == nil {
		countryDB = db
		defer db.Close()
	} else {
		log.Fatal("[-] Failed to open GeoIP DB")
	}

	var vpsQueryIP, localPrefix string

	if cfg.Mode == ModeAuto {
		ip, err := getPublicIP(cfg.TargetIP)
		if err != nil {
			log.Fatalf("[-] Ошибка получения публичного IP: %v\n", err)
		}
		vpsQueryIP = ip

		parsedIP := net.ParseIP(vpsQueryIP)
		if cfg.TargetASN == 0 {
			if r, err := asnDB.ASN(parsedIP); err == nil {
				cfg.TargetASN = uint(r.AutonomousSystemNumber)
			} else {
				log.Fatal("[-] Не удалось определить ASN по GeoIP")
			}
		}
		if cfg.TargetCountry == "" {
			if r, err := countryDB.Country(parsedIP); err == nil {
				cfg.TargetCountry = r.Country.IsoCode
			} else {
				log.Fatal("[-] Не удалось определить Country по GeoIP")
			}
		}
	}

	var results []Candidate

	if cfg.Mode == ModeAuto {
		cidrs, err := fetchASNCIDRs(cfg.TargetASN)
		if err != nil || len(cidrs) == 0 {
			log.Fatalf("[-] Failed to fetch CIDRs for AS%d", cfg.TargetASN)
		}

		vpsIPObj := net.ParseIP(vpsQueryIP)
		for _, c := range cidrs {
			_, ipnet, _ := net.ParseCIDR(c)
			if ipnet != nil && ipnet.Contains(vpsIPObj) {
				localPrefix = c
				break
			}
		}

		if !cfg.ScanEntireASN {
			if localPrefix == "" {
				log.Fatal("[-] Target IP is not present in ASN announced prefixes. Use --scan-all-asn to force full scan.")
			}
			cfg.CIDRs = []string{localPrefix}
		} else {
			cfg.CIDRs = cidrs
		}

		merged := MergeCIDRs(cfg.CIDRs)
		sampledIPs := SampleIPs(merged, cfg.MaxIPs, cfg.Seed)

		fmt.Printf("[*] Целевой IP:             %s\n", vpsQueryIP)
		fmt.Printf("[*] Announcing ASN:        AS%d\n", cfg.TargetASN)
		if !cfg.ScanEntireASN {
			fmt.Printf("[*] Фокус на IPv4 prefix:    %s\n", localPrefix)
		}
		fmt.Printf("[*] Страна сервера:          %s (MaxMind GeoIP)\n", cfg.TargetCountry)
		fmt.Printf("[*] Подсетей для скана:      %d\n", len(merged))
		fmt.Printf("[*] Подготовлено %d IP адресов. Запуск...\n", len(sampledIPs))

		results = RunPipeline(ctx, cfg, sampledIPs, asnDB, countryDB)

	} else if cfg.Mode == ModeDirect {
		merged := MergeCIDRs(cfg.CIDRs)
		sampledIPs := SampleIPs(merged, cfg.MaxIPs, cfg.Seed)
		fmt.Printf("[*] Direct Mode: Подготовлено %d IP адресов. Запуск...\n", len(sampledIPs))
		results = RunPipeline(ctx, cfg, sampledIPs, asnDB, countryDB)
	}

	fmt.Println("\n===================================================================================================================")
	fmt.Println("                                   ТЕЛЕМЕТРИЯ СКАНИРОВАНИЯ (PIPELINE STATS)")
	fmt.Println("===================================================================================================================")
	fmt.Printf("[*] IP отобрано для пула:      %d\n", stats.IPSampled)
	fmt.Printf("[*] IP с чистым PTR (Hosts):   %d\n", stats.IPWithPTR)
	fmt.Printf("[*] crt.sh:                    Попыток: %d (Успешно: %d, Ошибок: %d)\n", stats.CRTAttempts, stats.CRTSuccess, stats.CRTFailed)
	fmt.Printf("[*] Cert Spotter Fallback:     Попыток: %d (Успешно: %d, Ошибок: %d)\n", stats.CTFallbackAttempts, stats.CTFallbackSuccess, stats.CTFallbackFailed)
	fmt.Printf("[*] Уникальных DNS имён (CT):  %d\n", stats.UniqueDiscoveredNames)
	fmt.Printf("[*] Подтверждено DNS-пар:      %d\n", stats.DNSValidPairs)
	fmt.Printf("[*] Успешных TCP соединений:   %d\n", stats.TCPConnected)
	fmt.Printf("[*] Успешных TLS хэндшейков:   %d\n", stats.TLSHandshakeOK)
	fmt.Printf("[*] Ошибок валидации TLS:      %d\n", stats.TLSValidationErr)
	fmt.Printf("[*] С откликом H2 Headers:     %d\n", stats.H2HeadersOK)
	fmt.Printf("[*] Финальных кандидатов:      %d\n", len(results))

	if len(results) == 0 {
		fmt.Println("\n[-] Подходящих кандидатов не найдено.")
		return
	}

	fmt.Printf("\n[+] Найдено валидных HTTP/2 целей: %d\n\n", len(results))
	fmt.Printf("%-32.32s | %-15.15s | %-5s | %-4s | %-4s | %-4s | %-4s | %-4s | %-4s | %-4s | %-6s | %-7s\n",
		"Цель (SNI)", "IP адрес", "SCORE", "TLS", "CERT", "H2", "SRV", "HTTP", "DNS", "LAT", "STATUS", "TOTAL")
	fmt.Println(strings.Repeat("-", 125))

	for _, r := range results {
		rs := r.RealityScore
		rttStr := fmt.Sprintf("%d ms", r.Timings.TotalLatency().Milliseconds())
		scoreStr := fmt.Sprintf("%.1f", r.Score)

		fmt.Printf("%-32.32s | %-15.15s | %-5s | %2.0f   | %2.0f   | %2.0f   | %2.0f   | %2.0f   | %2.0f   | %2.0f   | %-6d | %s\n",
			r.SNI, r.IP, scoreStr, rs.TLSQuality, rs.Certificate, rs.H2Profile, rs.ServerProfile, rs.HTTPBehavior, rs.DNSConsistency, rs.Latency, r.HTTPStatus, rttStr)
	}

	best := results[0]
	fmt.Println("\n===================================================================================================================")
	fmt.Println("                                   РЕКОМЕНДУЕМАЯ КОНФИГУРАЦИЯ DEST/SNI")
	fmt.Println("===================================================================================================================")
	fmt.Printf("\"dest\": \"%s:443\",\n", best.SNI)
	fmt.Printf("\"serverNames\": [\n  \"%s\"\n]\n\n", best.SNI)
	fmt.Printf("Подробности лучшего кандидата:\n")
	fmt.Printf("TLS: %.0f/20 | CERT: %.0f/20 | H2: %.0f/20 | SERVER: %.0f/10 | HTTP: %.0f/10 | DNS: %.0f/10 | LATENCY: %.0f/10\n",
		best.RealityScore.TLSQuality, best.RealityScore.Certificate, best.RealityScore.H2Profile, best.RealityScore.ServerProfile, best.RealityScore.HTTPBehavior, best.RealityScore.DNSConsistency, best.RealityScore.Latency)
	fmt.Printf("-------------------------------------------------------------------------------------------------------------------\n")
	fmt.Printf("BASE SCORE: %.1f | PENALTY: -%.1f | FINAL REALITY SCORE: %.1f/100 (HTTP: %d, Total Latency: %d ms)\n", 
		best.RealityScore.Total, best.DomainPenalty, best.Score, best.HTTPStatus, best.Timings.TotalLatency().Milliseconds())
}
