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
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

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

	LimitMaxIPs          = 262144
	MaxDiscoveredDomains = 50000
	LimitValidPairs      = 10000

	providerMaxAttempts    = 3
	providerCBThreshold    = 10
	providerCBCooldown     = 2 * time.Minute
	provider429CBCooldown  = 5 * time.Minute
	providerBackoffInitial = 1 * time.Second
	providerBackoffSecond  = 3 * time.Second
	providerMaxRetryAfter  = 60 * time.Second

	DNSQueryTimeoutDefault = 1500 * time.Millisecond
	PTRQueryTimeoutDefault = 1000 * time.Millisecond
	DNSCooldownBase        = 500 * time.Millisecond
	DNSCooldownMax         = 4 * time.Second
	DNSMaxAttemptsA        = 4
	DNSMaxAttemptsPTR      = 6
	PTRDoHTimeout          = 1200 * time.Millisecond
	DefaultECSIPv4Prefix   = 24
	// Broad anycast/public DNS fallback set. Keep a mix of independent operators:
	// Cloudflare, Google, Quad9, OpenDNS, AdGuard and DNS.WATCH.
	DefaultDNSResolvers = "1.1.1.1,1.0.0.1,8.8.8.8,8.8.4.4,9.9.9.9,149.112.112.112,208.67.222.222,208.67.220.220,94.140.14.140,94.140.14.141,84.200.69.80,84.200.70.40,77.88.8.8,77.88.8.1,9.9.9.10,149.112.112.10"
)

var (
	cdnStrong = []string{"cloudflare", "fastly", "akamai", "ddos-guard", "qrator", "sucuri"}
	cdnWeak   = []string{"x-cache", "x-served-by", "x-edge"}
	junkTLDs  = []string{".xyz", ".top", ".site", ".fun", ".online", ".space", ".pw", ".cc", ".icu", ".click", ".win", ".bid", ".date"}
	dynDNS    = []string{"duckdns.org", "mooo.com", "ddns.net", "freeddns.org", "crabdance.com", "eu.org", "cloudns.cc", "hopto.org", "zapto.org", "sytes.net", "dyn.com", "no-ip.org"}

	domainRe = regexp.MustCompile(`^[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(\.[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+$`)
	numRe    = regexp.MustCompile(`(?i)(^|\.)\d+\.[a-z]{2,}$`)
	stampRe  = regexp.MustCompile(`^sdns://[A-Za-z0-9_-]+=*$`)

	ErrProviderNoData = errors.New("provider returned no data")

	uaRng *rand.Rand
	uaMu  sync.Mutex
)

type Config struct {
	Mode              Mode
	Workers           int
	MaxIPs            int
	IPOSINTLimit      int
	DomainOSINTLimit  int
	DNSWorkers        int
	DNSQueryTimeoutMs int
	ECSIP             string
	ECSPrefix         int
	DNSResolvers      []string
	TCPTimeoutMs      int
	TLSTimeoutMs      int
	H2ReadTimeoutMs   int
	H2WriteTimeoutMs  int
	Seed              int64
	TargetASN         string
	TargetCountry     string
	TargetIP          string
	DirectSNI         string
	ScanEntireASN     bool
	CIDRs             []string
	Domains           []string
	NoPTR             bool
	NoCT              bool
	NoPassive         bool
	NoReverseIP       bool

	VTKey      string
	URLScanKey string
	ChaosKey   string
}

var ErrDNSNXDomain = errors.New("NXDOMAIN")
var ErrDNSTruncated = errors.New("DNS truncated response")

// ================= EVIDENCE & PROVENANCE =================

type DomainSource uint32

const (
	SourceSeed DomainSource = 1 << iota
	SourcePTR
	SourceCRTSh
	SourceCertSpotter
	SourceAlienVault
	SourceWayback
	SourceHackerTarget
	SourceVirusTotalDomain
	SourceVirusTotalIP
	SourceChaos
	SourceURLScan
	SourceAnubis
	SourceThreatMiner
	SourceShodan
	SourceHTDomain
)

func (s DomainSource) Has(flag DomainSource) bool { return s&flag != 0 }

type Evidence struct {
	Direct    DomainSource
	Inherited DomainSource
}

func (e Evidence) Combined() DomainSource { return e.Direct | e.Inherited }

type RootCandidate struct {
	Domain string
	Source DomainSource
	Score  int
}

func rankRootSources(s DomainSource) int {
	score := 0
	if s.Has(SourcePTR) {
		score += 10
	}
	if s.Has(SourceHackerTarget) {
		score += 8
	}
	if s.Has(SourceShodan) {
		score += 8
	}
	if s.Has(SourceVirusTotalIP) || s.Has(SourceVirusTotalDomain) {
		score += 6
	}
	if s.Has(SourceChaos) {
		score += 5
	}
	if s.Has(SourceCRTSh) || s.Has(SourceCertSpotter) {
		score += 4
	}
	if s.Has(SourceAlienVault) || s.Has(SourceURLScan) {
		score += 3
	}
	if s.Has(SourceAnubis) || s.Has(SourceThreatMiner) || s.Has(SourceHTDomain) {
		score += 3
	}
	if s.Has(SourceWayback) {
		score += 2
	}
	if s.Has(SourceSeed) {
		score += 5
	}
	return score
}

type DiscoveryState struct {
	mu                          sync.RWMutex
	domainEvidence              map[string]Evidence
	pairEvidence                map[string]Evidence
	domainsToResolve            map[string]struct{}
	domainsCount                int
	droppedDomainsByGlobalLimit int
	droppedValidPairs           int
}

func NewDiscoveryState() *DiscoveryState {
	return &DiscoveryState{
		domainEvidence:   make(map[string]Evidence),
		pairEvidence:     make(map[string]Evidence),
		domainsToResolve: make(map[string]struct{}),
	}
}

func (s *DiscoveryState) AddDomainSource(d string, direct, inherited DomainSource) {
	s.mu.Lock()
	defer s.mu.Unlock()

	if _, exists := s.domainsToResolve[d]; !exists {
		if s.domainsCount >= MaxDiscoveredDomains {
			s.droppedDomainsByGlobalLimit++
			return
		}
		s.domainsToResolve[d] = struct{}{}
		s.domainsCount++
	}

	ev := s.domainEvidence[d]
	ev.Direct |= direct
	ev.Inherited |= inherited
	s.domainEvidence[d] = ev
}

func (s *DiscoveryState) AddPairSource(ip, d string, src DomainSource) {
	s.mu.Lock()
	defer s.mu.Unlock()

	if _, exists := s.domainsToResolve[d]; !exists {
		if s.domainsCount >= MaxDiscoveredDomains {
			s.droppedDomainsByGlobalLimit++
			return
		}
		s.domainsToResolve[d] = struct{}{}
		s.domainsCount++
	}

	key := ip + "\x00" + d
	evP := s.pairEvidence[key]
	evP.Direct |= src
	s.pairEvidence[key] = evP
}

// ================= MODELS =================

type Timings struct {
	TCP          time.Duration
	TLS          time.Duration
	H2FirstFrame time.Duration
	H2Headers    time.Duration
}

func (t Timings) TotalProbeLatency() time.Duration { return t.TCP + t.TLS + t.H2Headers }

type PeerSettingsProfile struct {
	HeaderTableSize         uint32
	EnablePush              uint32
	MaxConcurrentStreams    uint32
	InitialWindowSize       uint32
	MaxFrameSize            uint32
	MaxHeaderListSize       uint32
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
	DiscoveryScore float64
	Latency        float64
	Total          float64
}

type CDNStatus string

const (
	CDNConfirmed     CDNStatus = "Confirmed"
	CDNLikely        CDNStatus = "Likely"
	CDNStatusUnknown CDNStatus = "Unknown"
)

type Candidate struct {
	IP                    string
	SNI                   string
	ALPN                  string
	TLSCurve              string
	X25519                bool
	RealityFeasible       bool
	CertExpiry            time.Time
	H2HeadersReceived     bool
	ResponseHeadersParsed bool
	ResponseTrailersSeen  bool
	H2ProtocolConfirmed   bool
	TLS13                 bool
	HTTPStatus            int
	Location              string
	BodyBytes             int
	Server                string
	ContentType           string
	Timings               Timings
	ASN                   uint
	Country               string
	CDNProvider           string
	CDNStatus             CDNStatus
	Score                 float64
	DomainPenalty         float64
	RealityScore          RealityScore
	CertChainValid        bool
	EndStreamSeen         bool
	StreamReset           bool
	GoAwaySeen            bool
	Evidence              Evidence
	DomainQuality         string
	CertIssuer            string
	CertSubject           string
	CertSANCount          int
	CertValidTime         bool
	CertSNIMatch          bool
	SettingsFramesCount   int
	SettingsAckCount      int
	SettingsChanges       int
	H2SettingsReceived    bool
	H2SettingsAckSent     bool
	H2SettingsAckReceived bool
	InitialPeerSettings   PeerSettingsProfile
	LatestPeerSettings    PeerSettingsProfile
	H2DataFrames          int
	HPACKErrors           bool
	MissingStatus         bool
	ReadTimeout           bool
}

type TargetPair struct {
	IP       string
	SNI      string
	Evidence Evidence
}

// ================= TELEMETRY & CACHES =================

type ProviderStats struct {
	Attempts      int
	Success       int
	NoData        int
	Partial       int
	Failed        int
	Skipped       int
	WaitCanceled  int
	Timeouts      int
	Retries       int
	RawNames      int
	UniqueNames   int
	InvalidNames  int
	LimitedNames  int
	AcceptedNames int
	LastStatus    int
	LastError     string
	Category      DiscoveryCategory
}

type StatResult int

const (
	StatSuccess StatResult = iota
	StatNoData
	StatPartial
	StatFailed
	StatSkipped
	StatWaitCanceled
)

type StageCStats struct {
	TotalRoots     int
	Assigned       int
	Executed       int
	Success        int
	NoData         int
	Partial        int
	Failed         int
	Skipped        int
	Reassigned     int
	CompletedRoots int
	LostRoots      int
	CanceledRoots  int
	DeferredRoots  int
	Lost           int
}

type PipelineStats struct {
	mu                    sync.Mutex
	IPSampled             int
	IPWithPTR             int
	PTRFound              int
	PTRSystemFallbacks    int
	PTRDoHFallbacks       int
	PTRNegativeResponses  int
	DNSQueries            int
	DNSSuccess            int
	DNSFailed             int
	DNSNXDomain           int
	DNSTimeout            int
	DNSTemporary          int
	DNSNoIPv4             int
	DNSOtherErr           int
	DNSResolvedIPs        int
	DNSUniqueResolvedIPs  int
	DNSUniqueTargetIPs    int
	DNSTargetRangeMatches int
	DNSTargetDomains      int
	DNSValidPairs         int

	// TCP
	TCPConnected int
	TCPTimeouts  int
	TCPRefused   int
	TCPOtherErrs int

	// TLS
	TLSHandshake          int
	TLSTimeouts           int
	TLSValidationFailures int
	NoPeerCertificates    int
	TLSHandshakeFailure   int
	TLSUnrecognizedName   int
	TLSConnectionReset    int
	TLSEOF                int
	TLSOtherErrs          int

	// H2
	H2NoALPN               int
	H2ProtocolOK           int
	H2TimeoutNoFrames      int
	H2ConnectionReset      int
	H2BrokenPipe           int
	H2BadRequest           int
	H2GoAway               int
	H2EOF                  int
	H2TLSAlerts            int
	H2OtherErrs            int
	H2InvalidFrame         int
	H2BadContinuation      int
	H2HPACKDecode          int
	H2MissingSettings      int
	H2HeadersWithoutStatus int
	H2HeadersOK            int
	H2Timeouts             int
	H2HPACKErrors          int
	H2StatusOK             int
	H2InvalidStatus        int
	EndStreamOK            int

	// Final
	ScoreRejected             int
	LowScoreCandidates        int
	CandidatesAccepted        int
	RealityFeasibleCandidates int

	ASNFiltered     int
	CountryFiltered int
	CDNDropped      int

	Alloc         TotalAllocationStats
	StageC        StageCStats
	ProviderStats map[string]*ProviderStats
}

func NewPipelineStats() *PipelineStats {
	return &PipelineStats{
		ProviderStats: make(map[string]*ProviderStats),
	}
}

func (s *PipelineStats) incH2Reason(kind string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.H2OtherErrs++
	switch kind {
	case "invalid-frame":
		s.H2InvalidFrame++
	case "bad-continuation":
		s.H2BadContinuation++
	case "hpack-decode":
		s.H2HPACKDecode++
	case "missing-settings":
		s.H2MissingSettings++
	case "headers-without-status":
		s.H2HeadersWithoutStatus++
	}
}

func (s *PipelineStats) recordProviderStat(name string, cat DiscoveryCategory, result StatResult, isTimeout bool, raw, unique, invalid, limited, accepted, httpStatus int, errText string, retries int) {
	s.mu.Lock()
	defer s.mu.Unlock()

	ps, ok := s.ProviderStats[name]
	if !ok {
		ps = &ProviderStats{Category: cat}
		s.ProviderStats[name] = ps
	}

	ps.Retries += retries

	if result != StatSkipped && result != StatWaitCanceled {
		ps.Attempts++
	}
	if httpStatus != 0 {
		ps.LastStatus = httpStatus
	}
	if errText != "" {
		ps.LastError = errText
	}

	switch result {
	case StatSuccess, StatPartial:
		if result == StatSuccess {
			ps.Success++
		} else {
			ps.Partial++
		}
		ps.RawNames += raw
		ps.UniqueNames += unique
		ps.InvalidNames += invalid
		ps.LimitedNames += limited
		ps.AcceptedNames += accepted
	case StatNoData:
		ps.NoData++
	case StatFailed:
		ps.Failed++
		if isTimeout {
			ps.Timeouts++
		}
	case StatWaitCanceled:
		ps.WaitCanceled++
	case StatSkipped:
		ps.Skipped++
	}
}

type DNSResolverStat struct {
	Attempts int
	Answers  int
	NXDomain int
	Failures int
	Timeouts int
	IPv4s    int
	RTTMs    float64
}

type RuntimeCaches struct {
	ProvCache              *SafeCache
	ProvGroup              *singleflight.Group
	DNSCache               *SafeDNSCache
	DNSGroup               *singleflight.Group
	DNSStatsMu             sync.Mutex
	DNSResolverStats       map[string]*DNSResolverStat
	DNSRoundRobinCursor    int
	DNSCooldownUntil       map[string]time.Time
	DNSConsecutiveFailures map[string]int

	// PTR fallback telemetry. Access under DNSStatsMu.
	PTRSystemFallbacks   int
	PTRDoHFallbacks      int
	PTRNegativeResponses int
	DNSDoHFallbacks      int
	DNSSystemFallbacks   int
}

func NewRuntimeCaches() *RuntimeCaches {
	return &RuntimeCaches{
		ProvCache:              NewSafeCache(),
		ProvGroup:              &singleflight.Group{},
		DNSCache:               NewSafeDNSCache(),
		DNSGroup:               &singleflight.Group{},
		DNSResolverStats:       make(map[string]*DNSResolverStat),
		DNSCooldownUntil:       make(map[string]time.Time),
		DNSConsecutiveFailures: make(map[string]int),
	}
}

func (r *RuntimeCaches) dnsResolverStat(resolver string) *DNSResolverStat {
	r.DNSStatsMu.Lock()
	defer r.DNSStatsMu.Unlock()
	stat, ok := r.DNSResolverStats[resolver]
	if !ok {
		stat = &DNSResolverStat{}
		r.DNSResolverStats[resolver] = stat
	}
	return stat
}

func (r *RuntimeCaches) dnsResolverOrder(resolvers []string) []string {
	if len(resolvers) == 0 {
		return nil
	}
	now := time.Now()
	r.DNSStatsMu.Lock()
	defer r.DNSStatsMu.Unlock()

	start := r.DNSRoundRobinCursor % len(resolvers)
	if start < 0 {
		start = 0
	}
	// Advance the cursor once per logical lookup. The returned order is a
	// cyclic walk, not a health-sorted list. This prevents the healthiest
	// resolver from becoming a permanent hot spot.
	r.DNSRoundRobinCursor = (start + 1) % len(resolvers)

	order := make([]string, 0, len(resolvers))
	var earliest string
	var earliestUntil time.Time
	for i := 0; i < len(resolvers); i++ {
		resolver := resolvers[(start+i)%len(resolvers)]
		until := r.DNSCooldownUntil[resolver]
		if until.IsZero() || !now.Before(until) {
			order = append(order, resolver)
			continue
		}
		if earliest == "" || until.Before(earliestUntil) {
			earliest = resolver
			earliestUntil = until
		}
	}

	// If every resolver is cooling, probe the one whose cooldown expires first;
	// never pin the scan to a fixed resolver.
	if len(order) == 0 && earliest != "" {
		order = append(order, earliest)
	}
	return order
}

func (r *RuntimeCaches) recordDNSResult(resolver string, err error, elapsed time.Duration, ipv4Count int) {
	r.DNSStatsMu.Lock()
	defer r.DNSStatsMu.Unlock()

	stat, ok := r.DNSResolverStats[resolver]
	if !ok {
		stat = &DNSResolverStat{}
		r.DNSResolverStats[resolver] = stat
	}

	stat.Attempts++
	elapsedMs := float64(elapsed.Microseconds()) / 1000.0
	if stat.RTTMs == 0 {
		stat.RTTMs = elapsedMs
	} else {
		stat.RTTMs = stat.RTTMs*0.8 + elapsedMs*0.2
	}

	if err == nil {
		stat.Answers++
		if ipv4Count > 0 {
			stat.IPv4s += ipv4Count
		}
		r.DNSConsecutiveFailures[resolver] = 0
		delete(r.DNSCooldownUntil, resolver)
		return
	}
	if errors.Is(err, ErrDNSNXDomain) {
		stat.NXDomain++
		// NXDOMAIN is a valid DNS response, not a transport/provider failure.
		return
	}

	stat.Failures++
	isTimeout := errors.Is(err, context.DeadlineExceeded) || os.IsTimeout(err)
	if isTimeout {
		stat.Timeouts++
	}

	n := r.DNSConsecutiveFailures[resolver] + 1
	r.DNSConsecutiveFailures[resolver] = n

	cooldown := DNSCooldownBase
	for i := 1; i < n; i++ {
		cooldown *= 2
		if cooldown >= DNSCooldownMax {
			cooldown = DNSCooldownMax
			break
		}
	}
	if !isTimeout {
		if cooldown > 2*time.Second {
			cooldown = 2 * time.Second
		}
	}
	if cooldown > DNSCooldownMax {
		cooldown = DNSCooldownMax
	}
	r.DNSCooldownUntil[resolver] = time.Now().Add(cooldown)
}

type DNSCacheEntry struct {
	IPs      []string
	NXDomain bool
	Expires  time.Time
}

type SafeDNSCache struct {
	mu   sync.RWMutex
	data map[string]*DNSCacheEntry
}

func NewSafeDNSCache() *SafeDNSCache {
	return &SafeDNSCache{data: make(map[string]*DNSCacheEntry)}
}
func (c *SafeDNSCache) Get(key string) (*DNSCacheEntry, bool) {
	c.mu.RLock()
	v, ok := c.data[key]
	c.mu.RUnlock()
	if !ok {
		return nil, false
	}
	if time.Now().After(v.Expires) {
		c.mu.Lock()
		if v2, ok2 := c.data[key]; ok2 && time.Now().After(v2.Expires) {
			delete(c.data, key)
		}
		c.mu.Unlock()
		return nil, false
	}
	var ips []string
	if v.IPs != nil {
		ips = append([]string(nil), v.IPs...)
	}
	return &DNSCacheEntry{IPs: ips, NXDomain: v.NXDomain}, true
}
func (c *SafeDNSCache) Put(key string, entry *DNSCacheEntry, ttl time.Duration) {
	c.mu.Lock()
	defer c.mu.Unlock()
	var ips []string
	if entry.IPs != nil {
		ips = append([]string(nil), entry.IPs...)
	}
	c.data[key] = &DNSCacheEntry{IPs: ips, NXDomain: entry.NXDomain, Expires: time.Now().Add(ttl)}
}

type CacheItem struct {
	Values  []string
	Status  StatResult
	Expires time.Time
}

type SafeCache struct {
	mu   sync.RWMutex
	data map[string]CacheItem
}

func NewSafeCache() *SafeCache {
	return &SafeCache{data: make(map[string]CacheItem)}
}

func (c *SafeCache) Get(key string) ([]string, StatResult, bool) {
	c.mu.RLock()
	v, ok := c.data[key]
	c.mu.RUnlock()
	if !ok {
		return nil, StatFailed, false
	}
	if time.Now().After(v.Expires) {
		c.mu.Lock()
		if v2, ok2 := c.data[key]; ok2 && time.Now().After(v2.Expires) {
			delete(c.data, key)
		}
		c.mu.Unlock()
		return nil, StatFailed, false
	}
	return append([]string(nil), v.Values...), v.Status, true
}

func (c *SafeCache) Put(key string, vals []string, status StatResult, ttl time.Duration) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.data[key] = CacheItem{
		Values:  append([]string(nil), vals...),
		Status:  status,
		Expires: time.Now().Add(ttl),
	}
}

// ================= V17 REMEDIATION PLAN =================
// 1) Keep PTR compatibility: system resolver -> raw UDP/TCP -> DoH; count each path.
// 2) Keep health-aware round-robin for raw DNS, but rank resolvers by observed failure/RTT.
// 3) For A/ECS: UDP -> TCP on timeout/truncation -> DoH with ECS -> system resolver.
// 4) Require two independent NXDOMAIN responses before hard-negative caching.
// 5) Reduce DNS burst pressure from 128 to 64 workers to avoid public-resolver timeout storms.
// 6) Fix URLScan pagination precision by preserving JSON numeric sort values verbatim.
// 7) Use the current Anubis DB API path; isolate quota-limited VT/URLScan from hot provider scheduling.
// 8) Keep score as ranking only; valid H2 + HTTP candidates remain eligible.
// 9) Distinguish pre-cluster accepted candidates from post-cluster output in telemetry.
// ================= END V17 REMEDIATION PLAN =================

// ================= RAW UDP DNS + EDNS CLIENT SUBNET =================

// Raw DNS resolver used for both passive PTR discovery and ECS A lookups.
// No net.LookupHost and no DNSCrypt are used in the pipeline.

func normalizeDNSResolvers(values []string) []string {
	var out []string
	seen := make(map[string]struct{})
	for _, v := range values {
		v = strings.TrimSpace(v)
		if v == "" {
			continue
		}
		if host, _, err := net.SplitHostPort(v); err == nil {
			v = host
		}
		ip := net.ParseIP(v)
		if ip == nil || ip.To4() == nil {
			continue
		}
		v = ip.To4().String()
		if _, ok := seen[v]; ok {
			continue
		}
		seen[v] = struct{}{}
		out = append(out, v)
	}
	return out
}

func randomDNSID() uint16 {
	uaMu.Lock()
	defer uaMu.Unlock()
	if uaRng == nil {
		uaRng = rand.New(rand.NewSource(time.Now().UnixNano()))
	}
	return uint16(uaRng.Intn(1 << 16))
}

func encodeDNSName(name string) ([]byte, error) {
	name = strings.TrimSuffix(strings.TrimSpace(name), ".")
	if name == "" {
		return []byte{0}, nil
	}
	var out []byte
	for _, label := range strings.Split(name, ".") {
		if label == "" || len(label) > 63 {
			return nil, fmt.Errorf("invalid DNS label in %q", name)
		}
		if len(out)+1+len(label)+1 > 255 {
			return nil, fmt.Errorf("DNS name too long: %q", name)
		}
		out = append(out, byte(len(label)))
		out = append(out, label...)
	}
	out = append(out, 0)
	return out, nil
}

func buildECSOption(clientIP string, prefixLen int) ([]byte, error) {
	ip := net.ParseIP(clientIP)
	if ip == nil || ip.To4() == nil {
		return nil, fmt.Errorf("invalid ECS IPv4: %q", clientIP)
	}
	if prefixLen < 0 || prefixLen > 32 {
		return nil, fmt.Errorf("invalid ECS IPv4 prefix length: %d", prefixLen)
	}
	ip4 := append([]byte(nil), ip.To4()...)
	usedBytes := (prefixLen + 7) / 8
	if usedBytes > 0 && prefixLen%8 != 0 {
		ip4[usedBytes-1] &= byte(0xFF << uint(8-(prefixLen%8)))
	}
	ip4 = ip4[:usedBytes]

	payloadLen := 4 + len(ip4)
	option := make([]byte, 4+payloadLen)
	binary.BigEndian.PutUint16(option[0:2], 8)
	binary.BigEndian.PutUint16(option[2:4], uint16(payloadLen))
	binary.BigEndian.PutUint16(option[4:6], 1) // IPv4
	option[6] = byte(prefixLen)
	option[7] = 0 // scope
	copy(option[8:], ip4)
	return option, nil
}

func buildDNSQuery(domain string, qtype uint16, ecsIP string, ecsPrefix int) ([]byte, uint16, error) {
	name, err := encodeDNSName(domain)
	if err != nil {
		return nil, 0, err
	}
	id := randomDNSID()

	buf := make([]byte, 12)
	binary.BigEndian.PutUint16(buf[0:2], id)
	binary.BigEndian.PutUint16(buf[2:4], 0x0100) // RD
	binary.BigEndian.PutUint16(buf[4:6], 1)      // QDCOUNT

	buf = append(buf, name...)
	buf = append(buf, byte(qtype>>8), byte(qtype))
	buf = append(buf, 0x00, 0x01) // IN

	// A lookups use ECS. PTR lookups intentionally do not.
	if qtype == 1 {
		ecs, err := buildECSOption(ecsIP, ecsPrefix)
		if err != nil {
			return nil, 0, err
		}
		binary.BigEndian.PutUint16(buf[10:12], 1) // ARCOUNT
		opt := make([]byte, 11)
		binary.BigEndian.PutUint16(opt[1:3], 41)
		binary.BigEndian.PutUint16(opt[3:5], 1232)
		binary.BigEndian.PutUint16(opt[9:11], uint16(len(ecs)))
		buf = append(buf, opt...)
		buf = append(buf, ecs...)
	}
	return buf, id, nil
}

func readDNSName(msg []byte, off int) (string, int, error) {
	if off < 0 || off >= len(msg) {
		return "", off, fmt.Errorf("DNS name offset out of bounds")
	}
	var labels []string
	pos := off
	jumped := false
	returnPos := off
	jumps := 0
	for {
		if pos >= len(msg) {
			return "", off, fmt.Errorf("DNS name truncated")
		}
		l := msg[pos]
		if l == 0 {
			pos++
			if !jumped {
				returnPos = pos
			}
			return strings.Join(labels, "."), returnPos, nil
		}
		if l&0xC0 == 0xC0 {
			if pos+1 >= len(msg) {
				return "", off, fmt.Errorf("DNS compression pointer truncated")
			}
			ptr := int(l&0x3F)<<8 | int(msg[pos+1])
			if ptr >= len(msg) {
				return "", off, fmt.Errorf("DNS compression pointer out of bounds")
			}
			if !jumped {
				returnPos = pos + 2
				jumped = true
			}
			pos = ptr
			jumps++
			if jumps > 32 {
				return "", off, fmt.Errorf("DNS compression loop")
			}
			continue
		}
		if l > 63 {
			return "", off, fmt.Errorf("invalid DNS label length")
		}
		pos++
		if pos+int(l) > len(msg) {
			return "", off, fmt.Errorf("DNS label truncated")
		}
		labels = append(labels, string(msg[pos:pos+int(l)]))
		pos += int(l)
		if !jumped {
			returnPos = pos
		}
	}
}

func dnsRcode(msg []byte, wantID uint16) (int, int, int, int, int, error) {
	if len(msg) < 12 {
		return 0, 0, 0, 0, 0, fmt.Errorf("short DNS response")
	}
	id := binary.BigEndian.Uint16(msg[0:2])
	if id != wantID {
		return 0, 0, 0, 0, 0, fmt.Errorf("DNS transaction ID mismatch")
	}
	flags := binary.BigEndian.Uint16(msg[2:4])
	if flags&0x8000 == 0 {
		return 0, 0, 0, 0, 0, fmt.Errorf("not a DNS response")
	}
	return int(flags & 0x000F),
		int(binary.BigEndian.Uint16(msg[4:6])),
		int(binary.BigEndian.Uint16(msg[6:8])),
		int(binary.BigEndian.Uint16(msg[8:10])),
		int(binary.BigEndian.Uint16(msg[10:12])),
		nil
}

func parseDNSAResponse(msg []byte, wantID uint16) ([]string, error) {
	rcode, qd, an, ns, ar, err := dnsRcode(msg, wantID)
	if err != nil {
		return nil, err
	}
	if rcode == 3 {
		return nil, ErrDNSNXDomain
	}
	if rcode != 0 {
		return nil, fmt.Errorf("DNS server returned RCODE=%d", rcode)
	}
	off := 12
	for i := 0; i < qd; i++ {
		_, next, err := readDNSName(msg, off)
		if err != nil {
			return nil, err
		}
		off = next
		if off+4 > len(msg) {
			return nil, fmt.Errorf("truncated DNS question")
		}
		off += 4
	}
	var ips []string
	parseRR := func() error {
		_, next, err := readDNSName(msg, off)
		if err != nil {
			return err
		}
		off = next
		if off+10 > len(msg) {
			return fmt.Errorf("truncated DNS RR header")
		}
		qtype := binary.BigEndian.Uint16(msg[off : off+2])
		qclass := binary.BigEndian.Uint16(msg[off+2 : off+4])
		rdlen := int(binary.BigEndian.Uint16(msg[off+8 : off+10]))
		off += 10
		if off+rdlen > len(msg) {
			return fmt.Errorf("truncated DNS RDATA")
		}
		if qtype == 1 && qclass == 1 && rdlen == 4 {
			ips = append(ips, net.IPv4(msg[off], msg[off+1], msg[off+2], msg[off+3]).String())
		}
		off += rdlen
		return nil
	}
	for i := 0; i < an+ns+ar; i++ {
		if err := parseRR(); err != nil {
			return nil, err
		}
	}
	return uniqueStrings(ips), nil
}

func parseDNSPTRResponse(msg []byte, wantID uint16) ([]string, error) {
	rcode, qd, an, ns, ar, err := dnsRcode(msg, wantID)
	if err != nil {
		return nil, err
	}
	if rcode == 3 {
		return nil, ErrDNSNXDomain
	}
	if rcode != 0 {
		return nil, fmt.Errorf("DNS server returned RCODE=%d", rcode)
	}
	off := 12
	for i := 0; i < qd; i++ {
		_, next, err := readDNSName(msg, off)
		if err != nil {
			return nil, err
		}
		off = next
		if off+4 > len(msg) {
			return nil, fmt.Errorf("truncated DNS question")
		}
		off += 4
	}
	var names []string
	parseRR := func() error {
		_, next, err := readDNSName(msg, off)
		if err != nil {
			return err
		}
		off = next
		if off+10 > len(msg) {
			return fmt.Errorf("truncated DNS RR header")
		}
		qtype := binary.BigEndian.Uint16(msg[off : off+2])
		qclass := binary.BigEndian.Uint16(msg[off+2 : off+4])
		rdlen := int(binary.BigEndian.Uint16(msg[off+8 : off+10]))
		off += 10
		if off+rdlen > len(msg) {
			return fmt.Errorf("truncated DNS RDATA")
		}
		if qtype == 12 && qclass == 1 {
			name, _, err := readDNSName(msg, off)
			if err != nil {
				return err
			}
			if d := CleanDomain(name); d != "" {
				names = append(names, d)
			}
		}
		off += rdlen
		return nil
	}
	for i := 0; i < an+ns+ar; i++ {
		if err := parseRR(); err != nil {
			return nil, err
		}
	}
	return uniqueStrings(names), nil
}

func dnsExchangeTCP(ctx context.Context, resolver, domain string, qtype uint16, ecsIP string, ecsPrefix int, timeout time.Duration) ([]string, error) {
	query, id, err := buildDNSQuery(domain, qtype, ecsIP, ecsPrefix)
	if err != nil {
		return nil, err
	}
	addr := net.JoinHostPort(resolver, "53")
	dialer := net.Dialer{}
	conn, err := dialer.DialContext(ctx, "tcp", addr)
	if err != nil {
		return nil, err
	}
	defer conn.Close()
	deadline := time.Now().Add(timeout)
	if dl, ok := ctx.Deadline(); ok && dl.Before(deadline) {
		deadline = dl
	}
	_ = conn.SetDeadline(deadline)
	frame := make([]byte, 2+len(query))
	binary.BigEndian.PutUint16(frame[:2], uint16(len(query)))
	copy(frame[2:], query)
	if _, err := conn.Write(frame); err != nil {
		return nil, err
	}
	var hdr [2]byte
	if _, err := io.ReadFull(conn, hdr[:]); err != nil {
		return nil, err
	}
	length := int(binary.BigEndian.Uint16(hdr[:]))
	if length < 12 || length > 65535 {
		return nil, fmt.Errorf("invalid TCP DNS response length: %d", length)
	}
	buf := make([]byte, length)
	if _, err := io.ReadFull(conn, buf); err != nil {
		return nil, err
	}
	if qtype == 12 {
		return parseDNSPTRResponse(buf, id)
	}
	return parseDNSAResponse(buf, id)
}

func dnsExchangeUDP(ctx context.Context, resolver, domain string, qtype uint16, ecsIP string, ecsPrefix int, timeout time.Duration) ([]string, error) {
	query, id, err := buildDNSQuery(domain, qtype, ecsIP, ecsPrefix)
	if err != nil {
		return nil, err
	}
	addr := net.JoinHostPort(resolver, "53")
	dialer := net.Dialer{}
	conn, err := dialer.DialContext(ctx, "udp", addr)
	if err != nil {
		return nil, err
	}
	defer conn.Close()
	deadline := time.Now().Add(timeout)
	if dl, ok := ctx.Deadline(); ok && dl.Before(deadline) {
		deadline = dl
	}
	_ = conn.SetDeadline(deadline)
	if _, err := conn.Write(query); err != nil {
		return nil, err
	}
	buf := make([]byte, 4096)
	n, err := conn.Read(buf)
	if err != nil {
		return nil, err
	}
	if n >= 4 {
		flags := binary.BigEndian.Uint16(buf[2:4])
		if flags&0x0200 != 0 {
			return nil, ErrDNSTruncated
		}
	}
	if qtype == 12 {
		return parseDNSPTRResponse(buf[:n], id)
	}
	return parseDNSAResponse(buf[:n], id)
}

func resolveHostECS(ctx context.Context, domain, ecsIP string, ecsPrefix int, resolvers []string, timeout time.Duration, rtCaches *RuntimeCaches) ([]string, error) {
	domain = CleanDomain(domain)
	if domain == "" {
		return nil, fmt.Errorf("invalid domain")
	}
	if ecsIP == "" {
		return nil, fmt.Errorf("ECS client IP is empty")
	}
	if len(resolvers) == 0 {
		return nil, fmt.Errorf("DNS resolver pool is empty")
	}
	if timeout <= 0 {
		timeout = DNSQueryTimeoutDefault
	}

	ordered := rtCaches.dnsResolverOrder(resolvers)
	if len(ordered) > DNSMaxAttemptsA {
		ordered = ordered[:DNSMaxAttemptsA]
	}
	var lastErr error
	nxCount := 0
	emptyCount := 0

	for _, resolver := range ordered {
		started := time.Now()
		ips, err := dnsExchangeUDP(ctx, resolver, domain, 1, ecsIP, ecsPrefix, timeout)

		// UDP can fail because the answer was truncated. For transport timeouts
		// and truncation, retry the same resolver over TCP before consuming the
		// next resolver. This mirrors the behavior of a full recursive pool.
		if err != nil && (errors.Is(err, ErrDNSTruncated) || errors.Is(err, context.DeadlineExceeded) || os.IsTimeout(err)) {
			tcpIPs, tcpErr := dnsExchangeTCP(ctx, resolver, domain, 1, ecsIP, ecsPrefix, timeout)
			if tcpErr == nil {
				ips, err = tcpIPs, nil
			} else {
				lastErr = tcpErr
			}
		}
		rtCaches.recordDNSResult(resolver, err, time.Since(started), len(ips))

		if err == nil {
			if len(ips) > 0 {
				return ips, nil
			}
			emptyCount++
			continue
		}
		if errors.Is(err, ErrDNSNXDomain) {
			nxCount++
			// Require two independent negative answers before declaring NXDOMAIN.
			// This prevents one resolver's transient/geo-specific negative answer
			// from suppressing a valid answer from another resolver.
			if nxCount >= 2 {
				return nil, ErrDNSNXDomain
			}
			continue
		}
		if lastErr == nil {
			lastErr = fmt.Errorf("%s: %w", resolver, err)
		}
		if ctx.Err() != nil {
			return nil, ctx.Err()
		}
	}

	// Last-resort DoH with the same ECS prefix. This is intentionally only
	// used after bounded UDP/TCP attempts so healthy public resolvers remain the
	// fast path. It is the primary safety net for VPS networks that throttle UDP/53.
	if dohIPs, dohErr := resolveADoH(ctx, domain, ecsIP, ecsPrefix, PTRDoHTimeout); dohErr == nil && len(dohIPs) > 0 {
		rtCaches.DNSStatsMu.Lock()
		rtCaches.DNSDoHFallbacks++
		rtCaches.DNSStatsMu.Unlock()
		return dohIPs, nil
	} else if dohErr != nil {
		lastErr = dohErr
	}

	// Final compatibility fallback through the host resolver. This path does
	// not guarantee ECS, but is preferable to losing a live name completely.
	if sysIPs, sysErr := resolveASystem(ctx, domain); sysErr == nil && len(sysIPs) > 0 {
		rtCaches.DNSStatsMu.Lock()
		rtCaches.DNSSystemFallbacks++
		rtCaches.DNSStatsMu.Unlock()
		return sysIPs, nil
	}

	if nxCount > 0 && emptyCount+nxCount == len(ordered) {
		return nil, ErrDNSNXDomain
	}
	if lastErr == nil {
		lastErr = fmt.Errorf("all DNS resolvers failed")
	}
	return nil, lastErr
}

func resolvePTRRaw(ctx context.Context, ip string, resolvers []string, timeout time.Duration, rtCaches *RuntimeCaches) ([]string, error) {
	rev, err := reverseIPv4(ip)
	if err != nil {
		return nil, err
	}

	// The old Linux scanner got PTRs through a mature recursive resolver pool.
	// In the raw-UDP build, UDP/53 from a VPS can be selectively filtered while
	// the local/system resolver still has working access to the reverse zone.
	// Try the system resolver first: it is the fastest compatibility path and
	// preserves the old scanner's PTR behavior without giving up raw DNS.
	lookupCtx, cancel := context.WithTimeout(ctx, timeout)
	names, lookupErr := net.DefaultResolver.LookupAddr(lookupCtx, ip)
	cancel()
	if lookupErr == nil && len(names) > 0 {
		clean := make([]string, 0, len(names))
		for _, n := range names {
			if d := CleanDomain(strings.TrimSuffix(strings.TrimSpace(n), ".")); d != "" {
				clean = append(clean, d)
			}
		}
		if len(clean) > 0 {
			rtCaches.DNSStatsMu.Lock()
			rtCaches.PTRSystemFallbacks++
			rtCaches.DNSStatsMu.Unlock()
			return uniqueStrings(clean), nil
		}
	}

	if len(resolvers) == 0 {
		if lookupErr != nil {
			return nil, lookupErr
		}
		return nil, fmt.Errorf("DNS resolver pool is empty")
	}
	if timeout <= 0 {
		timeout = PTRQueryTimeoutDefault
	}

	ordered := rtCaches.dnsResolverOrder(resolvers)
	if len(ordered) > DNSMaxAttemptsPTR {
		ordered = ordered[:DNSMaxAttemptsPTR]
	}
	var lastErr error
	nxCount := 0
	emptyCount := 0
	for _, resolver := range ordered {
		started := time.Now()
		names, err := dnsExchangeUDP(ctx, resolver, rev, 12, "", 0, timeout)
		if err != nil && (errors.Is(err, context.DeadlineExceeded) || os.IsTimeout(err)) {
			if tcpNames, tcpErr := dnsExchangeTCP(ctx, resolver, rev, 12, "", 0, timeout); tcpErr == nil {
				names, err = tcpNames, nil
			}
		}
		rtCaches.recordDNSResult(resolver, err, time.Since(started), 0)

		if err == nil {
			if len(names) > 0 {
				return names, nil
			}
			emptyCount++
			continue
		}
		if errors.Is(err, ErrDNSNXDomain) {
			nxCount++
			rtCaches.DNSStatsMu.Lock()
			rtCaches.PTRNegativeResponses++
			rtCaches.DNSStatsMu.Unlock()
			// NXDOMAIN from one recursive resolver is not sufficient here: the old
			// scanner used a much broader resolver population. Keep checking the
			// other healthy fallback resolvers before declaring a negative result.
			continue
		}
		lastErr = fmt.Errorf("%s: %w", resolver, err)
		if ctx.Err() != nil {
			return nil, ctx.Err()
		}
	}

	if dohNames, dohErr := resolvePTRDoH(ctx, rev, PTRDoHTimeout); dohErr == nil && len(dohNames) > 0 {
		rtCaches.DNSStatsMu.Lock()
		rtCaches.PTRDoHFallbacks++
		rtCaches.DNSStatsMu.Unlock()
		return dohNames, nil
	} else if dohErr != nil {
		lastErr = dohErr
	}

	if nxCount == len(ordered) || (nxCount > 0 && emptyCount+nxCount == len(ordered)) {
		return nil, ErrDNSNXDomain
	}
	if lastErr == nil {
		lastErr = fmt.Errorf("all DNS resolvers returned no PTR")
	}
	return nil, lastErr
}

func resolveADoH(ctx context.Context, domain, ecsIP string, ecsPrefix int, timeout time.Duration) ([]string, error) {
	if timeout <= 0 {
		timeout = 1200 * time.Millisecond
	}
	ecs := ecsIP
	if parsed := net.ParseIP(ecsIP); parsed != nil && parsed.To4() != nil {
		masked := append(net.IP(nil), parsed.To4()...)
		used := (ecsPrefix + 7) / 8
		if used > 0 && ecsPrefix%8 != 0 {
			masked[used-1] &= byte(0xFF << uint(8-(ecsPrefix%8)))
		}
		for i := used; i < 4; i++ {
			masked[i] = 0
		}
		ecs = masked.String() + "/" + strconv.Itoa(ecsPrefix)
	}
	endpoints := []string{
		"https://dns.google/resolve",
		"https://cloudflare-dns.com/dns-query",
	}
	var lastErr error
	for _, endpoint := range endpoints {
		values := url.Values{}
		values.Set("name", domain)
		values.Set("type", "A")
		if ecs != "" {
			values.Set("edns_client_subnet", ecs)
		}
		reqCtx, cancel := context.WithTimeout(ctx, timeout)
		req, err := http.NewRequestWithContext(reqCtx, http.MethodGet, endpoint+"?"+values.Encode(), nil)
		if err != nil {
			cancel()
			lastErr = err
			continue
		}
		req.Header.Set("Accept", "application/dns-json")
		req.Header.Set("User-Agent", "reality-scanner/1.0")
		resp, err := (&http.Client{Timeout: timeout}).Do(req)
		if err != nil {
			cancel()
			lastErr = err
			continue
		}
		var payload struct {
			Status int `json:"Status"`
			Answer []struct {
				Type int    `json:"type"`
				Data string `json:"data"`
			} `json:"Answer"`
		}
		decodeErr := json.NewDecoder(io.LimitReader(resp.Body, 1<<20)).Decode(&payload)
		resp.Body.Close()
		cancel()
		if decodeErr != nil {
			lastErr = decodeErr
			continue
		}
		if payload.Status == 3 {
			return nil, ErrDNSNXDomain
		}
		if payload.Status != 0 {
			lastErr = fmt.Errorf("DoH DNS status=%d", payload.Status)
			continue
		}
		ips := make([]string, 0, len(payload.Answer))
		for _, answer := range payload.Answer {
			if answer.Type != 1 {
				continue
			}
			if ip := net.ParseIP(strings.TrimSpace(answer.Data)); ip != nil && ip.To4() != nil {
				ips = append(ips, ip.To4().String())
			}
		}
		return uniqueStrings(ips), nil
	}
	if lastErr == nil {
		lastErr = fmt.Errorf("DNS A DoH fallback failed")
	}
	return nil, lastErr
}

func resolveASystem(ctx context.Context, domain string) ([]string, error) {
	lookupCtx, cancel := context.WithTimeout(ctx, 1200*time.Millisecond)
	defer cancel()
	addrs, err := net.DefaultResolver.LookupIPAddr(lookupCtx, domain)
	if err != nil {
		return nil, err
	}
	ips := make([]string, 0, len(addrs))
	for _, addr := range addrs {
		if ip := addr.IP.To4(); ip != nil {
			ips = append(ips, ip.String())
		}
	}
	return uniqueStrings(ips), nil
}

func resolvePTRDoH(ctx context.Context, rev string, timeout time.Duration) ([]string, error) {
	endpoints := []string{
		"https://dns.google/resolve?name=" + url.QueryEscape(rev) + "&type=PTR",
		"https://cloudflare-dns.com/dns-query?name=" + url.QueryEscape(rev) + "&type=PTR",
	}
	client := &http.Client{Timeout: timeout}
	var lastErr error
	for _, endpoint := range endpoints {
		reqCtx, cancel := context.WithTimeout(ctx, timeout)
		req, err := http.NewRequestWithContext(reqCtx, http.MethodGet, endpoint, nil)
		if err != nil {
			cancel()
			lastErr = err
			continue
		}
		req.Header.Set("Accept", "application/dns-json")
		req.Header.Set("User-Agent", "reality-scanner/1.0")
		resp, err := client.Do(req)
		if err != nil {
			cancel()
			lastErr = err
			continue
		}
		var payload struct {
			Status int `json:"Status"`
			Answer []struct {
				Type int    `json:"type"`
				Data string `json:"data"`
			} `json:"Answer"`
		}
		decodeErr := json.NewDecoder(io.LimitReader(resp.Body, 1<<20)).Decode(&payload)
		resp.Body.Close()
		cancel()
		if decodeErr != nil {
			lastErr = decodeErr
			continue
		}
		if payload.Status == 3 {
			return nil, ErrDNSNXDomain
		}
		if payload.Status != 0 {
			lastErr = fmt.Errorf("DoH DNS status=%d", payload.Status)
			continue
		}
		var names []string
		for _, answer := range payload.Answer {
			if answer.Type != 12 {
				continue
			}
			if d := CleanDomain(strings.TrimSuffix(strings.TrimSpace(answer.Data), ".")); d != "" {
				names = append(names, d)
			}
		}
		return uniqueStrings(names), nil
	}
	if lastErr == nil {
		lastErr = fmt.Errorf("PTR DoH fallback failed")
	}
	return nil, lastErr
}

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
	domain = CleanDomain(domain)
	if domain == "" {
		return ""
	}
	root, err := publicsuffix.EffectiveTLDPlusOne(domain)
	if err != nil {
		return ""
	}
	return root
}

func limitStr(s string, n int) string {
	if n <= 0 {
		return ""
	}
	r := []rune(s)
	if len(r) <= n {
		return s
	}
	if n <= 3 {
		return string(r[:n])
	}
	return string(r[:n-3]) + "..."
}

func uniqueStrings(values []string) []string {
	seen := make(map[string]bool)
	var result []string
	for _, v := range values {
		if !seen[v] {
			seen[v] = true
			result = append(result, v)
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

var userAgents = []string{
	"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
	"Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
	"Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:125.0) Gecko/20100101 Firefox/125.0",
	"Mozilla/5.0 (Macintosh; Intel Mac OS X 10.15; rv:125.0) Gecko/20100101 Firefox/125.0",
}

func setBrowserHeaders(req *http.Request) {
	uaMu.Lock()
	ua := userAgents[uaRng.Intn(len(userAgents))]
	uaMu.Unlock()
	req.Header.Set("User-Agent", ua)
	req.Header.Set("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8")
	req.Header.Set("Accept-Language", "en-US,en;q=0.5")
	req.Header.Set("Upgrade-Insecure-Requests", "1")
	req.Header.Set("Sec-Fetch-Dest", "document")
	req.Header.Set("Sec-Fetch-Mode", "navigate")
	req.Header.Set("Sec-Fetch-Site", "none")
}

// ================= SNI PROVIDERS =================

type ProviderHTTPError struct {
	StatusCode int
	Body       string
	RetryAfter time.Duration
}

func (e *ProviderHTTPError) Error() string {
	if e.Body == "" {
		return fmt.Sprintf("http %d", e.StatusCode)
	}
	body := strings.TrimSpace(e.Body)
	body = strings.Join(strings.Fields(body), " ")
	if len(body) > 240 {
		body = body[:240] + "..."
	}
	return fmt.Sprintf("http %d: %s", e.StatusCode, body)
}

func makeProviderHTTPError(resp *http.Response) error {
	bodyBytes, _ := io.ReadAll(io.LimitReader(resp.Body, 4096))
	body := strings.TrimSpace(string(bodyBytes))
	body = strings.Join(strings.Fields(body), " ")

	var retryAfter time.Duration
	if v := resp.Header.Get("Retry-After"); v != "" {
		if secs, err := strconv.Atoi(strings.TrimSpace(v)); err == nil && secs >= 0 {
			retryAfter = time.Duration(secs) * time.Second
		} else if t, err := time.Parse(time.RFC1123, v); err == nil {
			if d := time.Until(t); d > 0 {
				retryAfter = d
			}
		}
	}
	if retryAfter > providerMaxRetryAfter {
		retryAfter = providerMaxRetryAfter
	}

	return &ProviderHTTPError{
		StatusCode: resp.StatusCode,
		Body:       body,
		RetryAfter: retryAfter,
	}
}

func providerCooldown(err error) (time.Duration, bool) {
	var httpErr *ProviderHTTPError
	if !errors.As(err, &httpErr) {
		return 0, false
	}

	switch httpErr.StatusCode {
	case http.StatusTooManyRequests:
		if httpErr.RetryAfter > 0 {
			return httpErr.RetryAfter, true
		}
		return provider429CBCooldown, true

	case http.StatusForbidden,
		http.StatusUnauthorized,
		http.StatusBadRequest,
		http.StatusNotFound,
		http.StatusMethodNotAllowed,
		http.StatusGone,
		http.StatusUnprocessableEntity:
		return providerCBCooldown, true

	case http.StatusInternalServerError,
		http.StatusBadGateway,
		http.StatusServiceUnavailable,
		http.StatusGatewayTimeout:
		return providerCBCooldown, true
	}

	return 0, false
}

type ProviderQueryType int

const (
	QueryIP ProviderQueryType = iota
	QueryDomain
)

type DiscoveryCategory string

const (
	CatReverseIP   DiscoveryCategory = "Reverse-IP"
	CatCertificate DiscoveryCategory = "Certificate"
	CatPassiveDNS  DiscoveryCategory = "Passive DNS"
	CatArchive     DiscoveryCategory = "Archive"
)

type ProviderConfig struct {
	Timeout       time.Duration
	MaxConcurrent int
	MinInterval   time.Duration
	MaxRoots      int
	MaxNames      int
	MaxPages      int
}

type ExecResult struct {
	Names  []string
	Status StatResult
}

type SNIProvider interface {
	Name() string
	Category() DiscoveryCategory
	QueryType() ProviderQueryType
	SourceBit() DomainSource
	Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error)
}

type ProviderRunner struct {
	SNIProvider
	Config        ProviderConfig
	sem           chan struct{}
	mu            sync.Mutex
	nextAllowed   time.Time
	cbFailures    int
	cbUntil       time.Time
	disabled      bool
	disableReason string
}

func NewRunner(p SNIProvider, cfg ProviderConfig) *ProviderRunner {
	r := &ProviderRunner{
		SNIProvider: p,
		Config:      cfg,
	}
	if cfg.MaxConcurrent > 0 {
		r.sem = make(chan struct{}, cfg.MaxConcurrent)
	}
	return r
}

func (r *ProviderRunner) StatsKey() string {
	switch r.QueryType() {
	case QueryIP:
		return r.Name() + "[IP]"
	case QueryDomain:
		return r.Name() + "[Domain]"
	default:
		return r.Name()
	}
}

func isProviderBlocked(p *ProviderRunner) bool {
	p.mu.Lock()
	defer p.mu.Unlock()
	if p.disabled {
		return true
	}
	return !p.cbUntil.IsZero() && time.Now().Before(p.cbUntil)
}

func providerDisabled(p *ProviderRunner) (bool, string) {
	p.mu.Lock()
	defer p.mu.Unlock()
	if p.disabled {
		return true, p.disableReason
	}
	if !p.cbUntil.IsZero() && time.Now().Before(p.cbUntil) {
		return true, fmt.Sprintf("circuit-open until %s", p.cbUntil.Format(time.RFC3339))
	}
	return false, ""
}

func providerShouldDisableForRun(err error) bool {
	var httpErr *ProviderHTTPError
	if !errors.As(err, &httpErr) {
		return false
	}
	body := strings.ToLower(httpErr.Body)
	switch httpErr.StatusCode {
	case http.StatusUnauthorized, http.StatusForbidden, http.StatusTooManyRequests, http.StatusPaymentRequired:
		return true
	}
	for _, marker := range []string{"quota exceeded", "rate limit", "rate_limited", "api count exceeded", "authenticate", "api key required", "anonymous access", "quota for 'search' exceeded"} {
		if strings.Contains(body, marker) {
			return true
		}
	}
	return false
}

func (r *ProviderRunner) waitRate(ctx context.Context) error {
	if r.Config.MinInterval <= 0 {
		return nil
	}

	r.mu.Lock()
	now := time.Now()
	slot := now
	if now.Before(r.nextAllowed) {
		slot = r.nextAllowed
	}
	r.nextAllowed = slot.Add(r.Config.MinInterval)
	r.mu.Unlock()

	wait := time.Until(slot)
	if wait <= 0 {
		return nil
	}

	timer := time.NewTimer(wait)
	defer timer.Stop()

	select {
	case <-timer.C:
		return nil
	case <-ctx.Done():
		return fmt.Errorf("rate limit wait canceled: %w", ctx.Err())
	}
}

func providerHTTPStatus(err error) int {
	var httpErr *ProviderHTTPError
	if errors.As(err, &httpErr) {
		return httpErr.StatusCode
	}
	return 0
}

func (r *ProviderRunner) Execute(ctx context.Context, query string, client *http.Client, pipeStats *PipelineStats, rtCaches *RuntimeCaches) ExecResult {
	if err := ctx.Err(); err != nil {
		return ExecResult{Names: nil, Status: StatWaitCanceled}
	}

	statName := r.StatsKey()
	cacheKey := fmt.Sprintf("%s:%d:%s:maxnames=%d:maxpages=%d", r.Name(), r.QueryType(), query, r.Config.MaxNames, r.Config.MaxPages)

	if cached, status, ok := rtCaches.ProvCache.Get(cacheKey); ok {
		return ExecResult{Names: cached, Status: status}
	}

	v, _, _ := rtCaches.ProvGroup.Do(cacheKey, func() (interface{}, error) {
		if blocked, reason := providerDisabled(r); blocked {
			pipeStats.recordProviderStat(statName, r.Category(), StatSkipped, false, 0, 0, 0, 0, 0, 0, reason, 0)
			return ExecResult{nil, StatSkipped}, nil
		}

		if errWait := r.waitRate(ctx); errWait != nil {
			pipeStats.recordProviderStat(statName, r.Category(), StatWaitCanceled, false, 0, 0, 0, 0, 0, 0, fmt.Sprintf("wait cancelled: %v", errWait), 0)
			return ExecResult{nil, StatWaitCanceled}, nil
		}

		// Re-check after waiting: a queued job may have been admitted before the
		// provider returned 401/403/429. Never let stale queued work hit a provider
		// that has already declared itself unavailable for this run.
		if blocked, reason := providerDisabled(r); blocked {
			pipeStats.recordProviderStat(statName, r.Category(), StatSkipped, false, 0, 0, 0, 0, 0, 0, reason, 0)
			return ExecResult{nil, StatSkipped}, nil
		}

		if r.sem != nil {
			select {
			case r.sem <- struct{}{}:
			case <-ctx.Done():
				return ExecResult{nil, StatWaitCanceled}, nil
			}
		}

		reqCtx, cancel := context.WithTimeout(ctx, r.Config.Timeout)
		rawRes, err := r.Fetch(reqCtx, query, client, r.Config)
		cancel()

		if r.sem != nil {
			<-r.sem
		}

		if err != nil && ctx.Err() != nil {
			pipeStats.recordProviderStat(statName, r.Category(), StatWaitCanceled, false, 0, 0, 0, 0, 0, 0, "root canceled", 0)
			return ExecResult{nil, StatWaitCanceled}, nil
		}

		httpStatus := providerHTTPStatus(err)
		isTimeout := errors.Is(err, context.DeadlineExceeded) || os.IsTimeout(err)

		rawCount := len(rawRes)
		var validRes []string
		invalidCount := 0

		for _, s := range rawRes {
			if d := CleanDomain(s); d != "" {
				validRes = append(validRes, d)
			} else {
				invalidCount++
			}
		}

		cleanRes := uniqueStrings(validRes)
		uniqueCount := len(cleanRes)
		acceptedCount := uniqueCount
		limitedCount := 0

		if r.Config.MaxNames > 0 && acceptedCount > r.Config.MaxNames {
			acceptedCount = r.Config.MaxNames
			limitedCount = uniqueCount - acceptedCount
			cleanRes = cleanRes[:acceptedCount]
		}

		if err != nil {
			if errors.Is(err, ErrProviderNoData) {
				r.mu.Lock()
				r.cbFailures = 0
				r.cbUntil = time.Time{}
				r.mu.Unlock()
				pipeStats.recordProviderStat(statName, r.Category(), StatNoData, false, 0, 0, 0, 0, 0, httpStatus, err.Error(), 0)
				rtCaches.ProvCache.Put(cacheKey, []string{}, StatNoData, 2*time.Minute)
				return ExecResult{[]string{}, StatNoData}, nil
			}

			if !errors.Is(err, context.Canceled) {
				if providerShouldDisableForRun(err) {
					r.mu.Lock()
					r.disabled = true
					r.disableReason = err.Error()
					r.mu.Unlock()
				} else {
					cooldown, hardBlock := providerCooldown(err)
					r.mu.Lock()
					if hardBlock {
						r.cbUntil = time.Now().Add(cooldown)
					} else {
						r.cbFailures++
						if r.cbFailures >= providerCBThreshold {
							r.cbUntil = time.Now().Add(providerCBCooldown)
						}
					}
					r.mu.Unlock()
				}
			} else {
				r.mu.Lock()
				r.cbFailures = 0
				r.mu.Unlock()
			}

			if len(cleanRes) > 0 {
				pipeStats.recordProviderStat(statName, r.Category(), StatPartial, isTimeout, rawCount, uniqueCount, invalidCount, limitedCount, acceptedCount, httpStatus, err.Error(), 0)
				rtCaches.ProvCache.Put(cacheKey, cleanRes, StatPartial, 2*time.Minute)
				return ExecResult{cleanRes, StatPartial}, nil
			}

			pipeStats.recordProviderStat(statName, r.Category(), StatFailed, isTimeout, rawCount, uniqueCount, invalidCount, limitedCount, acceptedCount, httpStatus, err.Error(), 0)
			return ExecResult{nil, StatFailed}, nil
		}

		r.mu.Lock()
		if !r.disabled {
			r.cbFailures = 0
			r.cbUntil = time.Time{}
		}
		r.mu.Unlock()

		if len(cleanRes) == 0 {
			pipeStats.recordProviderStat(statName, r.Category(), StatNoData, false, rawCount, uniqueCount, invalidCount, limitedCount, acceptedCount, httpStatus, "http 200: no valid names found", 0)
			rtCaches.ProvCache.Put(cacheKey, []string{}, StatNoData, 2*time.Minute)
			return ExecResult{[]string{}, StatNoData}, nil
		}

		pipeStats.recordProviderStat(statName, r.Category(), StatSuccess, false, rawCount, uniqueCount, invalidCount, limitedCount, acceptedCount, 0, "", 0)
		rtCaches.ProvCache.Put(cacheKey, cleanRes, StatSuccess, 10*time.Minute)
		return ExecResult{cleanRes, StatSuccess}, nil
	})

	if v != nil {
		return v.(ExecResult)
	}
	return ExecResult{nil, StatFailed}
}

// -------------------------------------------------
// Implementations: Free Providers (No API Keys)
// -------------------------------------------------
type shodanInternetDBProvider struct{}

func (p *shodanInternetDBProvider) Name() string                 { return "Shodan InternetDB" }
func (p *shodanInternetDBProvider) Category() DiscoveryCategory  { return CatReverseIP }
func (p *shodanInternetDBProvider) QueryType() ProviderQueryType { return QueryIP }
func (p *shodanInternetDBProvider) SourceBit() DomainSource      { return SourceShodan }
func (p *shodanInternetDBProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	u := fmt.Sprintf("https://internetdb.shodan.io/%s", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
	if err != nil {
		return nil, err
	}
	setBrowserHeaders(req)
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode == http.StatusNotFound {
		return nil, ErrProviderNoData
	}
	if resp.StatusCode != http.StatusOK {
		return nil, makeProviderHTTPError(resp)
	}
	var res struct {
		Hostnames []string `json:"hostnames"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&res); err != nil {
		return nil, err
	}
	return res.Hostnames, nil
}

type anubisProvider struct{}

func (p *anubisProvider) Name() string                 { return "Anubis DB" }
func (p *anubisProvider) Category() DiscoveryCategory  { return CatPassiveDNS }
func (p *anubisProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *anubisProvider) SourceBit() DomainSource      { return SourceAnubis }
func (p *anubisProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	u := fmt.Sprintf("https://anubisdb.com/subdomains/%s", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
	if err != nil {
		return nil, err
	}
	setBrowserHeaders(req)
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, makeProviderHTTPError(resp)
	}
	var subs []string
	if err := json.NewDecoder(resp.Body).Decode(&subs); err != nil {
		return nil, err
	}
	return subs, nil
}

type threatMinerProvider struct{}

func (p *threatMinerProvider) Name() string                 { return "ThreatMiner" }
func (p *threatMinerProvider) Category() DiscoveryCategory  { return CatPassiveDNS }
func (p *threatMinerProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *threatMinerProvider) SourceBit() DomainSource      { return SourceThreatMiner }
func (p *threatMinerProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	u := fmt.Sprintf("https://api.threatminer.org/v2/domain.php?q=%s&rt=5", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
	if err != nil {
		return nil, err
	}
	setBrowserHeaders(req)
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, makeProviderHTTPError(resp)
	}
	var res struct {
		Results []string `json:"results"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&res); err != nil {
		return nil, err
	}
	return res.Results, nil
}

type hackerTargetHostSearchProvider struct{}

func (p *hackerTargetHostSearchProvider) Name() string                 { return "HT HostSearch" }
func (p *hackerTargetHostSearchProvider) Category() DiscoveryCategory  { return CatPassiveDNS }
func (p *hackerTargetHostSearchProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *hackerTargetHostSearchProvider) SourceBit() DomainSource      { return SourceHTDomain }
func (p *hackerTargetHostSearchProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	u := fmt.Sprintf("https://api.hackertarget.com/hostsearch/?q=%s", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
	if err != nil {
		return nil, err
	}
	setBrowserHeaders(req)
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, makeProviderHTTPError(resp)
	}
	buf := new(bytes.Buffer)
	_, _ = buf.ReadFrom(resp.Body)
	content := buf.String()
	if strings.Contains(strings.ToLower(content), "api count exceeded") {
		return nil, &ProviderHTTPError{StatusCode: http.StatusTooManyRequests, Body: content}
	}
	var result []string
	for _, line := range strings.Split(content, "\n") {
		parts := strings.Split(line, ",")
		if len(parts) > 0 {
			result = append(result, parts[0])
		}
	}
	return result, nil
}

type crtShProvider struct{}

func (p *crtShProvider) Name() string                 { return "crt.sh" }
func (p *crtShProvider) Category() DiscoveryCategory  { return CatCertificate }
func (p *crtShProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *crtShProvider) SourceBit() DomainSource      { return SourceCRTSh }
func (p *crtShProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	u := fmt.Sprintf("https://crt.sh/?q=%%25.%s&output=json", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
	if err != nil {
		return nil, err
	}
	setBrowserHeaders(req)
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, makeProviderHTTPError(resp)
	}
	var ctRes []struct {
		NameValue string `json:"name_value"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&ctRes); err != nil {
		return nil, err
	}
	var subs []string
	for _, rec := range ctRes {
		for _, part := range strings.Split(rec.NameValue, "\n") {
			subs = append(subs, part)
		}
	}
	return subs, nil
}

type certSpotterProvider struct{}

func (p *certSpotterProvider) Name() string                 { return "CertSpotter" }
func (p *certSpotterProvider) Category() DiscoveryCategory  { return CatCertificate }
func (p *certSpotterProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *certSpotterProvider) SourceBit() DomainSource      { return SourceCertSpotter }
func (p *certSpotterProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	var result []string
	after := ""
	maxPages := cfg.MaxPages
	if maxPages <= 0 {
		maxPages = 1
	}
	for page := 0; page < maxPages; page++ {
		u := fmt.Sprintf("https://api.certspotter.com/v1/issuances?domain=%s&include_subdomains=true&expand=dns_names", url.QueryEscape(query))
		if after != "" {
			u += "&after=" + url.QueryEscape(after)
		}
		req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
		if err != nil {
			return result, err
		}
		setBrowserHeaders(req)
		resp, err := client.Do(req)
		if err != nil {
			return result, err
		}
		if resp.StatusCode != http.StatusOK {
			errProv := makeProviderHTTPError(resp)
			resp.Body.Close()
			if len(result) > 0 {
				return result, errProv
			}
			return nil, errProv
		}
		var issuances []struct {
			ID       string   `json:"id"`
			DNSNames []string `json:"dns_names"`
		}
		err = json.NewDecoder(resp.Body).Decode(&issuances)
		resp.Body.Close()
		if err != nil {
			if len(result) > 0 {
				return result, err
			}
			return nil, err
		}
		if len(issuances) == 0 {
			break
		}
		previousAfter := after
		for _, iss := range issuances {
			result = append(result, iss.DNSNames...)
			after = iss.ID
		}
		if after == "" || after == previousAfter {
			break
		}
	}
	return result, nil
}

type alienVaultProvider struct{}

func (p *alienVaultProvider) Name() string                 { return "AlienVault" }
func (p *alienVaultProvider) Category() DiscoveryCategory  { return CatPassiveDNS }
func (p *alienVaultProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *alienVaultProvider) SourceBit() DomainSource      { return SourceAlienVault }
func (p *alienVaultProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	var result []string
	maxPages := cfg.MaxPages
	if maxPages <= 0 {
		maxPages = 1
	}
	u := fmt.Sprintf("https://otx.alienvault.com/api/v1/indicators/domain/%s/passive_dns", url.QueryEscape(query))
	for page := 0; page < maxPages; page++ {
		req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
		if err != nil {
			return result, err
		}
		setBrowserHeaders(req)
		resp, err := client.Do(req)
		if err != nil {
			return result, err
		}
		if resp.StatusCode != http.StatusOK {
			errProv := makeProviderHTTPError(resp)
			resp.Body.Close()
			if len(result) > 0 {
				return result, errProv
			}
			return nil, errProv
		}
		var otxRes struct {
			PassiveDNS []struct {
				Hostname string `json:"hostname"`
			} `json:"passive_dns"`
			Next string `json:"next"`
		}
		err = json.NewDecoder(resp.Body).Decode(&otxRes)
		resp.Body.Close()
		if err != nil {
			if len(result) > 0 {
				return result, err
			}
			return nil, err
		}
		for _, entry := range otxRes.PassiveDNS {
			result = append(result, entry.Hostname)
		}
		if otxRes.Next == "" {
			break
		}
		previousURL := u
		if !strings.HasPrefix(otxRes.Next, "http") {
			if strings.HasPrefix(otxRes.Next, "/api") {
				u = "https://otx.alienvault.com" + otxRes.Next
			} else {
				break
			}
		} else {
			if !strings.HasPrefix(otxRes.Next, "https://otx.alienvault.com") {
				break
			}
			u = otxRes.Next
		}
		if u == previousURL {
			break
		}
	}
	return result, nil
}

type waybackProvider struct{}

func (p *waybackProvider) Name() string                 { return "WaybackMachine" }
func (p *waybackProvider) Category() DiscoveryCategory  { return CatArchive }
func (p *waybackProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *waybackProvider) SourceBit() DomainSource      { return SourceWayback }
func (p *waybackProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	u := fmt.Sprintf("https://web.archive.org/cdx/search/cdx?url=*.%s/*&output=json&collapse=urlkey&fl=original&limit=10000", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
	if err != nil {
		return nil, err
	}
	setBrowserHeaders(req)
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, makeProviderHTTPError(resp)
	}
	var cdx [][]string
	if err := json.NewDecoder(resp.Body).Decode(&cdx); err != nil {
		return nil, err
	}
	var result []string
	for i, row := range cdx {
		if i == 0 || len(row) < 1 {
			continue
		}
		if parsed, err := url.Parse(row[0]); err == nil && parsed.Hostname() != "" {
			result = append(result, parsed.Hostname())
		}
	}
	return result, nil
}

type hackerTargetProvider struct{}

func (p *hackerTargetProvider) Name() string                 { return "HackerTarget" }
func (p *hackerTargetProvider) Category() DiscoveryCategory  { return CatReverseIP }
func (p *hackerTargetProvider) QueryType() ProviderQueryType { return QueryIP }
func (p *hackerTargetProvider) SourceBit() DomainSource      { return SourceHackerTarget }
func (p *hackerTargetProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	u := fmt.Sprintf("https://api.hackertarget.com/reverseiplookup/?q=%s", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
	if err != nil {
		return nil, err
	}
	setBrowserHeaders(req)
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, makeProviderHTTPError(resp)
	}
	buf := new(bytes.Buffer)
	_, _ = buf.ReadFrom(resp.Body)
	content := buf.String()
	if strings.Contains(strings.ToLower(content), "api count exceeded") {
		return nil, &ProviderHTTPError{StatusCode: http.StatusTooManyRequests, Body: content}
	}
	return strings.Split(content, "\n"), nil
}

// -------------------------------------------------
// Implementations: Enterprise API Providers
// -------------------------------------------------
type vtDomainProvider struct{ Key string }

func (p *vtDomainProvider) Name() string                 { return "VirusTotal" }
func (p *vtDomainProvider) Category() DiscoveryCategory  { return CatPassiveDNS }
func (p *vtDomainProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *vtDomainProvider) SourceBit() DomainSource      { return SourceVirusTotalDomain }
func (p *vtDomainProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	var subs []string
	cursor := ""
	maxPages := cfg.MaxPages
	if maxPages <= 0 {
		maxPages = 3
	}
	for page := 0; page < maxPages; page++ {
		u := fmt.Sprintf("https://www.virustotal.com/api/v3/domains/%s/subdomains?limit=40", url.QueryEscape(query))
		if cursor != "" {
			u += "&cursor=" + url.QueryEscape(cursor)
		}
		req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
		if err != nil {
			return subs, err
		}
		setBrowserHeaders(req)
		req.Header.Add("x-apikey", p.Key)
		resp, err := client.Do(req)
		if err != nil {
			return subs, err
		}
		if resp.StatusCode != http.StatusOK {
			errProv := makeProviderHTTPError(resp)
			resp.Body.Close()
			if len(subs) > 0 {
				return subs, errProv
			}
			return nil, errProv
		}
		var res struct {
			Data []struct {
				Id string `json:"id"`
			} `json:"data"`
			Meta struct {
				Cursor string `json:"cursor"`
			} `json:"meta"`
		}
		err = json.NewDecoder(resp.Body).Decode(&res)
		resp.Body.Close()
		if err != nil {
			if len(subs) > 0 {
				return subs, err
			}
			return nil, err
		}
		for _, item := range res.Data {
			subs = append(subs, item.Id)
		}
		if cursor == res.Meta.Cursor || res.Meta.Cursor == "" {
			break
		}
		cursor = res.Meta.Cursor
	}
	return subs, nil
}

type vtIPProvider struct{ Key string }

func (p *vtIPProvider) Name() string                 { return "VirusTotal" }
func (p *vtIPProvider) Category() DiscoveryCategory  { return CatReverseIP }
func (p *vtIPProvider) QueryType() ProviderQueryType { return QueryIP }
func (p *vtIPProvider) SourceBit() DomainSource      { return SourceVirusTotalIP }
func (p *vtIPProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	var subs []string
	cursor := ""
	maxPages := cfg.MaxPages
	if maxPages <= 0 {
		maxPages = 3
	}
	for page := 0; page < maxPages; page++ {
		u := fmt.Sprintf("https://www.virustotal.com/api/v3/ip_addresses/%s/resolutions?limit=40", url.QueryEscape(query))
		if cursor != "" {
			u += "&cursor=" + url.QueryEscape(cursor)
		}
		req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
		if err != nil {
			return subs, err
		}
		setBrowserHeaders(req)
		req.Header.Add("x-apikey", p.Key)
		resp, err := client.Do(req)
		if err != nil {
			return subs, err
		}
		if resp.StatusCode != http.StatusOK {
			errProv := makeProviderHTTPError(resp)
			resp.Body.Close()
			if len(subs) > 0 {
				return subs, errProv
			}
			return nil, errProv
		}
		var res struct {
			Data []struct {
				Attributes struct {
					HostName string `json:"host_name"`
				} `json:"attributes"`
			} `json:"data"`
			Meta struct {
				Cursor string `json:"cursor"`
			} `json:"meta"`
		}
		err = json.NewDecoder(resp.Body).Decode(&res)
		resp.Body.Close()
		if err != nil {
			if len(subs) > 0 {
				return subs, err
			}
			return nil, err
		}
		for _, item := range res.Data {
			subs = append(subs, item.Attributes.HostName)
		}
		if cursor == res.Meta.Cursor || res.Meta.Cursor == "" {
			break
		}
		cursor = res.Meta.Cursor
	}
	return subs, nil
}

type URLScanSearchResponse struct {
	Results []struct {
		Page struct {
			Domain string `json:"domain"`
		} `json:"page"`
		Sort []json.RawMessage `json:"sort"`
	} `json:"results"`
	HasMore bool `json:"has_more"`
}

func fetchURLScanSearch(ctx context.Context, query string, key string, client *http.Client, maxPages int) ([]string, error) {
	var domains []string
	searchAfter := ""
	if maxPages <= 0 {
		maxPages = 1
	}
	for page := 0; page < maxPages; page++ {
		values := url.Values{}
		values.Set("q", query)
		values.Set("size", "10000")
		if searchAfter != "" {
			values.Set("search_after", searchAfter)
		}
		reqURL := "https://urlscan.io/api/v1/search/?" + values.Encode()
		req, err := http.NewRequestWithContext(ctx, http.MethodGet, reqURL, nil)
		if err != nil {
			return domains, err
		}
		setBrowserHeaders(req)
		req.Header.Set("api-key", key)

		resp, err := client.Do(req)
		if err != nil {
			return domains, err
		}
		if resp.StatusCode != http.StatusOK {
			errProv := makeProviderHTTPError(resp)
			resp.Body.Close()
			if len(domains) > 0 {
				return domains, errProv
			}
			return nil, errProv
		}
		var res URLScanSearchResponse
		err = json.NewDecoder(resp.Body).Decode(&res)
		resp.Body.Close()
		if err != nil {
			if len(domains) > 0 {
				return domains, err
			}
			return nil, err
		}
		for _, item := range res.Results {
			domains = append(domains, item.Page.Domain)
		}
		if !res.HasMore || len(res.Results) == 0 {
			break
		}

		lastSort := res.Results[len(res.Results)-1].Sort
		if len(lastSort) > 0 {
			parts := make([]string, 0, len(lastSort))
			for _, raw := range lastSort {
				raw = bytes.TrimSpace(raw)
				if len(raw) == 0 {
					return domains, fmt.Errorf("invalid empty urlscan sort value")
				}
				if raw[0] == '"' {
					var v string
					if err := json.Unmarshal(raw, &v); err != nil {
						return domains, fmt.Errorf("invalid urlscan string sort value: %w", err)
					}
					parts = append(parts, v)
				} else {
					// Preserve numeric precision exactly; converting to float64 turns
					// the 13-digit URLScan timestamp into scientific notation and causes 400.
					parts = append(parts, string(raw))
				}
			}
			newSearchAfter := strings.Join(parts, ",")
			if searchAfter == newSearchAfter {
				break
			}
			searchAfter = newSearchAfter
		} else {
			break
		}
	}
	return domains, nil
}

type urlScanDomainProvider struct{ Key string }

func (p *urlScanDomainProvider) Name() string                 { return "URLScan" }
func (p *urlScanDomainProvider) Category() DiscoveryCategory  { return CatArchive }
func (p *urlScanDomainProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *urlScanDomainProvider) SourceBit() DomainSource      { return SourceURLScan }
func (p *urlScanDomainProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	return fetchURLScanSearch(ctx, "domain:"+query, p.Key, client, cfg.MaxPages)
}

type urlScanIPProvider struct{ Key string }

func (p *urlScanIPProvider) Name() string                 { return "URLScan" }
func (p *urlScanIPProvider) Category() DiscoveryCategory  { return CatArchive }
func (p *urlScanIPProvider) QueryType() ProviderQueryType { return QueryIP }
func (p *urlScanIPProvider) SourceBit() DomainSource      { return SourceURLScan }
func (p *urlScanIPProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	return fetchURLScanSearch(ctx, "page.ip:"+query, p.Key, client, cfg.MaxPages)
}

type chaosProvider struct{ Key string }

func (p *chaosProvider) Name() string                 { return "Chaos" }
func (p *chaosProvider) Category() DiscoveryCategory  { return CatPassiveDNS }
func (p *chaosProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *chaosProvider) SourceBit() DomainSource      { return SourceChaos }
func (p *chaosProvider) Fetch(ctx context.Context, query string, client *http.Client, cfg ProviderConfig) ([]string, error) {
	u := fmt.Sprintf("https://dns.projectdiscovery.io/dns/%s/subdomains", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
	if err != nil {
		return nil, err
	}
	setBrowserHeaders(req)
	req.Header.Add("Authorization", p.Key)
	req.Header.Set("Connection", "close")
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, makeProviderHTTPError(resp)
	}
	var res struct {
		Subdomains []string `json:"subdomains"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&res); err != nil {
		return nil, err
	}
	var subs []string
	for _, sub := range res.Subdomains {
		subs = append(subs, sub+"."+query)
	}
	return subs, nil
}

// ================= PIPELINE SCHEDULING & SAMPLING =================

func sampleForProvider(sampled []string, limit int, seed int64, providerIndex int) []string {
	n := len(sampled)
	if limit <= 0 || limit >= n {
		out := make([]string, n)
		copy(out, sampled)
		return out
	}
	h := uint64(seed) + uint64(providerIndex)*0x9E3779B97F4A7C15
	rng := rand.New(rand.NewSource(int64(h)))

	indices := make([]int, n)
	for i := 0; i < n; i++ {
		indices[i] = i
	}
	out := make([]string, limit)
	for i := 0; i < limit; i++ {
		j := i + rng.Intn(n-i)
		indices[i], indices[j] = indices[j], indices[i]
		out[i] = sampled[indices[i]]
	}
	return out
}

type TotalAllocationStats struct {
	TotalRoots            int
	AssignedRoots         int
	OverlappedAssignments int
	UnassignedRoots       int
	PrimaryAssignments    map[string]int
	OverlapAssignments    map[string]int
}

func effectiveRootLimit(p *ProviderRunner, cfg Config) int {
	limit := p.Config.MaxRoots
	if cfg.DomainOSINTLimit > 0 && (limit <= 0 || cfg.DomainOSINTLimit < limit) {
		limit = cfg.DomainOSINTLimit
	}
	return limit
}

func containsRoot(list []RootCandidate, root string) bool {
	for _, r := range list {
		if r.Domain == root {
			return true
		}
	}
	return false
}

func distributeRoots(roots []RootCandidate, providers []*ProviderRunner, overlapPercent int, cfg Config, isBlocked func(*ProviderRunner) bool) (map[*ProviderRunner][]RootCandidate, TotalAllocationStats) {
	stats := TotalAllocationStats{
		TotalRoots:         len(roots),
		PrimaryAssignments: make(map[string]int),
		OverlapAssignments: make(map[string]int),
	}
	result := make(map[*ProviderRunner][]RootCandidate)
	if len(providers) == 0 || len(roots) == 0 {
		stats.UnassignedRoots = len(roots)
		return result, stats
	}

	capacity := make(map[*ProviderRunner]int)
	for _, p := range providers {
		result[p] = make([]RootCandidate, 0)
		limit := effectiveRootLimit(p, cfg)
		if limit <= 0 {
			limit = len(roots)
		}
		if isBlocked(p) {
			capacity[p] = 0
		} else {
			capacity[p] = limit
		}
	}

	rootIdx := 0
	for rootIdx < len(roots) {
		assignedThisRound := 0
		for _, p := range providers {
			if rootIdx >= len(roots) {
				break
			}
			if len(result[p]) < capacity[p] {
				result[p] = append(result[p], roots[rootIdx])
				stats.PrimaryAssignments[p.StatsKey()]++
				stats.AssignedRoots++
				rootIdx++
				assignedThisRound++
			}
		}
		if assignedThisRound == 0 {
			break
		}
	}
	stats.UnassignedRoots = len(roots) - rootIdx

	if overlapPercent > 0 {
		for _, p := range providers {
			remaining := capacity[p] - len(result[p])
			if remaining <= 0 {
				continue
			}

			ovCap := (capacity[p] * overlapPercent) / 100
			if ovCap <= 0 {
				ovCap = 1
			}
			if ovCap > remaining {
				ovCap = remaining
			}

			added := 0
			for j := 0; j < len(roots) && added < ovCap; j++ {
				cand := roots[j]

				if containsRoot(result[p], cand.Domain) {
					continue
				}

				result[p] = append(result[p], cand)
				stats.OverlapAssignments[p.StatsKey()]++
				stats.OverlappedAssignments++
				added++
			}
		}
	}

	return result, stats
}

func runProviderJobs(
	ctx context.Context,
	provider *ProviderRunner,
	queries []string,
	client *http.Client,
	pipeStats *PipelineStats,
	rtCaches *RuntimeCaches,
	handler func(string, []string),
) error {
	workers := provider.Config.MaxConcurrent
	if workers <= 0 {
		workers = 1
	}

	jobs := make(chan string)
	g, gctx := errgroup.WithContext(ctx)

	for i := 0; i < workers; i++ {
		g.Go(func() error {
			for {
				select {
				case <-gctx.Done():
					return gctx.Err()
				case q, ok := <-jobs:
					if !ok {
						return nil
					}
					res := provider.Execute(gctx, q, client, pipeStats, rtCaches)
					if len(res.Names) > 0 {
						handler(q, res.Names)
					}
				}
			}
		})
	}

	g.Go(func() error {
		defer close(jobs)
		for _, q := range queries {
			select {
			case jobs <- q:
			case <-gctx.Done():
				return gctx.Err()
			}
		}
		return nil
	})

	return g.Wait()
}

type RootState uint8

const (
	RootPending RootState = iota
	RootCompleted
	RootLost
	RootCanceled
	RootDeferred
)

type RootJob struct {
	Root   RootCandidate
	Ctx    context.Context
	Cancel context.CancelFunc
}

func RunStageC(
	ctx context.Context,
	roots []RootCandidate,
	providers []*ProviderRunner,
	cfg Config,
	client *http.Client,
	pipeStats *PipelineStats,
	rtCaches *RuntimeCaches,
	ds *DiscoveryState,
	rootProvenance map[string]DomainSource,
) {
	if len(roots) == 0 {
		return
	}

	if len(providers) == 0 {
		pipeStats.mu.Lock()
		pipeStats.StageC.TotalRoots = len(roots)
		pipeStats.StageC.DeferredRoots = len(roots)
		pipeStats.mu.Unlock()
		return
	}

	providerRoots, allocStats := distributeRoots(
		roots,
		providers,
		20,
		cfg,
		isProviderBlocked,
	)

	pipeStats.mu.Lock()
	pipeStats.Alloc = allocStats
	pipeStats.StageC.TotalRoots = len(roots)
	pipeStats.mu.Unlock()

	providerLimits := make(map[*ProviderRunner]int, len(providers))
	providerUsed := make(map[*ProviderRunner]int, len(providers))

	for _, p := range providers {
		limit := effectiveRootLimit(p, cfg)
		if limit <= 0 || limit > len(roots) {
			limit = len(roots)
		}
		providerLimits[p] = limit
		providerUsed[p] = 0
	}

	jobQueues := make(map[*ProviderRunner]chan RootJob, len(providers))
	for _, p := range providers {
		queueSize := providerLimits[p] * 2
		if queueSize < 1 {
			queueSize = 1
		}
		jobQueues[p] = make(chan RootJob, queueSize)
	}

	type stageResult struct {
		provider *ProviderRunner
		root     RootCandidate
		result   ExecResult
	}

	totalCapacity := 0
	for _, p := range providers {
		totalCapacity += providerLimits[p] * 2
	}
	if totalCapacity < 1 {
		totalCapacity = 1
	}

	resultsCh := make(chan stageResult, totalCapacity)
	var workerWG sync.WaitGroup

	for _, p := range providers {
		p := p
		workers := p.Config.MaxConcurrent
		if workers <= 0 {
			workers = 1
		}

		for i := 0; i < workers; i++ {
			workerWG.Add(1)
			go func() {
				defer workerWG.Done()
				for job := range jobQueues[p] {
					res := p.Execute(job.Ctx, job.Root.Domain, client, pipeStats, rtCaches)

					select {
					case resultsCh <- stageResult{
						provider: p,
						root:     job.Root,
						result:   res,
					}:
					case <-ctx.Done():
						return
					}
				}
			}()
		}
	}

	rootStates := make(map[string]RootState, len(roots))
	scheduled := make(map[string]map[*ProviderRunner]bool, len(roots))
	rootCtx := make(map[string]context.Context, len(roots))
	rootCancel := make(map[string]context.CancelFunc, len(roots))
	rootSkipped := make(map[string]bool, len(roots))

	for _, root := range roots {
		rctx, cancel := context.WithCancel(ctx)
		rootCtx[root.Domain] = rctx
		rootCancel[root.Domain] = cancel

		rootStates[root.Domain] = RootPending
		scheduled[root.Domain] = make(map[*ProviderRunner]bool)
	}

	markCompleted := func(domain string) {
		if rootStates[domain] != RootPending {
			return
		}
		rootStates[domain] = RootCompleted

		if cancel, ok := rootCancel[domain]; ok {
			cancel()
		}

		pipeStats.mu.Lock()
		pipeStats.StageC.CompletedRoots++
		pipeStats.mu.Unlock()
	}

	markLost := func(domain string) {
		if rootStates[domain] != RootPending {
			return
		}
		rootStates[domain] = RootLost

		if cancel, ok := rootCancel[domain]; ok {
			cancel()
		}

		pipeStats.mu.Lock()
		pipeStats.StageC.LostRoots++
		pipeStats.StageC.Lost++
		pipeStats.mu.Unlock()
	}

	markCanceled := func(domain string) {
		if rootStates[domain] != RootPending {
			return
		}
		rootStates[domain] = RootCanceled

		if cancel, ok := rootCancel[domain]; ok {
			cancel()
		}

		pipeStats.mu.Lock()
		pipeStats.StageC.CanceledRoots++
		pipeStats.mu.Unlock()
	}

	markDeferred := func(domain string) {
		if rootStates[domain] != RootPending {
			return
		}
		rootStates[domain] = RootDeferred

		if cancel, ok := rootCancel[domain]; ok {
			cancel()
		}

		pipeStats.mu.Lock()
		pipeStats.StageC.DeferredRoots++
		pipeStats.mu.Unlock()
	}

	enqueueRoot := func(root RootCandidate, preferred *ProviderRunner) bool {
		candidates := make([]*ProviderRunner, 0, len(providers))
		if preferred != nil {
			candidates = append(candidates, preferred)
		}
		for _, p := range providers {
			if p != preferred {
				candidates = append(candidates, p)
			}
		}

		for _, p := range candidates {
			if scheduled[root.Domain][p] {
				continue
			}
			if isProviderBlocked(p) {
				continue
			}
			if providerUsed[p] >= providerLimits[p]*2 {
				continue
			}

			scheduled[root.Domain][p] = true
			providerUsed[p]++
			jobQueues[p] <- RootJob{
				Root:   root,
				Ctx:    rootCtx[root.Domain],
				Cancel: rootCancel[root.Domain],
			}
			return true
		}
		return false
	}

	inFlight := 0

	for _, p := range providers {
		for _, root := range providerRoots[p] {
			if rootStates[root.Domain] != RootPending {
				continue
			}
			if scheduled[root.Domain][p] {
				continue
			}
			if enqueueRoot(root, p) {
				inFlight++
			}
		}
	}

	for _, root := range roots {
		if rootStates[root.Domain] != RootPending {
			continue
		}
		if len(scheduled[root.Domain]) == 0 {
			if !enqueueRoot(root, nil) {
				markDeferred(root.Domain)
			} else {
				inFlight++
			}
		}
	}

	assignedCount := 0
	for _, root := range roots {
		assignedCount += len(scheduled[root.Domain])
	}
	pipeStats.mu.Lock()
	pipeStats.StageC.Assigned = assignedCount
	pipeStats.mu.Unlock()

	findNextProvider := func(domain string) (*ProviderRunner, bool) {
		var openFound bool

		for _, candidate := range providers {
			if scheduled[domain][candidate] {
				continue
			}
			if providerUsed[candidate] >= providerLimits[candidate]*2 {
				continue
			}
			if isProviderBlocked(candidate) {
				openFound = true
				continue
			}
			return candidate, false
		}
		return nil, openFound
	}

SchedulerLoop:
	for inFlight > 0 {
		select {
		case <-ctx.Done():
			for _, root := range roots {
				if rootStates[root.Domain] == RootPending {
					markCanceled(root.Domain)
				}
			}
			break SchedulerLoop

		case item := <-resultsCh:
			inFlight--

			p := item.provider
			root := item.root
			res := item.result

			pipeStats.mu.Lock()
			if res.Status != StatSkipped && res.Status != StatWaitCanceled {
				pipeStats.StageC.Executed++
			}

			switch res.Status {
			case StatSuccess:
				pipeStats.StageC.Success++
			case StatNoData:
				pipeStats.StageC.NoData++
			case StatPartial:
				pipeStats.StageC.Partial++
			case StatFailed:
				pipeStats.StageC.Failed++
			case StatSkipped, StatWaitCanceled:
				pipeStats.StageC.Skipped++
			}
			pipeStats.mu.Unlock()

			if len(res.Names) > 0 {
				inheritedSrc := rootProvenance[root.Domain]
				for _, d := range res.Names {
					ds.AddDomainSource(d, p.SourceBit(), inheritedSrc)
				}
			}

			if rootStates[root.Domain] != RootPending {
				if res.Status == StatSkipped || res.Status == StatWaitCanceled {
					providerUsed[p]--
				}
				continue
			}

			if res.Status == StatSkipped || res.Status == StatWaitCanceled {
				providerUsed[p]--
				rootSkipped[root.Domain] = true
				if res.Status == StatWaitCanceled && ctx.Err() != nil {
					markCanceled(root.Domain)
					continue
				}
			}

			switch res.Status {
			case StatSuccess, StatNoData, StatPartial:
				markCompleted(root.Domain)
				continue
			}

			nextP, blockedByCB := findNextProvider(root.Domain)

			if nextP == nil {
				if blockedByCB || rootSkipped[root.Domain] {
					markDeferred(root.Domain)
				} else {
					markLost(root.Domain)
				}
				continue
			}

			scheduled[root.Domain][nextP] = true
			providerUsed[nextP]++

			pipeStats.mu.Lock()
			pipeStats.StageC.Reassigned++
			pipeStats.mu.Unlock()

			jobQueues[nextP] <- RootJob{
				Root:   root,
				Ctx:    rootCtx[root.Domain],
				Cancel: rootCancel[root.Domain],
			}
			inFlight++
		}
	}

	for _, root := range roots {
		if cancel, ok := rootCancel[root.Domain]; ok {
			cancel()
		}
	}

	for _, p := range providers {
		close(jobQueues[p])
	}
	workerWG.Wait()
}

func (s *PipelineStats) SnapshotAndPrint(rtCaches *RuntimeCaches, cfg Config, clustered int, ds *DiscoveryState) {
	s.mu.Lock()
	pSampled := s.IPSampled
	pWithPTR := s.PTRFound
	qDNS := s.DNSQueries
	qDNSSuc := s.DNSSuccess
	qDNSFail := s.DNSFailed
	qNX := s.DNSNXDomain
	qNoV4 := s.DNSNoIPv4
	qTimeout := s.DNSTimeout
	qTemp := s.DNSTemporary
	qOther := s.DNSOtherErr
	qResolved := s.DNSResolvedIPs
	qTargetMatches := s.DNSTargetRangeMatches
	qTargetDomains := s.DNSTargetDomains
	qValidPairs := s.DNSValidPairs

	pTCP := s.TCPConnected
	pTLS := s.TLSHandshake
	pH2 := s.H2ProtocolOK
	pH2Head := s.H2HeadersOK
	pStatus := s.H2StatusOK
	pFinal := s.CandidatesAccepted
	pReality := s.RealityFeasibleCandidates
	pLowScore := s.LowScoreCandidates

	localStats := make(map[string]ProviderStats)
	for k, v := range s.ProviderStats {
		localStats[k] = *v
	}
	stageC := s.StageC
	allocStats := s.Alloc
	s.mu.Unlock()

	ds.mu.RLock()
	droppedGlobal := ds.droppedDomainsByGlobalLimit
	droppedPairs := ds.droppedValidPairs
	ds.mu.RUnlock()

	fmt.Println("\n===================================================================================================================")
	fmt.Println("                                   ТЕЛЕМЕТРИЯ СКАНИРОВАНИЯ (PIPELINE STATS)")
	fmt.Println("===================================================================================================================")
	fmt.Printf("[*] IP отобрано для пула:      %d\n", pSampled)
	fmt.Printf("[*] IP с чистым PTR (Hosts):   %d\n", pWithPTR)
	rtCaches.DNSStatsMu.Lock()
	ptrSystem := rtCaches.PTRSystemFallbacks
	ptrDoHFallbacks := rtCaches.PTRDoHFallbacks
	dnsDoH := rtCaches.DNSDoHFallbacks
	dnsSystem := rtCaches.DNSSystemFallbacks
	ptrNegative := rtCaches.PTRNegativeResponses
	rtCaches.DNSStatsMu.Unlock()
	s.mu.Lock()
	s.PTRSystemFallbacks = ptrSystem
	s.PTRDoHFallbacks = ptrDoHFallbacks
	s.PTRNegativeResponses = ptrNegative
	s.PTRFound = pWithPTR
	s.mu.Unlock()
	fmt.Printf("[*] PTR system fallback:         %d\n", ptrSystem)
	fmt.Printf("[*] PTR DoH fallback:            %d\n", ptrDoHFallbacks)
	fmt.Printf("[*] DNS A DoH fallback:          %d\n", dnsDoH)
	fmt.Printf("[*] DNS A system fallback:       %d\n", dnsSystem)
	fmt.Printf("[*] PTR NXDOMAIN responses:      %d\n\n", ptrNegative)

	rtCaches.DNSStatsMu.Lock()
	ptrDoH := 0
	for _, st := range rtCaches.DNSResolverStats {
		if st != nil {
			ptrDoH += 0
		}
	}
	rtCaches.DNSStatsMu.Unlock()
	_ = ptrDoH

	if droppedGlobal > 0 {
		fmt.Printf("[!] Доменов отброшено глобальным лимитом (MaxDiscoveredDomains=%d): %d\n", MaxDiscoveredDomains, droppedGlobal)
	}

	fmt.Printf("[*] STAGE C: Domain OSINT Pipeline Stats:\n")
	fmt.Printf("    Total Roots:           %d\n", stageC.TotalRoots)
	fmt.Printf("    Assigned (Primary+Ov): %d\n", stageC.Assigned)
	fmt.Printf("    Completed (Unique):    %d\n", stageC.CompletedRoots)
	fmt.Printf("    Deferred (CB Open):    %d\n", stageC.DeferredRoots)
	fmt.Printf("    Lost (Exhausted):      %d\n", stageC.LostRoots)
	fmt.Printf("    Canceled (Timeout):    %d\n", stageC.CanceledRoots)
	fmt.Printf("    Executed Calls:        %d\n", stageC.Executed)
	fmt.Printf("    Success:               %d\n", stageC.Success)
	fmt.Printf("    NoData:                %d\n", stageC.NoData)
	fmt.Printf("    Partial:               %d\n", stageC.Partial)
	fmt.Printf("    Failed:                %d\n", stageC.Failed)
	fmt.Printf("    Skipped (CB/Rate):     %d\n", stageC.Skipped)
	fmt.Printf("    Reassigned to next:    %d\n", stageC.Reassigned)

	fmt.Println("\nSNI/Hostname Discovery Providers:")
	categories := map[DiscoveryCategory][]string{}
	for name, ps := range localStats {
		cat := ps.Category
		if cat == "" {
			cat = DiscoveryCategory("Unknown")
		}
		categories[cat] = append(categories[cat], name)
	}
	catNames := make([]string, 0, len(categories))
	for c := range categories {
		catNames = append(catNames, string(c))
	}
	sort.Strings(catNames)
	for _, catStr := range catNames {
		cat := DiscoveryCategory(catStr)
		names := categories[cat]
		fmt.Printf("  [%s]\n", cat)
		sort.Strings(names)
		for _, name := range names {
			p := localStats[name]
			primAlloc := allocStats.PrimaryAssignments[name]
			ovAlloc := allocStats.OverlapAssignments[name]
			fmt.Printf("    %-20s : Roots: %d (prim:%d ov:%d) | Попытки: %d (Успех: %d, NoData: %d, Част: %d, Ошиб: %d, Cancel: %d) -> Raw: %d (Уник: %d, Невалид: %d, Лимит: %d, Accept: %d)",
				name, primAlloc+ovAlloc, primAlloc, ovAlloc, p.Attempts, p.Success, p.NoData, p.Partial, p.Failed, p.WaitCanceled, p.RawNames, p.UniqueNames, p.InvalidNames, p.LimitedNames, p.AcceptedNames)
			if p.LastStatus != 0 {
				fmt.Printf(" | HTTP=%d", p.LastStatus)
			}
			if p.LastError != "" {
				fmt.Printf(" | err=%s", p.LastError)
			}
			fmt.Println()
		}
	}

	fmt.Printf("\n[*] ECS: %s/%d\n", cfg.ECSIP, cfg.ECSPrefix)
	fmt.Printf("[*] Raw UDP DNS pool: %s\n", strings.Join(cfg.DNSResolvers, ", "))
	fmt.Printf("[*] Logical DNS Lookups:       %d (Успех: %d, Ошибок: %d)\n", qDNS, qDNSSuc, qDNSFail)
	fmt.Printf("    Детали DNS успехов:        Resolved IPs: %d, NXDOMAIN: %d, NoIPv4: %d\n", qResolved, qNX, qNoV4)
	fmt.Printf("    Детали DNS ошибок:         Timeout: %d, Temporary: %d, Other: %d\n", qTimeout, qTemp, qOther)
	fmt.Printf("[*] Target Range IP Matches:   %d\n", qTargetMatches)
	fmt.Printf("[*] DNS доменов с Target IP:   %d\n", qTargetDomains)
	fmt.Printf("[*] Подтверждено DNS-пар:      %d\n", qValidPairs)
	if droppedPairs > 0 {
		fmt.Printf("[!] DNS-пар отброшено лимитом (LimitValidPairs=%d): %d\n", LimitValidPairs, droppedPairs)
	}

	fmt.Printf("\n[*] Анализ Stage E (Строгая Воронка):\n")
	fmt.Printf("    1. Целей на входе (DNS):       %d\n", qValidPairs)
	fmt.Printf("    2. Успешный TCP коннект:       %d (Потери: Timeouts=%d, Refused=%d, Other=%d)\n", pTCP, s.TCPTimeouts, s.TCPRefused, s.TCPOtherErrs)
	fmt.Printf("    3. Успешный TLS хэндшейк:      %d (Потери: Timeouts=%d, HandshakeFail=%d, UnrecName=%d, ConnReset=%d, EOF=%d, NoCert=%d, CertFail=%d, Other=%d)\n",
		pTLS, s.TLSTimeouts, s.TLSHandshakeFailure, s.TLSUnrecognizedName, s.TLSConnectionReset, s.TLSEOF, s.NoPeerCertificates, s.TLSValidationFailures, s.TLSOtherErrs)
	fmt.Printf("    4. Подтверждён H2 протокол:    %d (Потери: TimeoutNoFrames=%d, ConnReset=%d, BrokenPipe=%d, BadRequest/HTTP1=%d, GoAway=%d, EOF=%d, TLSAlerts=%d, Other=%d)\n",
		pH2, s.H2TimeoutNoFrames, s.H2ConnectionReset, s.H2BrokenPipe, s.H2BadRequest, s.H2GoAway, s.H2EOF, s.H2TLSAlerts, s.H2OtherErrs)
	fmt.Printf("    5. Получены H2 Headers:        %d (Потери: TimeoutsNoHeaders=%d, HPACK_Err=%d)\n", pH2Head, s.H2Timeouts, s.H2HPACKErrors)
	fmt.Printf("    6. Валидный HTTP Status:       %d (Потери: Invalid/Zero Status=%d)\n", pStatus, s.H2InvalidStatus)
	fmt.Printf("    7. Финальные Кандидаты:        %d (Score gate: отключён, LowScore=%d)\n", pFinal, pLowScore)
	fmt.Printf("    8. После кластеризации по IP:  %d (оставлен лучший SNI на IP)\n", clustered)
	fmt.Printf("    Reality-feasible из принятых:      %d\n", pReality)
	fmt.Printf("    H2 причины Other: InvalidFrame=%d, BadContinuation=%d, HPACK=%d, MissingSettings=%d, HeadersWithoutStatus=%d\n", s.H2InvalidFrame, s.H2BadContinuation, s.H2HPACKDecode, s.H2MissingSettings, s.H2HeadersWithoutStatus)
	fmt.Printf("       Важно: кластеризация по IP выполняется ПОСЛЕ этого этапа и не считается отклонением.\n")
	fmt.Printf("\n    * Инфо: H2 целей без ALPN 'h2': %d\n", s.H2NoALPN)
	fmt.Printf("    * Уникальных IP-кластеров:    %d (дедупликация финального списка по IP)\n", clustered)

	fmt.Printf("\n[*] DNS resolver telemetry:\n")
	rtCaches.DNSStatsMu.Lock()
	for _, resolver := range cfg.DNSResolvers {
		stat := rtCaches.DNSResolverStats[resolver]
		if stat == nil {
			continue
		}
		fmt.Printf("    %-15s attempts=%d answers=%d ipv4=%d nxdomain=%d failures=%d timeouts=%d\n",
			resolver, stat.Attempts, stat.Answers, stat.IPv4s, stat.NXDomain, stat.Failures, stat.Timeouts)
	}
	rtCaches.DNSStatsMu.Unlock()
}

// ================= DB & IP HELPERS =================

// ================= CIDR & SAMPLING =================
type ipRange struct{ start, end uint64 }

func MergeCIDRs(cidrs []string) []ipRange {
	var ranges []ipRange
	for _, c := range cidrs {
		_, ipnet, err := net.ParseCIDR(c)
		if err != nil || ipnet.Mask == nil {
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
		ranges = append(ranges, ipRange{startInt, startInt + count - 1})
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
	case maxIPs < -1:
		return nil
	case maxIPs == -1:
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
	if sampleSize > LimitMaxIPs {
		sampleSize = LimitMaxIPs
	}
	if sampleSize == 0 {
		return nil
	}
	rng := rand.New(rand.NewSource(seed))
	currIdx := rng.Uint64() % totalIPs
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
	for i := uint64(0); i < sampleSize; i++ {
		offset := currIdx
		for _, b := range blocks {
			count := b.end - b.start + 1
			if offset < count {
				ip := make(net.IP, 4)
				binary.BigEndian.PutUint32(ip, uint32(b.start+offset))
				result = append(result, ip.String())
				break
			}
			offset -= count
		}
		currIdx = (currIdx + step) % totalIPs
	}
	return result
}

func ipInRanges(ipStr string, ranges []ipRange) bool {
	parsed := net.ParseIP(ipStr)
	if parsed == nil {
		return false
	}
	ip4 := parsed.To4()
	if ip4 == nil {
		return false
	}
	val := uint64(binary.BigEndian.Uint32(ip4))
	for _, r := range ranges {
		if val >= r.start && val <= r.end {
			return true
		}
	}
	return false
}

func reverseIPv4(ip string) (string, error) {
	parsed := net.ParseIP(ip)
	if parsed == nil {
		return "", fmt.Errorf("invalid IP")
	}
	parsed = parsed.To4()
	if parsed == nil {
		return "", fmt.Errorf("not IPv4")
	}
	return fmt.Sprintf("%d.%d.%d.%d.in-addr.arpa.", parsed[3], parsed[2], parsed[1], parsed[0]), nil
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

func resolveIPv4Cached(ctx context.Context, domain string, rtCaches *RuntimeCaches, cfg Config) ([]string, error) {
	domain = CleanDomain(domain)
	if domain == "" {
		return nil, fmt.Errorf("invalid domain")
	}
	cacheKey := fmt.Sprintf("%s|ecs=%s/%d|dns=%s",
		domain, cfg.ECSIP, cfg.ECSPrefix, strings.Join(cfg.DNSResolvers, ","))

	v, err, _ := rtCaches.DNSGroup.Do(cacheKey, func() (interface{}, error) {
		if cached, ok := rtCaches.DNSCache.Get(cacheKey); ok {
			if cached.NXDomain {
				return nil, ErrDNSNXDomain
			}
			return cached.IPs, nil
		}

		ips, err := resolveHostECS(
			ctx,
			domain,
			cfg.ECSIP,
			cfg.ECSPrefix,
			cfg.DNSResolvers,
			time.Duration(cfg.DNSQueryTimeoutMs)*time.Millisecond,
			rtCaches,
		)
		if err != nil {
			if errors.Is(err, ErrDNSNXDomain) {
				rtCaches.DNSCache.Put(cacheKey, &DNSCacheEntry{NXDomain: true}, 10*time.Second)
			}
			return nil, err
		}

		var valid []string
		for _, ip := range ips {
			if net.ParseIP(ip).To4() != nil {
				valid = append(valid, ip)
			}
		}
		rtCaches.DNSCache.Put(cacheKey, &DNSCacheEntry{IPs: valid}, 10*time.Second)
		return valid, nil
	})
	if err != nil {
		return nil, err
	}
	return v.([]string), nil
}

func buildH2HeadersEncoder(sni string) []byte {
	var payload []byte
	payload = append(payload, 0x82, 0x87, 0x84)
	sniBytes := []byte(sni)
	payload = append(payload, 0x01, byte(len(sniBytes)))
	payload = append(payload, sniBytes...)
	ua := []byte("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/151.0.0.0 Safari/537.36")
	payload = append(payload, 0x0F, 0x2B, byte(len(ua)))
	payload = append(payload, ua...)
	return payload
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

func parseResponseHeaders(cand *Candidate, headers []hpack.HeaderField) {
	weakCount := 0
	hasStatus := false

	for _, h := range headers {
		hName := strings.ToLower(strings.TrimSpace(h.Name))

		if hName == ":status" {
			if n, err := strconv.Atoi(strings.TrimSpace(h.Value)); err == nil && n > 0 {
				cand.HTTPStatus = n
			}
			hasStatus = true
			continue
		}

		hValLower := strings.ToLower(h.Value)
		switch hName {
		case "server":
			cand.Server = h.Value
			for _, cdn := range cdnStrong {
				if strings.Contains(hValLower, cdn) {
					cand.CDNStatus = CDNConfirmed
					cand.CDNProvider = cdn
				}
			}
		case "content-type":
			cand.ContentType = h.Value
		case "location":
			cand.Location = h.Value
		case "cf-ray":
			cand.CDNStatus = CDNConfirmed
			cand.CDNProvider = "cloudflare"
		}

		if strings.HasPrefix(hName, "x-amz-cf-") ||
			strings.HasPrefix(hName, "x-sucuri-") ||
			strings.HasPrefix(hName, "x-akamai-") {
			cand.CDNStatus = CDNConfirmed
			if cand.CDNProvider == "" {
				cand.CDNProvider = "headers"
			}
		}

		for _, cdnH := range cdnWeak {
			if hName == cdnH {
				weakCount++
			}
		}
	}

	if !hasStatus {
		cand.MissingStatus = true
	}

	if cand.CDNStatus == CDNStatusUnknown && weakCount > 0 {
		cand.CDNStatus = CDNLikely
	}

	cand.ResponseHeadersParsed = true
}

func parseTrailers(cand *Candidate, headers []hpack.HeaderField) {
	cand.ResponseTrailersSeen = true
}

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
	if e == nil || e.Err == nil {
		return ""
	}
	return e.Err.Error()
}

func ProbeH2(ctx context.Context, ip, sni string, ev Evidence, cfg Config) (*Candidate, *ProbeError) {
	cand := &Candidate{
		IP:            ip,
		SNI:           sni,
		Evidence:      ev,
		DomainQuality: classifyDomainQuality(sni),
		CDNStatus:     CDNStatusUnknown,
		HTTPStatus:    0,
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
		NextProtos:         []string{"h2", "http/1.1"},
		MinVersion:         tls.VersionTLS13,
		MaxVersion:         tls.VersionTLS13,
	}, utls.HelloChrome_Auto)

	uConn.SetDeadline(time.Now().Add(time.Duration(cfg.TLSTimeoutMs) * time.Millisecond))
	if err := uConn.HandshakeContext(ctx); err != nil {
		return cand, &ProbeError{Stage: ProbeStageTLS, Err: err}
	}
	cand.Timings.TLS = time.Since(t1)
	uConn.SetDeadline(time.Time{})

	state := uConn.ConnectionState()

	// utls.ConnectionState does not expose the negotiated TLS key-share/curve.
	// Keep this explicit rather than guessing from the ClientHello.
	cand.TLSCurve = "unavailable (utls)"
	cand.X25519 = false

	if state.Version != tls.VersionTLS13 {
		return cand, &ProbeError{
			Stage: ProbeStageTLS,
			Err:   fmt.Errorf("unexpected TLS version: 0x%x", state.Version),
		}
	}
	cand.TLS13 = true

	if state.NegotiatedProtocol == "h2" {
		cand.ALPN = "h2"
	} else if state.NegotiatedProtocol == "" {
		cand.ALPN = "no ALPN"
	} else {
		cand.ALPN = state.NegotiatedProtocol
	}

	if len(state.PeerCertificates) == 0 {
		return cand, &ProbeError{Stage: ProbeStageTLSValidation, Err: fmt.Errorf("no peer certificates provided")}
	}

	cert := state.PeerCertificates[0]
	cand.CertIssuer = cert.Issuer.CommonName
	if cand.CertIssuer == "" && len(cert.Issuer.Organization) > 0 {
		cand.CertIssuer = cert.Issuer.Organization[0]
	}
	cand.CertSubject = cert.Subject.CommonName
	cand.CertSANCount = len(cert.DNSNames) + len(cert.IPAddresses)

	now := time.Now()
	cand.CertValidTime = now.After(cert.NotBefore) && now.Before(cert.NotAfter)
	cand.CertExpiry = cert.NotAfter

	opts := x509.VerifyOptions{
		DNSName:       sni,
		Roots:         nil,
		Intermediates: x509.NewCertPool(),
	}
	for _, c := range state.PeerCertificates[1:] {
		opts.Intermediates.AddCert(c)
	}

	if _, err := cert.Verify(opts); err == nil {
		cand.CertSNIMatch = true
		cand.CertChainValid = true
	} else {
		cand.CertChainValid = false
		cand.CertSNIMatch = (cert.VerifyHostname(sni) == nil)
	}

	wTo := time.Duration(cfg.H2WriteTimeoutMs) * time.Millisecond

	if err := writeH2(uConn, []byte("PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"), wTo); err != nil {
		return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
	}
	if err := writeH2(uConn, buildH2Frame(FrameSettings, 0, 0, nil), wTo); err != nil {
		return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
	}
	if err := writeH2(uConn, buildH2Frame(FrameHeaders, FlagEndHeaders|FlagEndStream, 1, buildH2HeadersEncoder(sni)), wTo); err != nil {
		return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
	}

	requestSent := time.Now()
	uConn.SetReadDeadline(time.Now().Add(time.Duration(cfg.H2ReadTimeoutMs) * time.Millisecond))

	const maxInboundFrameSize = uint32(16384)
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
			break ReadLoop
		}
		n, err := uConn.Read(buf)
		if n > 0 {
			recvBuf.Write(buf[:n])
		}

		for recvBuf.Len() >= 9 {
			data := recvBuf.Bytes()
			length := uint32(data[0])<<16 | uint32(data[1])<<8 | uint32(data[2])
			if length > maxInboundFrameSize {
				break ReadLoop
			}
			if uint32(recvBuf.Len()) < 9+length {
				break
			}
			if !firstFrameSeen {
				cand.Timings.H2FirstFrame = time.Since(requestSent)
				firstFrameSeen = true
			}

			frameType, flags := data[3], data[4]
			streamID := binary.BigEndian.Uint32(data[5:9]) & 0x7FFFFFFF
			payload := data[9 : 9+length]
			recvBuf.Next(int(9 + length))

			if expectingContinuation && frameType != FrameContinuation {
				return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid H2: expected CONTINUATION, got frame type %d", frameType)}
			}

			switch frameType {
			case FrameSettings:
				if length%6 != 0 {
					continue
				}
				if flags&FlagAck != 0 {
					cand.H2SettingsAckReceived = true
					cand.SettingsAckCount++
					break
				}
				cand.SettingsFramesCount++
				var prof PeerSettingsProfile
				if cand.H2SettingsReceived {
					prof = cand.LatestPeerSettings
				}
				for i := 0; i+6 <= int(length); i += 6 {
					id := binary.BigEndian.Uint16(payload[i : i+2])
					val := binary.BigEndian.Uint32(payload[i+2 : i+6])
					switch id {
					case 1:
						prof.HeaderTableSize = val
						prof.HasHeaderTableSize = true
						decoder.SetMaxDynamicTableSize(val)
					case 3:
						prof.MaxConcurrentStreams = val
						prof.HasMaxConcurrentStreams = true
					case 4:
						prof.InitialWindowSize = val
						prof.HasInitialWindowSize = true
					case 5:
						prof.MaxFrameSize = val
						prof.HasMaxFrameSize = true
					case 6:
						prof.MaxHeaderListSize = val
						prof.HasMaxHeaderListSize = true
					}
				}
				if !cand.H2SettingsReceived {
					cand.InitialPeerSettings = prof
					cand.LatestPeerSettings = prof
					cand.H2SettingsReceived = true
					cand.H2ProtocolConfirmed = true
				} else {
					if prof != cand.LatestPeerSettings {
						cand.SettingsChanges++
					}
					cand.LatestPeerSettings = prof
				}
				_ = writeH2(uConn, buildH2Frame(FrameSettings, FlagAck, 0, nil), wTo)
				cand.H2SettingsAckSent = true

			case FrameHeaders:
				if streamID == 1 {
					isTrailers := cand.EndStreamSeen
					if (flags & FlagEndStream) != 0 {
						cand.EndStreamSeen = true
					}
					actualPayload := payload
					padLen := 0
					if flags&FlagPadded != 0 && len(actualPayload) > 0 {
						padLen = int(actualPayload[0])
						actualPayload = actualPayload[1:]
					}
					if flags&FlagPriority != 0 && len(actualPayload) >= 5 {
						actualPayload = actualPayload[5:]
					}
					if padLen > len(actualPayload) {
						padLen = len(actualPayload)
					}
					actualPayload = actualPayload[:len(actualPayload)-padLen]

					headerBlocks.Write(actualPayload)
					if (flags & FlagEndHeaders) == 0 {
						expectingContinuation = true
						activeStreamID = streamID
					} else {
						expectingContinuation = false
						headers, errDecode := decoder.DecodeFull(headerBlocks.Bytes())
						if errDecode != nil {
							cand.HPACKErrors = true
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("HPACK decode: %w", errDecode)}
						}

						if !cand.ResponseHeadersParsed && !isTrailers {
							parseResponseHeaders(cand, headers)
							headerBlocks.Reset()

							cand.Timings.H2Headers = time.Since(requestSent)
							cand.H2HeadersReceived = true

							break ReadLoop
						} else if isTrailers {
							parseTrailers(cand, headers)
						}
						headerBlocks.Reset()
					}
				}
			case FrameContinuation:
				if !expectingContinuation || streamID != activeStreamID {
					continue
				}
				headerBlocks.Write(payload)
				if (flags & FlagEndHeaders) != 0 {
					expectingContinuation = false
					headers, errDecode := decoder.DecodeFull(headerBlocks.Bytes())
					if errDecode != nil {
						cand.HPACKErrors = true
						return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("HPACK decode: %w", errDecode)}
					}

					if !cand.ResponseHeadersParsed {
						parseResponseHeaders(cand, headers)
						headerBlocks.Reset()

						cand.Timings.H2Headers = time.Since(requestSent)
						cand.H2HeadersReceived = true

						break ReadLoop
					} else {
						parseTrailers(cand, headers)
					}
					headerBlocks.Reset()
				}
			case FrameData:
				if streamID == 1 {
					cand.H2DataFrames++
					if (flags & FlagEndStream) != 0 {
						cand.EndStreamSeen = true
					}
					actualPayload := payload
					padLen := 0
					if flags&FlagPadded != 0 && len(actualPayload) > 0 {
						padLen = int(actualPayload[0])
						actualPayload = actualPayload[1:]
					}
					if padLen > len(actualPayload) {
						padLen = len(actualPayload)
					}
					actualPayload = actualPayload[:len(actualPayload)-padLen]

					cand.BodyBytes += len(actualPayload)
					inc := length
					if inc > 0 {
						_ = writeH2(uConn, buildWindowUpdateFrame(1, inc), wTo)
						_ = writeH2(uConn, buildWindowUpdateFrame(0, inc), wTo)
					}
				}
			case FrameRSTStream:
				if streamID == 1 {
					cand.StreamReset = true
					break ReadLoop
				}
			case FrameGoAway:
				cand.GoAwaySeen = true
			}

			if cand.H2ProtocolConfirmed && cand.H2HeadersReceived && (cand.BodyBytes > 0 || cand.Server != "" || cand.EndStreamSeen) {
				break ReadLoop
			}
		}

		if err != nil {
			if cand.H2ProtocolConfirmed {
				cand.ReadTimeout = true
				break ReadLoop
			}
			return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
		}
	}

	if !cand.H2SettingsReceived || !cand.H2ProtocolConfirmed {
		return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("no valid H2 SETTINGS exchange received")}
	}

	cand.RealityFeasible = cand.TLS13 && cand.ALPN == "h2" && cand.CertSNIMatch && cand.CertValidTime

	return cand, nil
}

// ================= SCORING & ENRICHMENT =================

func scoreH2Profile(c *Candidate) float64 {
	score := 0.0
	if c.H2SettingsReceived {
		score += 5.0
	}
	prof := c.InitialPeerSettings
	if prof.HasMaxConcurrentStreams && prof.MaxConcurrentStreams > 0 && prof.MaxConcurrentStreams <= 1000 {
		score += 3.0
	}
	if prof.HasInitialWindowSize {
		switch {
		case prof.InitialWindowSize == 65535:
			score += 1.0
		case prof.InitialWindowSize > 65535:
			score += 3.0
		}
	}
	if prof.HasMaxFrameSize {
		switch {
		case prof.MaxFrameSize == 16384:
			score += 1.0
		case prof.MaxFrameSize > 16384:
			score += 3.0
		}
	}
	if c.H2DataFrames > 0 {
		score += 3.0
	}
	if c.BodyBytes >= 1024 {
		score += 1.0
	}
	if c.EndStreamSeen {
		score += 2.0
	}
	return math.Min(score, 20.0)
}

func validateAndEnrich(cand *Candidate, cfg Config, pipeStats *PipelineStats) bool {
	if !cand.H2ProtocolConfirmed {
		return false
	}

	rs := RealityScore{}

	if cand.TLS13 {
		rs.TLSQuality += 10.0
	}
	if cand.ALPN == "h2" {
		rs.TLSQuality += 10.0
	}

	if cand.CertValidTime {
		rs.Certificate += 5.0
	}
	if cand.CertSNIMatch {
		rs.Certificate += 10.0
	}
	if cand.CertChainValid {
		rs.Certificate += 5.0
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
			rs.HTTPBehavior = 5
		} else if cand.HTTPStatus >= 500 {
			rs.HTTPBehavior = -5
		}
	}

	discovery := 0.0
	scoreDirect := func(src DomainSource, pts float64) {
		if cand.Evidence.Direct.Has(src) {
			discovery += pts
		} else if cand.Evidence.Inherited.Has(src) {
			discovery += pts / 2.0
		}
	}
	scoreDirect(SourcePTR, 3.0)
	scoreDirect(SourceHackerTarget, 3.0)
	scoreDirect(SourceShodan, 3.0)
	scoreDirect(SourceVirusTotalIP, 2.0)
	scoreDirect(SourceVirusTotalDomain, 2.0)
	scoreDirect(SourceURLScan, 2.0)
	scoreDirect(SourceCRTSh, 2.0)
	scoreDirect(SourceCertSpotter, 2.0)
	scoreDirect(SourceAlienVault, 1.0)
	scoreDirect(SourceWayback, 1.0)
	scoreDirect(SourceAnubis, 1.0)
	scoreDirect(SourceThreatMiner, 1.0)
	scoreDirect(SourceHTDomain, 1.0)
	scoreDirect(SourceChaos, 1.0)
	scoreDirect(SourceSeed, 1.0)

	combinedSources := cand.Evidence.Combined()
	diversity := 0
	if combinedSources.Has(SourcePTR) || combinedSources.Has(SourceHackerTarget) || combinedSources.Has(SourceShodan) {
		diversity++
	}
	if combinedSources.Has(SourceVirusTotalIP) || combinedSources.Has(SourceVirusTotalDomain) || combinedSources.Has(SourceURLScan) {
		diversity++
	}
	if combinedSources.Has(SourceCRTSh) || combinedSources.Has(SourceCertSpotter) {
		diversity++
	}
	if combinedSources.Has(SourceAlienVault) || combinedSources.Has(SourceWayback) || combinedSources.Has(SourceChaos) || combinedSources.Has(SourceAnubis) || combinedSources.Has(SourceThreatMiner) || combinedSources.Has(SourceHTDomain) {
		diversity++
	}
	if combinedSources.Has(SourceSeed) {
		diversity++
	}
	if diversity >= 2 {
		discovery += 2.0
	}
	if diversity >= 3 {
		discovery += 2.0
	}
	rs.DiscoveryScore = math.Min(discovery, 10.0)

	rtt := cand.Timings.TotalProbeLatency().Milliseconds()
	if rtt <= 50 {
		rs.Latency = 10
	} else if rtt <= 150 {
		rs.Latency = 7
	} else if rtt <= 300 {
		rs.Latency = 4
	} else {
		rs.Latency = 1
	}

	rs.Total = rs.TLSQuality + rs.Certificate + rs.H2Profile + rs.ServerProfile + rs.HTTPBehavior + rs.DiscoveryScore + rs.Latency

	scorePenalty := 0.0
	switch cand.DomainQuality {
	case "Numeric":
		scorePenalty = 30.0
	case "DynDNS":
		scorePenalty = 20.0
	case "JunkTLD":
		scorePenalty = 5.0
	}
	if cand.CDNStatus == CDNLikely {
		scorePenalty += 10.0
	}

	cand.RealityFeasible = cand.TLS13 && cand.ALPN == "h2" && cand.CertSNIMatch && cand.CertValidTime
	cand.RealityScore = rs
	cand.DomainPenalty = scorePenalty
	cand.Score = rs.Total - scorePenalty

	// A confirmed H2 response with a valid HTTP status is already a working
	// candidate. Score is for ranking only; it must never silently discard a
	// technically valid target. Low scores remain visible in telemetry.
	if cand.Score < 0 && pipeStats != nil {
		pipeStats.mu.Lock()
		pipeStats.LowScoreCandidates++
		pipeStats.mu.Unlock()
	}
	return true
}

func RunPipeline(ctx context.Context, cfg Config, sampledIPs []string, scanRanges []ipRange) []Candidate {
	httpClient := &http.Client{Timeout: 15 * time.Second}

	pipeStats := NewPipelineStats()
	pipeStats.mu.Lock()
	pipeStats.IPSampled = len(sampledIPs)
	pipeStats.mu.Unlock()

	ds := NewDiscoveryState()
	rtCaches := NewRuntimeCaches()

	for _, d := range cfg.Domains {
		if cleaned := CleanDomain(d); cleaned != "" {
			ds.AddDomainSource(cleaned, SourceSeed, 0)
		}
	}

	var extProviders []*ProviderRunner
	if !cfg.NoCT {
		extProviders = append(extProviders, NewRunner(&crtShProvider{}, ProviderConfig{Timeout: 6 * time.Second, MaxConcurrent: 1, MinInterval: 1 * time.Second, MaxNames: 1000, MaxRoots: 50, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&certSpotterProvider{}, ProviderConfig{Timeout: 5 * time.Second, MaxConcurrent: 2, MinInterval: 500 * time.Millisecond, MaxNames: 1000, MaxRoots: 100, MaxPages: 3}))
	}
	if !cfg.NoPassive {
		extProviders = append(extProviders, NewRunner(&alienVaultProvider{}, ProviderConfig{Timeout: 8 * time.Second, MaxConcurrent: 1, MinInterval: 1 * time.Second, MaxNames: 1000, MaxRoots: 150, MaxPages: 3}))
		extProviders = append(extProviders, NewRunner(&waybackProvider{}, ProviderConfig{Timeout: 7 * time.Second, MaxConcurrent: 3, MinInterval: 500 * time.Millisecond, MaxNames: 6000, MaxRoots: 100, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&anubisProvider{}, ProviderConfig{Timeout: 6 * time.Second, MaxConcurrent: 2, MinInterval: 400 * time.Millisecond, MaxNames: 1500, MaxRoots: 150, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&threatMinerProvider{}, ProviderConfig{Timeout: 5 * time.Second, MaxConcurrent: 2, MinInterval: 1 * time.Second, MaxNames: 1000, MaxRoots: 80, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&hackerTargetHostSearchProvider{}, ProviderConfig{Timeout: 6 * time.Second, MaxConcurrent: 1, MinInterval: 1 * time.Second, MaxNames: 1000, MaxRoots: 50, MaxPages: 1}))
	}
	if !cfg.NoReverseIP {
		extProviders = append(extProviders, NewRunner(&hackerTargetProvider{}, ProviderConfig{Timeout: 6 * time.Second, MaxConcurrent: 1, MinInterval: 1 * time.Second, MaxNames: 1000, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&shodanInternetDBProvider{}, ProviderConfig{Timeout: 6 * time.Second, MaxConcurrent: 10, MinInterval: 50 * time.Millisecond, MaxNames: 1000, MaxPages: 1}))
	}
	if cfg.VTKey != "" {
		extProviders = append(extProviders, NewRunner(&vtDomainProvider{Key: cfg.VTKey}, ProviderConfig{Timeout: 8 * time.Second, MaxConcurrent: 1, MinInterval: 15 * time.Second, MaxNames: 1500, MaxRoots: 75, MaxPages: 2}))
		extProviders = append(extProviders, NewRunner(&vtIPProvider{Key: cfg.VTKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MinInterval: 1 * time.Second, MaxNames: 2000, MaxPages: 3}))
	}
	if cfg.URLScanKey != "" {
		extProviders = append(extProviders, NewRunner(&urlScanDomainProvider{Key: cfg.URLScanKey}, ProviderConfig{Timeout: 8 * time.Second, MaxConcurrent: 1, MaxNames: 8000, MaxRoots: 100, MaxPages: 3}))
		extProviders = append(extProviders, NewRunner(&urlScanIPProvider{Key: cfg.URLScanKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MaxNames: 10000, MaxPages: 5}))
	}
	if cfg.ChaosKey != "" {
		extProviders = append(extProviders, NewRunner(&chaosProvider{Key: cfg.ChaosKey}, ProviderConfig{Timeout: 8 * time.Second, MaxConcurrent: 2, MinInterval: 400 * time.Millisecond, MaxNames: 750, MaxRoots: 100, MaxPages: 1}))
	}

	var ipProviders []*ProviderRunner
	var domainProviders []*ProviderRunner
	for _, p := range extProviders {
		if p.QueryType() == QueryIP {
			ipProviders = append(ipProviders, p)
		} else {
			domainProviders = append(domainProviders, p)
		}
	}

	fmt.Printf("[*] STAGE A: Reverse-IP OSINT & PTR Gathering...\n")
	gA, gCtxA := errgroup.WithContext(ctx)

	if !cfg.NoPTR {
		gA.Go(func() error {
			ptrJobs := make(chan string)
			var ptrG errgroup.Group
			for i := 0; i < cfg.Workers; i++ {
				ptrG.Go(func() error {
					for {
						select {
						case <-gCtxA.Done():
							return gCtxA.Err()
						case ip, ok := <-ptrJobs:
							if !ok {
								return nil
							}
							names, err := resolvePTRRaw(gCtxA, ip, cfg.DNSResolvers, PTRQueryTimeoutDefault, rtCaches)
							if err == nil && len(names) > 0 {
								for _, n := range names {
									ds.AddPairSource(ip, n, SourcePTR)
								}
								pipeStats.mu.Lock()
								pipeStats.IPWithPTR++
								pipeStats.PTRFound++
								pipeStats.mu.Unlock()
							}
						}
					}
				})
			}
			ptrG.Go(func() error {
				defer close(ptrJobs)
				for _, ip := range sampledIPs {
					select {
					case <-gCtxA.Done():
						return gCtxA.Err()
					case ptrJobs <- ip:
					}
				}
				return nil
			})
			return ptrG.Wait()
		})
	}

	for idx, p := range ipProviders {
		p := p
		limitIP := cfg.IPOSINTLimit
		if limitIP <= 0 {
			limitIP = len(sampledIPs)
		}
		ipSlice := sampleForProvider(sampledIPs, limitIP, cfg.Seed, idx)

		gA.Go(func() error {
			return runProviderJobs(gCtxA, p, ipSlice, httpClient, pipeStats, rtCaches, func(q string, res []string) {
				for _, d := range res {
					ds.AddPairSource(q, d, p.SourceBit())
				}
			})
		})
	}
	if err := gA.Wait(); err != nil || ctx.Err() != nil {
		fmt.Println("[-] Выполнение прервано (Stage A).")
		return nil
	}

	fmt.Printf("[*] STAGE B: Normalizing Domains & Ranking Roots...\n")
	rootProvenance := make(map[string]DomainSource)

	ds.mu.RLock()
	for d, ev := range ds.domainEvidence {
		if r := GetRootDomain(d); r != "" {
			rootProvenance[r] |= ev.Direct
		}
	}
	for key, ev := range ds.pairEvidence {
		parts := strings.Split(key, "\x00")
		if len(parts) == 2 {
			if r := GetRootDomain(parts[1]); r != "" {
				rootProvenance[r] |= ev.Direct
			}
		}
	}
	ds.mu.RUnlock()

	var rootsRanked []RootCandidate
	for r, src := range rootProvenance {
		rootsRanked = append(rootsRanked, RootCandidate{Domain: r, Source: src, Score: rankRootSources(src)})
	}

	sort.SliceStable(rootsRanked, func(i, j int) bool {
		if rootsRanked[i].Score != rootsRanked[j].Score {
			return rootsRanked[i].Score > rootsRanked[j].Score
		}
		return rootsRanked[i].Domain < rootsRanked[j].Domain
	})

	fmt.Printf("[*] STAGE C: Domain OSINT (Distributing %d Roots)...\n", len(rootsRanked))
	RunStageC(ctx, rootsRanked, domainProviders, cfg, httpClient, pipeStats, rtCaches, ds, rootProvenance)

	var allDomains []string
	ds.mu.RLock()
	for d := range ds.domainsToResolve {
		allDomains = append(allDomains, d)
	}
	ds.mu.RUnlock()

	var validPairs []TargetPair
	var pairSeen sync.Map

	if cfg.Mode == ModeDirect && cfg.DirectSNI != "" {
		sni := CleanDomain(cfg.DirectSNI)
		if sni != "" {
			for _, ip := range sampledIPs {
				key := ip + "\x00" + sni
				if _, loaded := pairSeen.LoadOrStore(key, true); !loaded {
					ds.mu.Lock()
					if len(validPairs) < LimitValidPairs {
						validPairs = append(validPairs, TargetPair{
							IP:       ip,
							SNI:      sni,
							Evidence: Evidence{Direct: SourceSeed},
						})
					} else {
						ds.droppedValidPairs++
					}
					ds.mu.Unlock()
				}
			}
		}
	}

	fmt.Printf("[*] STAGE D: DNS Validation (%d Domains)...\n", len(allDomains))
	var uniqueResolvedIPs sync.Map
	var uniqueTargetIPs sync.Map

	gD, gCtxD := errgroup.WithContext(ctx)
	gD.SetLimit(cfg.DNSWorkers)
	for _, dom := range allDomains {
		if cfg.Mode == ModeDirect && dom == CleanDomain(cfg.DirectSNI) {
			continue
		}
		dom := dom
		gD.Go(func() error {
			if gCtxD.Err() != nil {
				return gCtxD.Err()
			}
			pipeStats.mu.Lock()
			pipeStats.DNSQueries++
			pipeStats.mu.Unlock()

			ips, err := resolveIPv4Cached(gCtxD, dom, rtCaches, cfg)

			pipeStats.mu.Lock()
			if err != nil {
				if errors.Is(err, ErrDNSNXDomain) {
					pipeStats.DNSSuccess++
					pipeStats.DNSNXDomain++
				} else {
					pipeStats.DNSFailed++
					var dnsErr *net.DNSError
					if errors.Is(err, context.DeadlineExceeded) || os.IsTimeout(err) {
						pipeStats.DNSTimeout++
					} else if errors.As(err, &dnsErr) {
						if dnsErr.Timeout() {
							pipeStats.DNSTimeout++
						} else if dnsErr.Temporary() {
							pipeStats.DNSTemporary++
						} else {
							pipeStats.DNSOtherErr++
						}
					} else {
						pipeStats.DNSOtherErr++
					}
				}
				pipeStats.mu.Unlock()
				return nil
			}

			if len(ips) == 0 {
				pipeStats.DNSSuccess++
				pipeStats.DNSNoIPv4++
				pipeStats.mu.Unlock()
				return nil
			}

			pipeStats.DNSSuccess++
			pipeStats.DNSResolvedIPs += len(ips)
			pipeStats.mu.Unlock()

			matched := false
			for _, resolvedIP := range ips {
				uniqueResolvedIPs.Store(resolvedIP, struct{}{})

				if ipInRanges(resolvedIP, scanRanges) {
					uniqueTargetIPs.Store(resolvedIP, struct{}{})
					matched = true

					pipeStats.mu.Lock()
					pipeStats.DNSTargetRangeMatches++
					pipeStats.mu.Unlock()

					pairKey := resolvedIP + "\x00" + dom
					if _, loaded := pairSeen.LoadOrStore(pairKey, true); !loaded {
						ds.mu.Lock()
						if len(validPairs) < LimitValidPairs {
							evD := ds.domainEvidence[dom]
							evP := ds.pairEvidence[pairKey]
							finalEvidence := Evidence{
								Direct:    evD.Direct | evP.Direct,
								Inherited: evD.Inherited | evP.Inherited,
							}
							validPairs = append(validPairs, TargetPair{
								IP:       resolvedIP,
								SNI:      dom,
								Evidence: finalEvidence,
							})
						} else {
							ds.droppedValidPairs++
						}
						ds.mu.Unlock()
					}
				}
			}
			if matched {
				pipeStats.mu.Lock()
				pipeStats.DNSTargetDomains++
				pipeStats.mu.Unlock()
			}
			return nil
		})
	}
	if err := gD.Wait(); err != nil || ctx.Err() != nil {
		fmt.Println("[-] Выполнение прервано (Stage D).")
		return nil
	}

	uniqueResolvedCount := 0
	uniqueResolvedIPs.Range(func(k, v interface{}) bool {
		uniqueResolvedCount++
		return true
	})
	uniqueTargetCount := 0
	uniqueTargetIPs.Range(func(k, v interface{}) bool {
		uniqueTargetCount++
		return true
	})

	pipeStats.mu.Lock()
	pipeStats.DNSUniqueResolvedIPs = uniqueResolvedCount
	pipeStats.DNSUniqueTargetIPs = uniqueTargetCount
	pipeStats.DNSValidPairs = len(validPairs)
	fmt.Printf("[+] Stage D Завершён. Подтверждено DNS-пар (IP+SNI): %d\n", pipeStats.DNSValidPairs)
	pipeStats.mu.Unlock()

	if len(validPairs) == 0 {
		return nil
	}

	fmt.Printf("[*] STAGE E: Active HTTP/2 Scanning & TLS Enrichment (%d targets)...\n", len(validPairs))
	var candidates []Candidate
	var candMu sync.Mutex

	h2jobs := make(chan TargetPair, len(validPairs))
	var wgE sync.WaitGroup

	// Keep the tested minimum probe timeouts.
	if cfg.TCPTimeoutMs < 3000 {
		cfg.TCPTimeoutMs = 3000
	}
	if cfg.TLSTimeoutMs < 3000 {
		cfg.TLSTimeoutMs = 3000
	}

	for i := 0; i < cfg.Workers; i++ {
		wgE.Add(1)
		go func() {
			defer wgE.Done()
			for p := range h2jobs {
				if ctx.Err() != nil {
					return
				}

				cand, pErr := ProbeH2(ctx, p.IP, p.SNI, p.Evidence, cfg)

				pipeStats.mu.Lock()

				// 1. TCP
				if pErr != nil && pErr.Stage == ProbeStageTCP {
					errStr := pErr.Err.Error()
					if os.IsTimeout(pErr.Err) || strings.Contains(errStr, "deadline") || strings.Contains(errStr, "i/o timeout") {
						pipeStats.TCPTimeouts++
					} else if strings.Contains(strings.ToLower(errStr), "refused") {
						pipeStats.TCPRefused++
					} else {
						pipeStats.TCPOtherErrs++
					}
					pipeStats.mu.Unlock()
					continue
				}
				pipeStats.TCPConnected++

				// 2. TLS
				if pErr != nil && (pErr.Stage == ProbeStageTLS || pErr.Stage == ProbeStageTLSValidation) {
					errStr := pErr.Err.Error()
					if os.IsTimeout(pErr.Err) || strings.Contains(errStr, "deadline") || strings.Contains(errStr, "i/o timeout") {
						pipeStats.TLSTimeouts++
					} else if strings.Contains(strings.ToLower(errStr), "no peer certificates") {
						pipeStats.NoPeerCertificates++
					} else if strings.Contains(strings.ToLower(errStr), "handshake failure") {
						pipeStats.TLSHandshakeFailure++
					} else if strings.Contains(strings.ToLower(errStr), "unrecognized name") {
						pipeStats.TLSUnrecognizedName++
					} else if strings.Contains(strings.ToLower(errStr), "connection reset") {
						pipeStats.TLSConnectionReset++
					} else if errors.Is(pErr.Err, io.EOF) || strings.Contains(errStr, "EOF") {
						pipeStats.TLSEOF++
					} else if pErr.Stage == ProbeStageTLSValidation {
						pipeStats.TLSValidationFailures++
					} else {
						pipeStats.TLSOtherErrs++
					}
					pipeStats.mu.Unlock()
					continue
				}
				pipeStats.TLSHandshake++

				// 3. H2 is determined from actual HTTP/2 frames, not ALPN alone.
				if cand != nil && cand.ALPN != "h2" {
					pipeStats.H2NoALPN++
				}

				if pErr != nil {
					errStr := pErr.Err.Error()
					lowerErr := strings.ToLower(errStr)
					switch {
					case os.IsTimeout(pErr.Err) || strings.Contains(lowerErr, "deadline") || strings.Contains(lowerErr, "i/o timeout") || (cand != nil && cand.ReadTimeout):
						pipeStats.H2TimeoutNoFrames++
					case strings.Contains(lowerErr, "connection reset"):
						pipeStats.H2ConnectionReset++
					case strings.Contains(lowerErr, "broken pipe"):
						pipeStats.H2BrokenPipe++
					case strings.Contains(errStr, "400 Bad Request") || strings.Contains(errStr, "HTTP/1.1"):
						pipeStats.H2BadRequest++
					case cand != nil && cand.GoAwaySeen:
						pipeStats.H2GoAway++
					case errors.Is(pErr.Err, io.EOF) || strings.Contains(errStr, "EOF"):
						pipeStats.H2EOF++
					case strings.Contains(lowerErr, "tls:"):
						pipeStats.H2TLSAlerts++
					case strings.Contains(lowerErr, "expected continuation"):
						pipeStats.H2OtherErrs++
						pipeStats.H2BadContinuation++
					case strings.Contains(lowerErr, "invalid h2"):
						pipeStats.H2OtherErrs++
						pipeStats.H2InvalidFrame++
					case strings.Contains(lowerErr, "hpack decode") || strings.Contains(lowerErr, "hpack"):
						pipeStats.H2OtherErrs++
						pipeStats.H2HPACKDecode++
					default:
						pipeStats.H2OtherErrs++
					}
					pipeStats.mu.Unlock()
					continue
				}

				if cand == nil || !cand.H2ProtocolConfirmed {
					pipeStats.mu.Unlock()
					pipeStats.incH2Reason("missing-settings")
					continue
				}
				pipeStats.H2ProtocolOK++

				// 4. H2 Headers
				if !cand.H2HeadersReceived {
					if cand.ReadTimeout {
						pipeStats.H2Timeouts++
					} else if cand.HPACKErrors {
						pipeStats.H2HPACKErrors++
					} else {
						pipeStats.mu.Unlock()
						pipeStats.incH2Reason("headers-without-status")
						continue
					}
					pipeStats.mu.Unlock()
					continue
				}
				pipeStats.H2HeadersOK++

				// 5. HTTP status
				if cand.MissingStatus || cand.HTTPStatus <= 0 {
					pipeStats.H2InvalidStatus++
					pipeStats.mu.Unlock()
					continue
				}
				pipeStats.H2StatusOK++

				if cand.EndStreamSeen {
					pipeStats.EndStreamOK++
				}
				pipeStats.mu.Unlock()

				cand.Evidence = p.Evidence

				// 6. Enrichment + score
				if !validateAndEnrich(cand, cfg, pipeStats) {
					// validateAndEnrich currently rejects only structurally invalid
					// H2 candidates, which are already filtered above. Keep this guard
					// for future hard validation without using score as a gate.
					pipeStats.mu.Lock()
					pipeStats.ScoreRejected++
					pipeStats.mu.Unlock()
					continue
				}

				pipeStats.mu.Lock()
				pipeStats.CandidatesAccepted++
				pipeStats.mu.Unlock()

				candMu.Lock()
				candidates = append(candidates, *cand)
				candMu.Unlock()
			}
		}()
	}

	for _, p := range validPairs {
		h2jobs <- p
	}
	close(h2jobs)
	wgE.Wait()

	if ctx.Err() != nil {
		fmt.Println("[-] Выполнение прервано (Stage E).")
		return nil
	}

	ipClusters := make(map[string][]Candidate)
	for _, c := range candidates {
		ipClusters[c.IP] = append(ipClusters[c.IP], c)
	}

	// Technical eligibility always outranks the heuristic Score.
	// Score is intentionally only a tie-breaker among technically comparable
	// candidates; this prevents a high heuristic score from selecting an SNI
	// with an unsuitable certificate when another SNI on the same IP is
	// Reality-feasible.
	candidateLess := func(a, b Candidate) bool {
		boolRank := func(v bool) int {
			if v {
				return 1
			}
			return 0
		}

		if boolRank(a.RealityFeasible) != boolRank(b.RealityFeasible) {
			return boolRank(a.RealityFeasible) > boolRank(b.RealityFeasible)
		}
		if boolRank(a.CertSNIMatch) != boolRank(b.CertSNIMatch) {
			return boolRank(a.CertSNIMatch) > boolRank(b.CertSNIMatch)
		}
		if boolRank(a.CertValidTime) != boolRank(b.CertValidTime) {
			return boolRank(a.CertValidTime) > boolRank(b.CertValidTime)
		}
		if boolRank(a.H2ProtocolConfirmed) != boolRank(b.H2ProtocolConfirmed) {
			return boolRank(a.H2ProtocolConfirmed) > boolRank(b.H2ProtocolConfirmed)
		}
		if boolRank(a.H2HeadersReceived) != boolRank(b.H2HeadersReceived) {
			return boolRank(a.H2HeadersReceived) > boolRank(b.H2HeadersReceived)
		}

		statusClass := func(status int) int {
			switch {
			case status >= 200 && status < 300:
				return 3
			case status >= 300 && status < 400:
				return 2
			case status >= 400 && status < 500:
				return 1
			default:
				return 0
			}
		}
		if statusClass(a.HTTPStatus) != statusClass(b.HTTPStatus) {
			return statusClass(a.HTTPStatus) > statusClass(b.HTTPStatus)
		}

		ar := a.Timings.TotalProbeLatency()
		br := b.Timings.TotalProbeLatency()
		if ar != br {
			return ar < br
		}
		if a.Score != b.Score {
			return a.Score > b.Score
		}
		return a.SNI < b.SNI
	}

	var clusteredCandidates []Candidate
	for _, cluster := range ipClusters {
		sort.SliceStable(cluster, func(i, j int) bool {
			return candidateLess(cluster[i], cluster[j])
		})
		clusteredCandidates = append(clusteredCandidates, cluster[0])
	}

	sort.SliceStable(clusteredCandidates, func(i, j int) bool {
		return candidateLess(clusteredCandidates[i], clusteredCandidates[j])
	})

	pipeStats.SnapshotAndPrint(rtCaches, cfg, len(clusteredCandidates), ds)

	return clusteredCandidates
}

// ================= API HELPERS (ACTIVE-SCANNER STYLE) =================

func getPublicIP(targetIP string) (string, error) {
	if strings.TrimSpace(targetIP) != "" {
		ip := net.ParseIP(strings.TrimSpace(targetIP))
		if ip == nil || ip.To4() == nil {
			return "", fmt.Errorf("invalid target IPv4: %s", targetIP)
		}
		return ip.To4().String(), nil
	}
	client := &http.Client{Timeout: 5 * time.Second}
	for _, endpoint := range []string{
		"https://api.ipify.org",
		"https://ifconfig.me/ip",
		"https://icanhazip.com",
		"http://ip-api.com/line/?fields=query",
	} {
		resp, err := client.Get(endpoint)
		if err != nil {
			continue
		}
		body, err := io.ReadAll(io.LimitReader(resp.Body, 128))
		resp.Body.Close()
		if err != nil {
			continue
		}
		ip := net.ParseIP(strings.TrimSpace(string(body)))
		if ip != nil && ip.To4() != nil {
			return ip.To4().String(), nil
		}
	}
	return "", fmt.Errorf("could not determine public IPv4")
}

func getPrefixes(asn string) []string {
	asn = strings.TrimSpace(strings.ToUpper(asn))
	if asn == "" || asn == "UNKNOWN_ASN" {
		return nil
	}
	if !strings.HasPrefix(asn, "AS") {
		asn = "AS" + asn
	}
	client := &http.Client{Timeout: 10 * time.Second}
	resp, err := client.Get(fmt.Sprintf("https://stat.ripe.net/data/announced-prefixes/data.json?resource=%s", url.QueryEscape(asn)))
	if err != nil {
		return nil
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil
	}
	var result struct {
		Data struct {
			Prefixes []struct {
				Prefix string `json:"prefix"`
			} `json:"prefixes"`
		} `json:"data"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil
	}
	var prefixes []string
	for _, item := range result.Data.Prefixes {
		if strings.Contains(item.Prefix, ":") {
			continue
		}
		if _, _, err := net.ParseCIDR(item.Prefix); err == nil {
			prefixes = append(prefixes, item.Prefix)
		}
	}
	return uniqueStrings(prefixes)
}

func getCountry(ip string) string {
	client := &http.Client{Timeout: 4 * time.Second}
	resp, err := client.Get(fmt.Sprintf("http://ip-api.com/json/%s?fields=countryCode", ip))
	if err != nil {
		return "UNKNOWN"
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return "UNKNOWN"
	}
	var result struct {
		CountryCode string `json:"countryCode"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil || result.CountryCode == "" {
		return "UNKNOWN"
	}
	return strings.ToUpper(result.CountryCode)
}

func getASNAndPrefix(ip string) (string, string) {
	client := &http.Client{Timeout: 6 * time.Second}
	var asn, prefix string

	resp, err := client.Get(fmt.Sprintf("https://stat.ripe.net/data/network-info/data.json?resource=%s", ip))
	if err == nil {
		var result struct {
			Data struct {
				ASNs   []interface{} `json:"asns"`
				Prefix string        `json:"prefix"`
			} `json:"data"`
		}
		if err := json.NewDecoder(resp.Body).Decode(&result); err == nil {
			if len(result.Data.ASNs) > 0 {
				asn = fmt.Sprintf("%v", result.Data.ASNs[0])
				if !strings.HasPrefix(strings.ToUpper(asn), "AS") {
					asn = "AS" + asn
				}
			}
			prefix = result.Data.Prefix
		}
		resp.Body.Close()
	}

	if asn == "" {
		resp2, err2 := client.Get(fmt.Sprintf("http://ip-api.com/json/%s?fields=as", ip))
		if err2 == nil {
			var res2 struct {
				AS string `json:"as"`
			}
			if err := json.NewDecoder(resp2.Body).Decode(&res2); err == nil && res2.AS != "" {
				parts := strings.Split(res2.AS, " ")
				if len(parts) > 0 {
					asn = strings.ToUpper(parts[0])
					if !strings.HasPrefix(asn, "AS") {
						asn = "AS" + asn
					}
				}
			}
			resp2.Body.Close()
		}
	}

	if asn == "" {
		asn = "UNKNOWN_ASN"
	}
	if prefix == "" {
		parsedIP := net.ParseIP(ip)
		if parsedIP != nil && parsedIP.To4() != nil {
			v := parsedIP.To4()
			prefix = fmt.Sprintf("%d.%d.%d.0/24", v[0], v[1], v[2])
		}
	}
	return asn, prefix
}

// ================= MAIN =================

func main() {
	uaRng = rand.New(rand.NewSource(time.Now().UnixNano()))

	cfg := Config{
		Mode:              ModeAuto,
		Workers:           30,
		DNSWorkers:        64,
		MaxIPs:            -1, // full announced ASN scan, capped by LimitMaxIPs
		IPOSINTLimit:      256,
		DomainOSINTLimit:  100,
		TCPTimeoutMs:      3000,
		TLSTimeoutMs:      3000,
		H2ReadTimeoutMs:   3000,
		H2WriteTimeoutMs:  2000,
		DNSQueryTimeoutMs: int(DNSQueryTimeoutDefault.Milliseconds()),
		ECSPrefix:         DefaultECSIPv4Prefix,
		DNSResolvers:      normalizeDNSResolvers(strings.Split(DefaultDNSResolvers, ",")),
		Seed:              time.Now().UnixNano(),
		VTKey:             "dea2ba0b84a3d88ea20a5fb14165e94d170cbe369529dbc57119757e04f1efb5",
		URLScanKey:        "01a032ae-681d-7718-821b-c6fd33aa11a7",
		ChaosKey:          "e3c91ed9-2f79-4147-807f-43dd150003e4",
		NoPTR:             false,
		NoCT:              false,
		NoPassive:         false,
		NoReverseIP:       false,
		ScanEntireASN:     true,
	}

	flag.IntVar(&cfg.Workers, "w", 30, "Worker pool size")
	flag.StringVar(&cfg.TargetIP, "vps-ip", "", "IP сервера; используется для ASN/Country и ECS")
	flag.Parse()

	if cfg.Workers < 1 {
		cfg.Workers = 1
	}
	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer cancel()

	publicIP, err := getPublicIP(cfg.TargetIP)
	if err != nil {
		log.Fatalf("[-] Не удалось определить публичный IPv4: %v", err)
	}
	cfg.TargetIP = publicIP

	parsedIP := net.ParseIP(cfg.TargetIP)
	if parsedIP == nil || parsedIP.To4() == nil {
		log.Fatalf("[-] Invalid target IPv4: %s", cfg.TargetIP)
	}
	cfg.ECSIP = parsedIP.To4().String()

	cfg.TargetASN, _ = getASNAndPrefix(cfg.TargetIP)
	cfg.TargetCountry = getCountry(cfg.TargetIP)
	if cfg.TargetASN == "UNKNOWN_ASN" {
		log.Fatalf("[-] Не удалось определить ASN для %s", cfg.TargetIP)
	}
	if cfg.TargetCountry == "UNKNOWN" {
		log.Printf("[!] Не удалось определить Country для %s; продолжаем без country filter", cfg.TargetIP)
	}

	cidrs := getPrefixes(cfg.TargetASN)
	if len(cidrs) == 0 {
		log.Fatalf("[-] Failed to fetch CIDRs for %s", cfg.TargetASN)
	}
	localPrefix := ""
	for _, c := range cidrs {
		_, ipnet, _ := net.ParseCIDR(c)
		if ipnet != nil && ipnet.Contains(parsedIP) {
			localPrefix = c
			break
		}
	}
	if localPrefix == "" {
		log.Fatalf("[-] Target IP is not present in ASN announced prefixes")
	}

	var samplingCIDRs []string
	if cfg.ScanEntireASN {
		samplingCIDRs = cidrs
	} else {
		samplingCIDRs = []string{localPrefix}
	}
	samplingRanges := MergeCIDRs(samplingCIDRs)
	sampledIPs := SampleIPs(samplingRanges, cfg.MaxIPs, cfg.Seed)
	dnsRanges := MergeCIDRs(cidrs)

	fmt.Printf("[*] ECS client IP:          %s/%d\n", cfg.ECSIP, cfg.ECSPrefix)
	fmt.Printf("[*] Raw UDP DNS pool:       %s\n", strings.Join(cfg.DNSResolvers, ", "))
	fmt.Printf("[*] Целевой IP:             %s\n", cfg.TargetIP)
	fmt.Printf("[*] Announcing ASN:         %s\n", cfg.TargetASN)
	if cfg.ScanEntireASN {
		fmt.Printf("[*] Фокус на все префиксы:   %d подсетей ASN\n", len(cidrs))
	} else {
		fmt.Printf("[*] Фокус на IPv4 prefix:   %s (DNS-валидация по всем %d префиксам ASN)\n", localPrefix, len(cidrs))
	}
	fmt.Printf("[*] Страна сервера:          %s (ip-api)\n", cfg.TargetCountry)
	fmt.Printf("[*] Подготовлено %d IP адресов для passive discovery. Запуск...\n\n", len(sampledIPs))

	results := RunPipeline(ctx, cfg, sampledIPs, dnsRanges)

	if len(results) == 0 {
		fmt.Println("\n[-] Подходящих кандидатов не найдено.")
		return
	}

	fmt.Printf("\n[+] Найдено валидных HTTP/2 целей (после кластеризации): %d\n\n", len(results))
	fmt.Printf("%-32.32s | %-15.15s | %-6s | %-16s | %-30s | %4s\n",
		"Цель (SNI)", "IP адрес", "STATUS", "TLS curve", "certificate", "RTT")
	fmt.Println(strings.Repeat("-", 116))

	for _, r := range results {
		cert := r.CertSubject
		if cert == "" {
			cert = r.CertIssuer
		}
		if cert == "" {
			cert = "-"
		}
		certState := "INVALID"
		if r.CertSNIMatch && r.CertValidTime {
			certState = "valid"
		}
		certCol := fmt.Sprintf("%s [%s]", limitStr(cert, 21), certState)
		rtt := r.Timings.TCP + r.Timings.TLS + r.Timings.H2Headers
		fmt.Printf("%-32.32s | %-15.15s | %-6d | %-16.16s | %-30.30s | %4dms\n",
			r.SNI, r.IP, r.HTTPStatus, r.TLSCurve, certCol, rtt.Milliseconds())
	}

	best := results[0]
	fmt.Println("\n===================================================================================================================")
	fmt.Println("                                   РЕКОМЕНДУЕМАЯ КОНФИГУРАЦИЯ DEST/SNI")
	fmt.Println("===================================================================================================================")
	fmt.Printf("\"dest\": \"%s:443\",\n", best.SNI)
	fmt.Printf("\"serverNames\": [\n  \"%s\"\n]\n\n", best.SNI)
	fmt.Printf("Подробности лучшего кандидата:\n")
	fmt.Printf("STATUS: %d | TLS: %.0f/20 | curve: %s | X25519: %t | certificate: %s | SNI match: %t | Reality feasible: %t | RTT: %d ms\n",
		best.HTTPStatus, best.RealityScore.TLSQuality, best.TLSCurve, best.X25519, best.CertSubject, best.CertSNIMatch, best.RealityFeasible,
		(best.Timings.TCP + best.Timings.TLS + best.Timings.H2Headers).Milliseconds())
	fmt.Printf("-------------------------------------------------------------------------------------------------------------------\n")
	fmt.Printf("RANK: RealityFeasible=%t | BASE SCORE: %.1f | PENALTY: -%.1f | FINAL REALITY SCORE: %.1f/100 (HTTP: %d, Total Probe Latency: %d ms)\n", best.RealityFeasible,
		best.RealityScore.Total, best.DomainPenalty, best.Score, best.HTTPStatus, best.Timings.TotalProbeLatency().Milliseconds())
}
