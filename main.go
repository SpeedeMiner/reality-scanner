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
	"sync/atomic"
	"syscall"
	"time"

	dnscrypt "github.com/ameshkov/dnscrypt/v2"
	"github.com/ameshkov/dnsstamps"
	mdns "github.com/miekg/dns"
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

	dnsFastPoolSize = 32

	LimitMaxIPs          = 262144
	MaxDiscoveredDomains = 50000
	LimitValidPairs      = 10000

	providerMaxAttempts    = 3
	providerCBThreshold    = 8
	providerCBCooldown     = 2 * time.Minute
	provider429CBCooldown  = 5 * time.Minute
	providerBackoffInitial = 750 * time.Millisecond
	providerBackoffSecond  = 2 * time.Second
	providerMaxRetryAfter  = 60 * time.Second
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
)

type Config struct {
	Mode             Mode
	Workers          int
	MaxIPs           int
	IPOSINTLimit     int
	DomainOSINTLimit int
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
	NoPTR            bool
	NoCT             bool
	NoPassive        bool
	NoReverseIP      bool

	VTKey      string
	URLScanKey string
	ChaosKey   string
}

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
}

type PipelineStats struct {
	mu                    sync.Mutex
	IPSampled             int
	IPWithPTR             int
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
	TCPConnected          int
	TLSHandshake          int
	NoPeerCertificates    int
	TLSValidationFailures int
	H2HeadersOK           int
	EndStreamOK           int
	ASNFiltered           int
	CountryFiltered       int
	CDNDropped            int

	Alloc         TotalAllocationStats
	StageC        StageCStats
	ProviderStats map[string]*ProviderStats
}

func NewPipelineStats() *PipelineStats {
	return &PipelineStats{
		ProviderStats: make(map[string]*ProviderStats),
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

type RuntimeCaches struct {
	ProvCache *SafeCache
	ProvGroup *singleflight.Group
	DNSCache  *SafeDNSCache
	DNSGroup  *singleflight.Group
}

func NewRuntimeCaches() *RuntimeCaches {
	return &RuntimeCaches{
		ProvCache: NewSafeCache(),
		ProvGroup: &singleflight.Group{},
		DNSCache:  NewSafeDNSCache(),
		DNSGroup:  &singleflight.Group{},
	}
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

// ================= DNSCRYPT POOL =================
const dnsPoolCacheFile = "dnscrypt_pool.json"
const requiredDNSProps = dnsstamps.ServerInformalPropertyNoLog | dnsstamps.ServerInformalPropertyNoFilter

var resolverListURLsV3 = []string{
	"https://download.dnscrypt.info/resolvers-list/v3/public-resolvers.md",
	"https://raw.githubusercontent.com/DNSCrypt/dnscrypt-resolvers/master/v3/public-resolvers.md",
	"https://cdn.jsdelivr.net/gh/DNSCrypt/dnscrypt-resolvers@master/v3/public-resolvers.md",
}
var resolverListURLsV2 = []string{
	"https://download.dnscrypt.info/resolvers-list/v2/public-resolvers.md",
}

type DNSResolver struct {
	Stamp              string
	Info               *dnscrypt.ResolverInfo
	RTT                time.Duration
	Success            atomic.Uint64
	Failures           atomic.Uint64
	ConsecutiveFailure atomic.Uint64
	mu                 sync.Mutex
	DisabledTo         time.Time
}

func (r *DNSResolver) getInfo() *dnscrypt.ResolverInfo {
	r.mu.Lock()
	defer r.mu.Unlock()
	return r.Info
}

func (r *DNSResolver) refresh() error {
	client := &dnscrypt.Client{Net: "udp", Timeout: 3 * time.Second}
	info, err := client.Dial(r.Stamp)
	if err != nil {
		return err
	}
	r.mu.Lock()
	r.Info = info
	r.mu.Unlock()
	return nil
}

type DNSPool struct {
	mu             sync.RWMutex
	resolvers      []*DNSResolver
	Discovered     atomic.Uint64
	Checked        atomic.Uint64
	Healthy        atomic.Uint64
	LogicalQueries atomic.Uint64
	Queries        atomic.Uint64
	Successes      atomic.Uint64
	Failures       atomic.Uint64
	Retries        atomic.Uint64
	rngMu          sync.Mutex
	rng            *rand.Rand
}

type StampCache struct {
	Timestamp time.Time `json:"timestamp"`
	Stamps    []string  `json:"stamps"`
}

func parseResolverList(body string) []string {
	lines := strings.Split(body, "\n")
	seen := make(map[string]struct{})
	var stamps []string
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if !stampRe.MatchString(line) {
			continue
		}
		stamp, err := dnsstamps.NewServerStampFromString(line)
		if err != nil || stamp.Proto != dnsstamps.StampProtoTypeDNSCrypt || stamp.Props&requiredDNSProps != requiredDNSProps {
			continue
		}
		if _, ok := seen[line]; ok {
			continue
		}
		seen[line] = struct{}{}
		stamps = append(stamps, line)
	}
	return stamps
}

func downloadResolverList(ctx context.Context, urlStr string) ([]string, error) {
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, urlStr, nil)
	if err != nil {
		return nil, err
	}
	client := &http.Client{Timeout: 15 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("HTTP %d from %s", resp.StatusCode, urlStr)
	}
	body, err := io.ReadAll(io.LimitReader(resp.Body, 5<<20))
	if err != nil {
		return nil, err
	}
	return parseResolverList(string(body)), nil
}

func loadResolverStamps(ctx context.Context) ([]string, error) {
	if data, err := os.ReadFile(dnsPoolCacheFile); err == nil {
		var cache StampCache
		if err := json.Unmarshal(data, &cache); err == nil {
			if time.Since(cache.Timestamp) < 12*time.Hour && len(cache.Stamps) > 0 {
				fmt.Printf("[DNS] Загружено %d stamps из локального кэша\n", len(cache.Stamps))
				return cache.Stamps, nil
			}
		}
	}
	var all []string
	for _, urlStr := range resolverListURLsV3 {
		stamps, err := downloadResolverList(ctx, urlStr)
		if err != nil {
			continue
		}
		all = append(all, stamps...)
	}
	if len(all) < 50 {
		for _, urlStr := range resolverListURLsV2 {
			stamps, err := downloadResolverList(ctx, urlStr)
			if err == nil {
				all = append(all, stamps...)
			}
		}
	}
	all = uniqueStrings(all)
	if len(all) == 0 {
		return nil, fmt.Errorf("no DNSCrypt resolvers found")
	}
	cacheData, err := json.Marshal(StampCache{Timestamp: time.Now(), Stamps: all})
	if err == nil {
		_ = os.WriteFile(dnsPoolCacheFile, cacheData, 0644)
	}
	return all, nil
}

func checkDNSResolver(ctx context.Context, stamp string) (*DNSResolver, error) {
	client := &dnscrypt.Client{Net: "udp", Timeout: 3 * time.Second}
	info, err := client.Dial(stamp)
	if err != nil {
		return nil, fmt.Errorf("dial: %w", err)
	}
	tests := []struct {
		Name      string
		Type      uint16
		WantRcode int
	}{
		{"example.com.", mdns.TypeA, mdns.RcodeSuccess},
		{"cloudflare.com.", mdns.TypeA, mdns.RcodeSuccess},
		{"this-name-should-not-exist.invalid.", mdns.TypeA, mdns.RcodeNameError},
	}
	var totalRTT time.Duration
	for _, t := range tests {
		req := new(mdns.Msg)
		req.SetQuestion(t.Name, t.Type)
		req.RecursionDesired = true
		qStart := time.Now()
		resp, err := client.Exchange(req, info)
		if err != nil {
			return nil, fmt.Errorf("exchange %s: %w", t.Name, err)
		}
		totalRTT += time.Since(qStart)
		if resp == nil || resp.Rcode != t.WantRcode {
			return nil, fmt.Errorf("bad response for %s", t.Name)
		}
	}
	return &DNSResolver{Stamp: stamp, Info: info, RTT: totalRTT / 3}, nil
}

func buildDNSPool(ctx context.Context, stamps []string) *DNSPool {
	pool := &DNSPool{rng: rand.New(rand.NewSource(time.Now().UnixNano()))}
	pool.Discovered.Store(uint64(len(stamps)))

	var mu sync.Mutex
	g, gctx := errgroup.WithContext(ctx)
	g.SetLimit(64)

	for _, stamp := range stamps {
		stamp := stamp
		g.Go(func() error {
			r, err := checkDNSResolver(gctx, stamp)
			pool.Checked.Add(1)

			if err == nil {
				pool.Healthy.Add(1)
				mu.Lock()
				pool.resolvers = append(pool.resolvers, r)
				mu.Unlock()
			}
			return nil
		})
	}
	_ = g.Wait()
	pool.sortByRTT()
	return pool
}

func (p *DNSPool) sortByRTT() {
	p.mu.Lock()
	defer p.mu.Unlock()
	sort.Slice(p.resolvers, func(i, j int) bool {
		return p.resolvers[i].RTT < p.resolvers[j].RTT
	})
}

func max64(a, b int64) int64 {
	if a > b {
		return a
	}
	return b
}

func (p *DNSPool) pickWeighted() *DNSResolver {
	p.mu.RLock()
	defer p.mu.RUnlock()

	var available []*DNSResolver
	now := time.Now()
	for _, r := range p.resolvers {
		r.mu.Lock()
		disabled := now.Before(r.DisabledTo)
		r.mu.Unlock()
		if !disabled {
			available = append(available, r)
		}
	}

	if len(available) == 0 {
		return nil
	}
	n := len(available)
	if n > dnsFastPoolSize {
		n = dnsFastPoolSize
	}

	var weights []int
	totalWeight := 0

	for i := 0; i < n; i++ {
		r := available[i]
		r.mu.Lock()
		rtt := r.RTT.Milliseconds()
		r.mu.Unlock()

		success := r.Success.Load()
		failures := r.Failures.Load()
		totalReqs := success + failures
		if totalReqs == 0 {
			totalReqs = 1
		}
		failureRate := float64(failures) / float64(totalReqs)

		weight := 1000 / int(max64(10, rtt))
		if weight < 1 {
			weight = 1
		}
		if failureRate > 0.30 {
			weight /= 4
		} else if failureRate > 0.10 {
			weight /= 2
		}
		if weight < 1 {
			weight = 1
		}

		weights = append(weights, weight)
		totalWeight += weight
	}

	if totalWeight == 0 {
		return available[0]
	}

	p.rngMu.Lock()
	x := p.rng.Intn(totalWeight)
	p.rngMu.Unlock()

	for i, w := range weights {
		if x < w {
			return available[i]
		}
		x -= w
	}
	return available[0]
}

func (p *DNSPool) onFailure(r *DNSResolver) {
	r.mu.Lock()
	r.DisabledTo = time.Now().Add(5 * time.Minute)
	r.mu.Unlock()
}

func (p *DNSPool) resolverFailure(r *DNSResolver) uint64 {
	r.Failures.Add(1)
	n := r.ConsecutiveFailure.Add(1)
	if n >= 3 {
		p.onFailure(r)
	}
	return n
}

func (p *DNSPool) exchange(ctx context.Context, req *mdns.Msg) (*mdns.Msg, *DNSResolver, time.Duration, error) {
	p.LogicalQueries.Add(1)
	var lastErr error

	for attempt := 0; attempt < 3; attempt++ {
		if err := ctx.Err(); err != nil {
			return nil, nil, 0, err
		}
		p.Queries.Add(1)
		if attempt > 0 {
			p.Retries.Add(1)
		}

		resolver := p.pickWeighted()
		if resolver == nil {
			return nil, nil, 0, fmt.Errorf("DNSCrypt pool is empty")
		}

		client := &dnscrypt.Client{Net: "udp", Timeout: 2500 * time.Millisecond}
		info := resolver.getInfo()

		type exRes struct {
			resp *mdns.Msg
			err  error
		}
		ch := make(chan exRes, 1)

		start := time.Now()
		go func() {
			resp, err := client.Exchange(req, info)
			ch <- exRes{resp, err}
		}()

		var resp *mdns.Msg
		var err error
		select {
		case <-ctx.Done():
			return nil, nil, 0, ctx.Err()
		case res := <-ch:
			resp, err = res.resp, res.err
		}
		elapsed := time.Since(start)

		if err != nil {
			failures := p.resolverFailure(resolver)
			if failures == 2 {
				if refreshErr := resolver.refresh(); refreshErr == nil {
					info = resolver.getInfo()
					start = time.Now()

					ch2 := make(chan exRes, 1)
					go func() {
						r, e := client.Exchange(req, info)
						ch2 <- exRes{r, e}
					}()

					select {
					case <-ctx.Done():
						return nil, nil, 0, ctx.Err()
					case res := <-ch2:
						resp, err = res.resp, res.err
					}
					elapsed = time.Since(start)

					if err == nil {
						resolver.ConsecutiveFailure.Store(0)
					} else {
						p.resolverFailure(resolver)
					}
				}
			}

			if err != nil {
				lastErr = err
				continue
			}
		}

		switch resp.Rcode {
		case mdns.RcodeSuccess, mdns.RcodeNameError:
			resolver.Success.Add(1)
			resolver.ConsecutiveFailure.Store(0)
			resolver.mu.Lock()
			if resolver.RTT == 0 {
				resolver.RTT = elapsed
			} else {
				resolver.RTT = (resolver.RTT*7 + elapsed) / 8
			}
			resolver.mu.Unlock()
			p.Successes.Add(1)
			return resp, resolver, elapsed, nil
		case mdns.RcodeServerFailure:
			lastErr = fmt.Errorf("SERVFAIL")
			p.resolverFailure(resolver)
			continue
		case mdns.RcodeRefused:
			lastErr = fmt.Errorf("REFUSED")
			p.resolverFailure(resolver)
			continue
		default:
			lastErr = fmt.Errorf("rcode=%s", mdns.RcodeToString[resp.Rcode])
			p.resolverFailure(resolver)
			continue
		}
	}
	p.Failures.Add(1)
	return nil, nil, 0, lastErr
}

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
	Config      ProviderConfig
	sem         chan struct{}
	mu          sync.Mutex
	nextAllowed time.Time
	cbFailures  int
	cbUntil     time.Time
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

func providerRetryAfter(err error) time.Duration {
	var httpErr *ProviderHTTPError
	if errors.As(err, &httpErr) {
		return httpErr.RetryAfter
	}
	return 0
}

func isTransientProviderError(err error) bool {
	if err == nil {
		return false
	}
	if errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) || os.IsTimeout(err) {
		return true
	}
	var httpErr *ProviderHTTPError
	if errors.As(err, &httpErr) {
		switch httpErr.StatusCode {
		case http.StatusTooManyRequests,
			http.StatusInternalServerError,
			http.StatusBadGateway,
			http.StatusServiceUnavailable,
			http.StatusGatewayTimeout:
			return true
		}
	}
	msg := strings.ToLower(err.Error())
	for _, s := range []string{
		"connection reset",
		"connection refused",
		"broken pipe",
		"unexpected eof",
		"temporary",
		"tls handshake timeout",
	} {
		if strings.Contains(msg, s) {
			return true
		}
	}
	return false
}

func (r *ProviderRunner) Execute(ctx context.Context, query string, client *http.Client, pipeStats *PipelineStats, rtCaches *RuntimeCaches) ExecResult {
	statName := r.StatsKey()
	cacheKey := fmt.Sprintf("%s:%d:%s:maxnames=%d:maxpages=%d", r.Name(), r.QueryType(), query, r.Config.MaxNames, r.Config.MaxPages)

	if cached, status, ok := rtCaches.ProvCache.Get(cacheKey); ok {
		return ExecResult{Names: cached, Status: status}
	}

	v, _, _ := rtCaches.ProvGroup.Do(cacheKey, func() (interface{}, error) {
		r.mu.Lock()
		cbOpen := !r.cbUntil.IsZero() && time.Now().Before(r.cbUntil)
		cbUntil := r.cbUntil
		r.mu.Unlock()

		if cbOpen {
			pipeStats.recordProviderStat(statName, r.Category(), StatSkipped, false, 0, 0, 0, 0, 0, 0, fmt.Sprintf("circuit-open until %s", cbUntil.Format(time.RFC3339)), 0)
			return ExecResult{nil, StatSkipped}, nil
		}

		var (
			rawRes  []string
			err     error
			retries int
		)

		for attempt := 1; attempt <= providerMaxAttempts; attempt++ {
			if errWait := r.waitRate(ctx); errWait != nil {
				pipeStats.recordProviderStat(statName, r.Category(), StatWaitCanceled, false, 0, 0, 0, 0, 0, 0, fmt.Sprintf("wait cancelled: %v", errWait), retries)
				return ExecResult{nil, StatWaitCanceled}, nil
			}

			if r.sem != nil {
				select {
				case r.sem <- struct{}{}:
				case <-ctx.Done():
					return ExecResult{nil, StatWaitCanceled}, nil
				}
			}

			reqCtx, cancel := context.WithTimeout(ctx, r.Config.Timeout)
			rawRes, err = r.Fetch(reqCtx, query, client, r.Config)
			cancel()

			if r.sem != nil {
				<-r.sem
			}

			if err == nil {
				break
			}

			if errors.Is(err, context.Canceled) {
				break
			}

			httpStatus := providerHTTPStatus(err)
			if httpStatus == http.StatusTooManyRequests {
				break
			}

			if !isTransientProviderError(err) || attempt == providerMaxAttempts {
				break
			}

			retries++
			backoff := providerRetryAfter(err)
			if backoff <= 0 {
				switch attempt {
				case 1:
					backoff = providerBackoffInitial
				case 2:
					backoff = providerBackoffSecond
				default:
					backoff = 4 * time.Second
				}
			}
			select {
			case <-time.After(backoff):
			case <-ctx.Done():
				return ExecResult{nil, StatWaitCanceled}, nil
			}
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

				pipeStats.recordProviderStat(statName, r.Category(), StatNoData, false, 0, 0, 0, 0, 0, httpStatus, err.Error(), retries)
				rtCaches.ProvCache.Put(cacheKey, []string{}, StatNoData, 2*time.Minute)
				return ExecResult{[]string{}, StatNoData}, nil
			}

			if len(cleanRes) > 0 {
				pipeStats.recordProviderStat(statName, r.Category(), StatPartial, isTimeout, rawCount, uniqueCount, invalidCount, limitedCount, acceptedCount, httpStatus, err.Error(), retries)
				rtCaches.ProvCache.Put(cacheKey, cleanRes, StatPartial, 2*time.Minute)
				return ExecResult{cleanRes, StatPartial}, nil
			}

			pipeStats.recordProviderStat(statName, r.Category(), StatFailed, isTimeout, rawCount, uniqueCount, invalidCount, limitedCount, acceptedCount, httpStatus, err.Error(), retries)

			if isTransientProviderError(err) && !errors.Is(err, context.Canceled) {
				r.mu.Lock()
				r.cbFailures++
				if r.cbFailures >= providerCBThreshold || httpStatus == http.StatusTooManyRequests {
					cooldown := providerCBCooldown
					if httpStatus == http.StatusTooManyRequests {
						cooldown = provider429CBCooldown
					}
					r.cbUntil = time.Now().Add(cooldown)
				}
				r.mu.Unlock()
			} else {
				r.mu.Lock()
				r.cbFailures = 0
				r.mu.Unlock()
			}
			return ExecResult{nil, StatFailed}, nil
		}

		r.mu.Lock()
		r.cbFailures = 0
		r.cbUntil = time.Time{}
		r.mu.Unlock()

		if len(cleanRes) == 0 {
			pipeStats.recordProviderStat(statName, r.Category(), StatNoData, false, rawCount, uniqueCount, invalidCount, limitedCount, acceptedCount, httpStatus, "http 200: no valid names found", retries)
			rtCaches.ProvCache.Put(cacheKey, []string{}, StatNoData, 2*time.Minute)
			return ExecResult{[]string{}, StatNoData}, nil
		}

		pipeStats.recordProviderStat(statName, r.Category(), StatSuccess, false, rawCount, uniqueCount, invalidCount, limitedCount, acceptedCount, 0, "", retries)
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
	req.Header.Set("User-Agent", "asn-sni-osint/1.0 (+authorized-security-research)")
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
	u := fmt.Sprintf("https://jldc.me/anubis/subdomains/%s", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
	if err != nil {
		return nil, err
	}
	req.Header.Set("User-Agent", "asn-sni-osint/1.0 (+authorized-security-research)")
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
	req.Header.Set("User-Agent", "asn-sni-osint/1.0 (+authorized-security-research)")
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
	req.Header.Set("User-Agent", "asn-sni-osint/1.0 (+authorized-security-research)")
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
	req.Header.Set("User-Agent", "asn-sni-osint/1.0 (+authorized-security-research)")
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
		req.Header.Set("User-Agent", "asn-sni-osint/1.0 (+authorized-security-research)")
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
		req.Header.Set("User-Agent", "asn-sni-osint/1.0 (+authorized-security-research)")
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
	req.Header.Set("User-Agent", "asn-sni-osint/1.0 (+authorized-security-research)")
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
	req.Header.Set("User-Agent", "asn-sni-osint/1.0 (+authorized-security-research)")
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
		req.Header.Add("x-apikey", p.Key)
		req.Header.Set("User-Agent", "asn-sni-osint/1.0 (+authorized-security-research)")
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
		req.Header.Add("x-apikey", p.Key)
		req.Header.Set("User-Agent", "asn-sni-osint/1.0 (+authorized-security-research)")
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
		req.Header.Set("api-key", key)
		req.Header.Set("User-Agent", "asn-sni-osint/1.0 (+authorized-security-research)")

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
				var v interface{}
				if err := json.Unmarshal(raw, &v); err != nil {
					return domains, fmt.Errorf("invalid urlscan sort value: %w", err)
				}
				switch x := v.(type) {
				case string:
					parts = append(parts, x)
				default:
					parts = append(parts, fmt.Sprint(x))
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
	req.Header.Add("Authorization", p.Key)
	req.Header.Set("User-Agent", "asn-sni-osint/1.0 (+authorized-security-research)")
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

func distributeRoots(roots []RootCandidate, providers []*ProviderRunner, overlapPercent int, cfg Config) (map[*ProviderRunner][]RootCandidate, TotalAllocationStats) {
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
		capacity[p] = limit
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
)

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
	providerRoots, allocStats := distributeRoots(roots, providers, 20, cfg)

	pipeStats.mu.Lock()
	pipeStats.Alloc = allocStats
	pipeStats.StageC.TotalRoots = len(roots)
	pipeStats.StageC.Assigned = allocStats.AssignedRoots + allocStats.OverlappedAssignments
	pipeStats.mu.Unlock()

	providerLimits := make(map[*ProviderRunner]int)
	providerUsed := make(map[*ProviderRunner]int)
	for _, p := range providers {
		limit := effectiveRootLimit(p, cfg)
		if limit <= 0 {
			limit = 999999
		}
		providerLimits[p] = limit
		providerUsed[p] = len(providerRoots[p])
	}

	jobQueues := make(map[*ProviderRunner]chan RootCandidate)
	for _, p := range providers {
		jobQueues[p] = make(chan RootCandidate, providerLimits[p]+1000)
	}

	var stateMu sync.Mutex
	rootStates := make(map[string]RootState)
	history := make(map[string]map[*ProviderRunner]bool)
	for _, r := range roots {
		rootStates[r.Domain] = RootPending
		history[r.Domain] = make(map[*ProviderRunner]bool)
	}

	markCompleted := func(domain string) bool {
		stateMu.Lock()
		defer stateMu.Unlock()
		if rootStates[domain] == RootPending {
			rootStates[domain] = RootCompleted
			pipeStats.mu.Lock()
			pipeStats.StageC.CompletedRoots++
			pipeStats.mu.Unlock()
			return true
		}
		return false
	}

	markLost := func(domain string) {
		stateMu.Lock()
		defer stateMu.Unlock()
		if rootStates[domain] == RootPending {
			rootStates[domain] = RootLost
			pipeStats.mu.Lock()
			pipeStats.StageC.LostRoots++
			pipeStats.mu.Unlock()
		}
	}

	var activeTasks sync.WaitGroup
	var workerWG sync.WaitGroup

	for p, proots := range providerRoots {
		for _, r := range proots {
			history[r.Domain][p] = true
			activeTasks.Add(1)
			jobQueues[p] <- r
		}
	}

	reassignCh := make(chan RootCandidate, len(roots)*len(providers))

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
				for root := range jobQueues[p] {
					if ctx.Err() != nil {
						activeTasks.Done()
						continue
					}

					res := p.Execute(ctx, root.Domain, client, pipeStats, rtCaches)

					pipeStats.mu.Lock()
					pipeStats.StageC.Executed++
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

					needsReassign := (res.Status != StatSuccess)

					if res.Status == StatSuccess {
						markCompleted(root.Domain)
					}

					if ctx.Err() == nil && needsReassign {
						activeTasks.Add(1)
						reassignCh <- root
					}

					if len(res.Names) > 0 {
						inheritedSrc := rootProvenance[root.Domain]
						for _, d := range res.Names {
							ds.AddDomainSource(d, p.SourceBit(), inheritedSrc)
						}
					}
					activeTasks.Done()
				}
			}()
		}
	}

	workerWG.Add(1)
	go func() {
		defer workerWG.Done()
		for root := range reassignCh {
			stateMu.Lock()
			isCompleted := (rootStates[root.Domain] == RootCompleted)
			stateMu.Unlock()

			if isCompleted {
				activeTasks.Done()
				continue
			}

			stateMu.Lock()
			tried := history[root.Domain]
			var nextP *ProviderRunner

			for _, p := range providers {
				if !tried[p] {
					p.mu.Lock()
					cbOpen := !p.cbUntil.IsZero() && time.Now().Before(p.cbUntil)
					p.mu.Unlock()

					if !cbOpen && providerUsed[p] < providerLimits[p] {
						nextP = p
						break
					}
				}
			}

			if nextP != nil {
				tried[nextP] = true
				providerUsed[nextP]++
				pipeStats.mu.Lock()
				pipeStats.StageC.Reassigned++
				pipeStats.mu.Unlock()

				activeTasks.Add(1)
				jobQueues[nextP] <- root
			} else {
				markLost(root.Domain)
			}
			stateMu.Unlock()
			
			activeTasks.Done()
		}
	}()

	go func() {
		activeTasks.Wait()
		close(reassignCh)
		for _, p := range providers {
			close(jobQueues[p])
		}
	}()

	waitCh := make(chan struct{})
	go func() {
		workerWG.Wait()
		close(waitCh)
	}()

	select {
	case <-waitCh:
	case <-ctx.Done():
	}

	stateMu.Lock()
	for _, r := range roots {
		if rootStates[r.Domain] == RootPending {
			rootStates[r.Domain] = RootCanceled
			pipeStats.mu.Lock()
			pipeStats.StageC.CanceledRoots++
			pipeStats.mu.Unlock()
		}
	}
	stateMu.Unlock()
}

func (s *PipelineStats) SnapshotAndPrint(pool *DNSPool, clustered int, ds *DiscoveryState) {
	s.mu.Lock()
	pSampled := s.IPSampled
	pWithPTR := s.IPWithPTR
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
	pTLSVal := s.TLSValidationFailures
	pNoCert := s.NoPeerCertificates
	pH2Head := s.H2HeadersOK

	fASN := s.ASNFiltered
	fCountry := s.CountryFiltered

	localStats := make(map[string]ProviderStats)
	for k, v := range s.ProviderStats {
		localStats[k] = *v
	}
	allocStats := s.Alloc
	stageC := s.StageC
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

	if droppedGlobal > 0 {
		fmt.Printf("[!] Доменов отброшено глобальным лимитом (MaxDiscoveredDomains=%d): %d\n", MaxDiscoveredDomains, droppedGlobal)
	}

	fmt.Printf("\n[*] STAGE C: Domain OSINT Pipeline Stats:\n")
	fmt.Printf("    Total Roots:           %d\n", stageC.TotalRoots)
	fmt.Printf("    Assigned (Primary+Ov): %d\n", stageC.Assigned)
	fmt.Printf("    Completed (Unique):    %d\n", stageC.CompletedRoots)
	fmt.Printf("    Lost (Exhausted):      %d\n", stageC.LostRoots)
	fmt.Printf("    Canceled (Timeout):    %d\n", stageC.CanceledRoots)
	fmt.Printf("    --- Executions ---\n")
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

			fmt.Printf("    %-20s : Roots: %d (prim:%d ov:%d) | Попыток: %d (Успех: %d, NoData: %d, Част: %d, Ошиб: %d, Cancel: %d) -> Raw: %d (Уник: %d, Невалид: %d, Лимит: %d, Accept: %d)",
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

	fmt.Println("\n[DNSCrypt Pool Telemetry]")
	fmt.Printf("  Logical Queries:             %d\n", pool.LogicalQueries.Load())
	fmt.Printf("  Resolver Exchanges:          %d (Успех: %d, Ошибок: %d, Ретраи: %d)\n", pool.Queries.Load(), pool.Successes.Load(), pool.Failures.Load(), pool.Retries.Load())

	fmt.Printf("\n[*] Logical DNS Lookups:       %d (Успех: %d, Ошибок: %d)\n", qDNS, qDNSSuc, qDNSFail)
	fmt.Printf("    Детали DNS успехов:        Resolved IPs: %d, NXDOMAIN: %d, NoIPv4: %d\n", qResolved, qNX, qNoV4)
	fmt.Printf("    Детали DNS ошибок:         Timeout: %d, Temporary: %d, Other: %d\n", qTimeout, qTemp, qOther)
	fmt.Printf("[*] Target Range IP Matches:   %d\n", qTargetMatches)
	fmt.Printf("[*] DNS доменов с Target IP:   %d\n", qTargetDomains)
	fmt.Printf("[*] Отсеяно по ASN:            %d\n", fASN)
	fmt.Printf("[*] Отсеяно по Country:        %d\n", fCountry)
	fmt.Printf("[*] Подтверждено DNS-пар:      %d\n", qValidPairs)
	if droppedPairs > 0 {
		fmt.Printf("[!] DNS-пар отброшено лимитом (LimitValidPairs=%d): %d\n", LimitValidPairs, droppedPairs)
	}
	fmt.Printf("[*] Успешных TCP соединений:   %d\n", pTCP)
	fmt.Printf("[*] Успешных TLS хэндшейков:   %d\n", pTLS)
	fmt.Printf("[*] Отсутствие сертификатов:   %d\n", pNoCert)
	fmt.Printf("[*] Ошибок валидации TLS:      %d\n", pTLSVal)
	fmt.Printf("[*] С откликом H2 Headers:     %d\n", pH2Head)
	fmt.Printf("[*] Финальных IP-кластеров:    %d\n", clustered)
}

// ================= DB & IP HELPERS =================
func ensureDB(path, dbURL string) error {
	if fi, err := os.Stat(path); err == nil && fi.Size() > 1024*1024 {
		if db, err := geoip2.Open(path); err == nil {
			db.Close()
			return nil
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

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("RIPEstat HTTP %d", resp.StatusCode)
	}
	var stat RipeStatResponse
	if err := json.NewDecoder(resp.Body).Decode(&stat); err != nil {
		return nil, err
	}
	var cidrs []string
	for _, p := range stat.Data.Prefixes {
		if !strings.Contains(p.Prefix, ":") {
			if _, _, err := net.ParseCIDR(p.Prefix); err == nil {
				cidrs = append(cidrs, p.Prefix)
			}
		}
	}
	return cidrs, nil
}

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

func resolvePTRDNSCrypt(ctx context.Context, pool *DNSPool, ip string) ([]string, error) {
	rev, err := reverseIPv4(ip)
	if err != nil {
		return nil, err
	}
	req := new(mdns.Msg)
	req.SetQuestion(rev, mdns.TypePTR)
	req.RecursionDesired = true
	resp, _, _, err := pool.exchange(ctx, req)
	if err != nil {
		return nil, err
	}
	if resp.Rcode == mdns.RcodeNameError {
		return nil, ErrDNSNXDomain
	}
	if resp.Rcode != mdns.RcodeSuccess {
		return nil, fmt.Errorf("DNS response code: %s", mdns.RcodeToString[resp.Rcode])
	}
	var names []string
	for _, ans := range resp.Answer {
		if ptr, ok := ans.(*mdns.PTR); ok {
			if d := CleanDomain(ptr.Ptr); d != "" {
				names = append(names, d)
			}
		}
	}
	return names, nil
}

func resolveIPv4DNSCrypt(ctx context.Context, pool *DNSPool, domain string) ([]string, error) {
	req := new(mdns.Msg)
	req.SetQuestion(mdns.Fqdn(domain), mdns.TypeA)
	req.RecursionDesired = true
	resp, _, _, err := pool.exchange(ctx, req)
	if err != nil {
		return nil, err
	}
	if resp.Rcode == mdns.RcodeNameError {
		return nil, ErrDNSNXDomain
	}
	if resp.Rcode != mdns.RcodeSuccess {
		return nil, fmt.Errorf("DNS response code: %s", mdns.RcodeToString[resp.Rcode])
	}
	seen := make(map[string]struct{})
	var ips []string
	for _, answer := range resp.Answer {
		if a, ok := answer.(*mdns.A); ok {
			ip := a.A.String()
			if _, exists := seen[ip]; !exists {
				seen[ip] = struct{}{}
				ips = append(ips, ip)
			}
		}
	}
	return ips, nil
}

var ErrDNSNXDomain = errors.New("NXDOMAIN")

func resolveIPv4Cached(ctx context.Context, pool *DNSPool, domain string, rtCaches *RuntimeCaches) ([]string, error) {
	domain = CleanDomain(domain)
	if domain == "" {
		return nil, fmt.Errorf("invalid domain")
	}
	v, err, _ := rtCaches.DNSGroup.Do(domain, func() (interface{}, error) {
		if cached, ok := rtCaches.DNSCache.Get(domain); ok {
			if cached.NXDomain {
				return nil, ErrDNSNXDomain
			}
			return cached.IPs, nil
		}
		ips, err := resolveIPv4DNSCrypt(ctx, pool, domain)
		if errors.Is(err, ErrDNSNXDomain) {
			rtCaches.DNSCache.Put(domain, &DNSCacheEntry{NXDomain: true}, 1*time.Minute)
			return nil, err
		}
		if err != nil {
			return nil, err
		}
		rtCaches.DNSCache.Put(domain, &DNSCacheEntry{IPs: ips}, 5*time.Minute)
		return ips, nil
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

func (e *ProbeError) Error() string { return e.Err.Error() }

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

func buildClientSettingsFrame() []byte {
	payload := make([]byte, 30)
	binary.BigEndian.PutUint16(payload[0:2], 1)
	binary.BigEndian.PutUint32(payload[2:6], 65536)
	binary.BigEndian.PutUint16(payload[6:8], 2)
	binary.BigEndian.PutUint32(payload[8:12], 0)
	binary.BigEndian.PutUint16(payload[12:14], 3)
	binary.BigEndian.PutUint32(payload[14:18], 1000)
	binary.BigEndian.PutUint16(payload[18:20], 4)
	binary.BigEndian.PutUint32(payload[20:24], 6291456)
	binary.BigEndian.PutUint16(payload[24:26], 6)
	binary.BigEndian.PutUint32(payload[26:30], 262144)
	return buildH2Frame(FrameSettings, 0, 0, payload)
}

func buildWindowUpdateFrame(streamID uint32, increment uint32) []byte {
	payload := make([]byte, 4)
	binary.BigEndian.PutUint32(payload, increment&0x7FFFFFFF)
	return buildH2Frame(FrameWindowUpdate, 0, streamID, payload)
}

func parseResponseHeaders(cand *Candidate, headers []hpack.HeaderField) error {
	weakCount := 0
	blockStatus := 0
	hasStatus := false

	for _, h := range headers {
		hName := strings.ToLower(strings.TrimSpace(h.Name))

		if hName == ":status" {
			n, err := strconv.Atoi(strings.TrimSpace(h.Value))
			if err != nil {
				return fmt.Errorf("invalid :status value %q: %w", h.Value, err)
			}
			if n < 100 || n > 999 {
				return fmt.Errorf("invalid HTTP status: %d", n)
			}
			blockStatus = n
			hasStatus = true
		}
	}

	if !hasStatus {
		return fmt.Errorf("response HEADERS missing :status")
	}

	isInformational := blockStatus >= 100 && blockStatus < 200
	isFinalResponse := blockStatus >= 200

	if isInformational {
		return nil
	}

	if isFinalResponse && !cand.ResponseHeadersParsed {
		cand.HTTPStatus = blockStatus
		cand.ResponseHeadersParsed = true

		for _, h := range headers {
			hName := strings.ToLower(strings.TrimSpace(h.Name))
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

		if cand.CDNStatus == CDNStatusUnknown && weakCount > 0 {
			cand.CDNStatus = CDNLikely
		}
	}

	return nil
}

func parseTrailers(cand *Candidate, headers []hpack.HeaderField) error {
	cand.ResponseTrailersSeen = true
	for _, h := range headers {
		if len(h.Name) > 0 && h.Name[0] == ':' {
			return fmt.Errorf("pseudo-header %q found in trailers", h.Name)
		}
	}
	return nil
}

func ProbeH2(ctx context.Context, ip, sni string, ev Evidence, cfg Config) (*Candidate, *ProbeError) {
	cand := &Candidate{
		IP:            ip,
		SNI:           sni,
		Evidence:      ev,
		DomainQuality: classifyDomainQuality(sni),
		CDNStatus:     CDNStatusUnknown,
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
	uConn.SetDeadline(time.Time{})

	state := uConn.ConnectionState()

	if state.Version != tls.VersionTLS13 {
		return cand, &ProbeError{
			Stage: ProbeStageTLS,
			Err:   fmt.Errorf("unexpected TLS version: 0x%x", state.Version),
		}
	}
	cand.TLS13 = true

	if state.NegotiatedProtocol == "h2" {
		cand.ALPN = "h2"
	} else {
		cand.ALPN = "h2 (no ALPN)"
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
	if err := writeH2(uConn, buildClientSettingsFrame(), wTo); err != nil {
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
			if !firstFrameSeen {
				cand.Timings.H2FirstFrame = time.Since(requestSent)
				firstFrameSeen = true
			}

			frameType, flags := data[3], data[4]
			streamID := binary.BigEndian.Uint32(data[5:9]) & 0x7FFFFFFF
			payload := data[9 : 9+length]
			recvBuf.Next(int(9 + length))

			if expectingContinuation && frameType != FrameContinuation {
				return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("expected CONTINUATION frame")}
			}

			switch frameType {
			case FrameSettings, FrameGoAway:
				if streamID != 0 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("frame type %d must use stream 0, got %d", frameType, streamID)}
				}
			case FrameHeaders, FrameData, FrameRSTStream, FrameContinuation:
				if streamID == 0 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("frame type %d must use non-zero stream", frameType)}
				}
			}

			switch frameType {
			case FrameSettings:
				if length%6 != 0 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid SETTINGS length")}
				}
				if flags&FlagAck != 0 {
					if length != 0 {
						return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("SETTINGS ACK with non-zero payload")}
					}
					cand.H2SettingsAckReceived = true
					cand.SettingsAckCount++
					break
				}
				cand.SettingsFramesCount++
				seenSettings := make(map[uint16]bool)
				var prof PeerSettingsProfile
				if cand.H2SettingsReceived {
					prof = cand.LatestPeerSettings
				}
				for i := 0; i < int(length); i += 6 {
					id := binary.BigEndian.Uint16(payload[i : i+2])
					val := binary.BigEndian.Uint32(payload[i+2 : i+6])
					if seenSettings[id] {
						return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("duplicate SETTINGS identifier")}
					}
					seenSettings[id] = true
					switch id {
					case 1:
						prof.HeaderTableSize = val
						prof.HasHeaderTableSize = true
						decoder.SetMaxDynamicTableSize(val)
					case 2:
						return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("server sent SETTINGS_ENABLE_PUSH")}
					case 3:
						prof.MaxConcurrentStreams = val
						prof.HasMaxConcurrentStreams = true
					case 4:
						if val > 0x7fffffff {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid INITIAL_WINDOW_SIZE")}
						}
						prof.InitialWindowSize = val
						prof.HasInitialWindowSize = true
					case 5:
						if val < 16384 || val > 16777215 {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid MAX_FRAME_SIZE")}
						}
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
				} else {
					if prof != cand.LatestPeerSettings {
						cand.SettingsChanges++
					}
					cand.LatestPeerSettings = prof
				}
				if err := writeH2(uConn, buildH2Frame(FrameSettings, FlagAck, 0, nil), wTo); err != nil {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
				}
				cand.H2SettingsAckSent = true

			case FrameHeaders:
				if streamID == 1 {
					isTrailers := cand.EndStreamSeen
					if (flags & FlagEndStream) != 0 {
						cand.EndStreamSeen = true
					}
					actualPayload := payload
					padLen := 0
					if flags&FlagPadded != 0 {
						if len(actualPayload) < 1 {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("PADDED flag set but payload too short")}
						}
						padLen = int(actualPayload[0])
						actualPayload = actualPayload[1:]
					}
					if flags&FlagPriority != 0 {
						if len(actualPayload) < 5 {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("PRIORITY flag set but payload too short")}
						}
						actualPayload = actualPayload[5:]
					}
					if padLen > len(actualPayload) {
						return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("padding exceeds payload")}
					}
					actualPayload = actualPayload[:len(actualPayload)-padLen]

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

						if !cand.ResponseHeadersParsed && !isTrailers {
							if err := parseResponseHeaders(cand, headers); err != nil {
								return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
							}
						} else {
							if err := parseTrailers(cand, headers); err != nil {
								return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
							}
						}
						headerBlocks.Reset()

						if cand.ResponseHeadersParsed && !cand.H2HeadersReceived {
							cand.Timings.H2Headers = time.Since(requestSent)
							cand.H2HeadersReceived = true
						}
					}
				}
			case FrameContinuation:
				if !expectingContinuation {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("unexpected CONTINUATION frame")}
				}
				if streamID != activeStreamID {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("CONTINUATION stream mismatch: got %d, want %d", streamID, activeStreamID)}
				}
				headerBlocks.Write(payload)
				if (flags & FlagEndHeaders) != 0 {
					expectingContinuation = false
					headers, err := decoder.DecodeFull(headerBlocks.Bytes())
					if err != nil {
						return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
					}

					if !cand.ResponseHeadersParsed {
						if err := parseResponseHeaders(cand, headers); err != nil {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
						}
					} else {
						if err := parseTrailers(cand, headers); err != nil {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: err}
						}
					}
					headerBlocks.Reset()

					if cand.ResponseHeadersParsed && !cand.H2HeadersReceived {
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
					padLen := 0
					if flags&FlagPadded != 0 {
						if len(actualPayload) < 1 {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("PADDED flag set on DATA but payload too short")}
						}
						padLen = int(actualPayload[0])
						actualPayload = actualPayload[1:]
					}
					if padLen > len(actualPayload) {
						return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("padding exceeds DATA payload")}
					}
					actualPayload = actualPayload[:len(actualPayload)-padLen]

					cand.BodyBytes += len(actualPayload)
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
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid WINDOW_UPDATE length")}
				}
				increment := binary.BigEndian.Uint32(payload) & 0x7fffffff
				if increment == 0 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("WINDOW_UPDATE increment is zero")}
				}
			case FrameRSTStream:
				if length != 4 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid RST_STREAM length")}
				}
				if streamID == 1 {
					cand.StreamReset = true
					break ReadLoop
				}
			case FrameGoAway:
				if length < 8 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid GOAWAY length")}
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

	if cand.H2SettingsReceived && cand.H2HeadersReceived && cand.HTTPStatus >= 200 && cand.EndStreamSeen {
		cand.H2ProtocolConfirmed = true
	}

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

	cand.RealityScore = rs
	cand.DomainPenalty = scorePenalty
	cand.Score = rs.Total - scorePenalty

	return cand.Score >= 0
}

func RunPipeline(ctx context.Context, cfg Config, sampledIPs []string, scanRanges []ipRange, pool *DNSPool, asnDB, countryDB *geoip2.Reader) []Candidate {
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
		extProviders = append(extProviders, NewRunner(&crtShProvider{}, ProviderConfig{Timeout: 6 * time.Second, MaxConcurrent: 1, MinInterval: 12 * time.Second, MaxNames: 1000, MaxRoots: 30, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&certSpotterProvider{}, ProviderConfig{Timeout: 5 * time.Second, MaxConcurrent: 4, MaxNames: 1000, MaxRoots: 50, MaxPages: 3}))
	}
	if !cfg.NoPassive {
		extProviders = append(extProviders, NewRunner(&alienVaultProvider{}, ProviderConfig{Timeout: 8 * time.Second, MaxConcurrent: 2, MinInterval: 1 * time.Second, MaxNames: 1000, MaxRoots: 100, MaxPages: 3}))
		extProviders = append(extProviders, NewRunner(&waybackProvider{}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 3, MaxNames: 10000, MaxRoots: 100, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&anubisProvider{}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 3, MinInterval: 500 * time.Millisecond, MaxNames: 1000, MaxRoots: 100, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&threatMinerProvider{}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 3, MinInterval: 1 * time.Second, MaxNames: 1000, MaxRoots: 100, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&hackerTargetHostSearchProvider{}, ProviderConfig{Timeout: 6 * time.Second, MaxConcurrent: 1, MinInterval: 2 * time.Second, MaxNames: 1000, MaxRoots: 30, MaxPages: 1}))
	}
	if !cfg.NoReverseIP {
		extProviders = append(extProviders, NewRunner(&hackerTargetProvider{}, ProviderConfig{Timeout: 6 * time.Second, MaxConcurrent: 1, MinInterval: 2 * time.Second, MaxNames: 1000, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&shodanInternetDBProvider{}, ProviderConfig{Timeout: 6 * time.Second, MaxConcurrent: 10, MinInterval: 50 * time.Millisecond, MaxNames: 1000, MaxPages: 1}))
	}
	if cfg.VTKey != "" {
		extProviders = append(extProviders, NewRunner(&vtDomainProvider{Key: cfg.VTKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MinInterval: 1 * time.Second, MaxNames: 2000, MaxRoots: 100, MaxPages: 3}))
		extProviders = append(extProviders, NewRunner(&vtIPProvider{Key: cfg.VTKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MinInterval: 1 * time.Second, MaxNames: 2000, MaxPages: 3}))
	}
	if cfg.URLScanKey != "" {
		extProviders = append(extProviders, NewRunner(&urlScanDomainProvider{Key: cfg.URLScanKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MaxNames: 10000, MaxRoots: 100, MaxPages: 5}))
		extProviders = append(extProviders, NewRunner(&urlScanIPProvider{Key: cfg.URLScanKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MaxNames: 10000, MaxPages: 5}))
	}
	if cfg.ChaosKey != "" {
		extProviders = append(extProviders, NewRunner(&chaosProvider{Key: cfg.ChaosKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 1, MinInterval: 1 * time.Second, MaxNames: 2000, MaxRoots: 100, MaxPages: 1}))
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
							names, err := resolvePTRDNSCrypt(gCtxA, pool, ip)
							if err == nil && len(names) > 0 {
								for _, n := range names {
									ds.AddPairSource(ip, n, SourcePTR)
								}
								pipeStats.mu.Lock()
								pipeStats.IPWithPTR++
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
	if len(domainProviders) > 0 {
		RunStageC(ctx, rootsRanked, domainProviders, cfg, httpClient, pipeStats, rtCaches, ds, rootProvenance)
	} else {
		pipeStats.mu.Lock()
		pipeStats.StageC.TotalRoots = len(rootsRanked)
		pipeStats.StageC.LostRoots = len(rootsRanked)
		pipeStats.mu.Unlock()
	}

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
	gD.SetLimit(cfg.Workers)
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

			ips, err := resolveIPv4Cached(gCtxD, pool, dom, rtCaches)

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
					parsedIP := net.ParseIP(resolvedIP)
					if parsedIP != nil {
						var asn uint
						var country string
						if asnDB != nil {
							if r, err := asnDB.ASN(parsedIP); err == nil {
								asn = uint(r.AutonomousSystemNumber)
							}
						}
						if countryDB != nil {
							if r, err := countryDB.Country(parsedIP); err == nil {
								country = r.Country.IsoCode
							}
						}
						if cfg.TargetASN != 0 && asn != cfg.TargetASN {
							pipeStats.mu.Lock()
							pipeStats.ASNFiltered++
							pipeStats.mu.Unlock()
							continue
						}
						if cfg.TargetCountry != "" && !strings.EqualFold(country, cfg.TargetCountry) {
							pipeStats.mu.Lock()
							pipeStats.CountryFiltered++
							pipeStats.mu.Unlock()
							continue
						}
					}

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
	gE, gCtxE := errgroup.WithContext(ctx)
	gE.SetLimit(cfg.Workers)

	for _, p := range validPairs {
		p := p
		gE.Go(func() error {
			if gCtxE.Err() != nil {
				return gCtxE.Err()
			}
			cand, pErr := ProbeH2(gCtxE, p.IP, p.SNI, p.Evidence, cfg)

			tcpOK := pErr == nil || pErr.Stage > ProbeStageTCP
			tlsOK := pErr == nil || pErr.Stage > ProbeStageTLS

			pipeStats.mu.Lock()
			if tcpOK {
				pipeStats.TCPConnected++
			}
			if tlsOK {
				pipeStats.TLSHandshake++
			}
			if pErr != nil && pErr.Stage == ProbeStageTLSValidation {
				if strings.Contains(pErr.Err.Error(), "no peer certificates") {
					pipeStats.NoPeerCertificates++
				} else {
					pipeStats.TLSValidationFailures++
				}
			}
			if cand != nil && cand.H2HeadersReceived {
				pipeStats.H2HeadersOK++
			}
			if cand != nil && cand.EndStreamSeen {
				pipeStats.EndStreamOK++
			}
			pipeStats.mu.Unlock()

			if pErr != nil {
				return nil
			}

			if parsedIP := net.ParseIP(cand.IP); parsedIP != nil {
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

			if validateAndEnrich(cand, cfg, pipeStats) {
				candMu.Lock()
				candidates = append(candidates, *cand)
				candMu.Unlock()
			}
			return nil
		})
	}
	if err := gE.Wait(); err != nil || ctx.Err() != nil {
		fmt.Println("[-] Выполнение прервано (Stage E).")
		return nil
	}

	ipClusters := make(map[string][]Candidate)
	for _, c := range candidates {
		ipClusters[c.IP] = append(ipClusters[c.IP], c)
	}

	var clusteredCandidates []Candidate
	for _, cluster := range ipClusters {
		sort.Slice(cluster, func(i, j int) bool {
			if cluster[i].Score != cluster[j].Score {
				return cluster[i].Score > cluster[j].Score
			}
			if cluster[i].Timings.TotalProbeLatency() != cluster[j].Timings.TotalProbeLatency() {
				return cluster[i].Timings.TotalProbeLatency() < cluster[j].Timings.TotalProbeLatency()
			}
			return cluster[i].SNI < cluster[j].SNI
		})
		clusteredCandidates = append(clusteredCandidates, cluster[0])
	}

	sort.Slice(clusteredCandidates, func(i, j int) bool {
		if clusteredCandidates[i].Score != clusteredCandidates[j].Score {
			return clusteredCandidates[i].Score > clusteredCandidates[j].Score
		}
		if clusteredCandidates[i].Timings.TotalProbeLatency() != clusteredCandidates[j].Timings.TotalProbeLatency() {
			return clusteredCandidates[i].Timings.TotalProbeLatency() < clusteredCandidates[j].Timings.TotalProbeLatency()
		}
		return clusteredCandidates[i].SNI < clusteredCandidates[j].SNI
	})

	pipeStats.SnapshotAndPrint(pool, len(clusteredCandidates), ds)

	return clusteredCandidates
}

// ================= MAIN =================

func main() {
	cfg := Config{}
	var modeStr, domainsStr string

	flag.StringVar(&modeStr, "mode", "autonomous", "autonomous | direct")
	flag.IntVar(&cfg.Workers, "w", 30, "Worker pool size for generic tasks")
	flag.IntVar(&cfg.MaxIPs, "max-ips", 0, "Limit for IP sampling (0 = default 1024, -1 = up to hard safety limit 262144)")
	flag.IntVar(&cfg.IPOSINTLimit, "ip-osint-limit", 256, "Maximum Reverse-IP queries per provider (0 = all sampled IPs)")
	flag.IntVar(&cfg.DomainOSINTLimit, "domain-osint-limit", 100, "Maximum roots per domain OSINT provider (0 = all eligible roots)")
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

	flag.BoolVar(&cfg.NoPTR, "no-ptr", false, "Disable Reverse DNS PTR lookups")
	flag.BoolVar(&cfg.NoCT, "no-ct", false, "Disable Certificate Transparency lookups")
	flag.BoolVar(&cfg.NoPassive, "no-passive", false, "Disable Passive DNS OSINT")
	flag.BoolVar(&cfg.NoReverseIP, "no-reverse-ip", false, "Disable Reverse IP lookups")

	flag.StringVar(&cfg.VTKey, "vt-key", os.Getenv("dea2ba0b84a3d88ea20a5fb14165e94d170cbe369529dbc57119757e04f1efb5"), "VirusTotal API Key")
	flag.StringVar(&cfg.URLScanKey, "urlscan-key", os.Getenv("01a032ae-681d-7718-821b-c6fd33aa11a7"), "URLScan.io API Key")
	flag.StringVar(&cfg.ChaosKey, "chaos-key", os.Getenv("e3c91ed9-2f79-4147-807f-43dd150003e4"), "ProjectDiscovery Chaos API Key")

	flag.Parse()

	if cfg.Workers < 1 {
		cfg.Workers = 1
	}
	cfg.Mode = Mode(modeStr)
	cfg.CIDRs = flag.Args()

	if domainsStr != "" {
		for _, d := range strings.Split(domainsStr, ",") {
			if cleaned := CleanDomain(d); cleaned != "" {
				cfg.Domains = append(cfg.Domains, cleaned)
			}
		}
	}

	if cfg.Mode != ModeAuto && cfg.Mode != ModeDirect {
		log.Fatalf("[-] Unknown mode: %s", cfg.Mode)
	}
	if cfg.Mode == ModeDirect {
		if len(cfg.CIDRs) == 0 {
			log.Fatal("[-] Direct mode requires at least one IPv4 CIDR")
		}
		if CleanDomain(cfg.DirectSNI) == "" {
			log.Fatal("[-] Direct mode requires -sni target explicitly")
		}
	}
	if cfg.MaxIPs == -1 {
		fmt.Printf("[!] ВНИМАНИЕ: Выбран режим полного сканирования (-1 = до %d адресов).\n", LimitMaxIPs)
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

	dnsCtx, dnsCancel := context.WithTimeout(ctx, 60*time.Second)
	defer dnsCancel()
	fmt.Println("[DNS] Загрузка публичного DNSCrypt pool...")
	stamps, err := loadResolverStamps(dnsCtx)
	if err != nil {
		log.Fatalf("[-] DNSCrypt list: %v", err)
	}

	dnsPool := buildDNSPool(dnsCtx, stamps)
	dnsPool.mu.RLock()
	poolSize := len(dnsPool.resolvers)
	dnsPool.mu.RUnlock()

	if poolSize < 5 {
		log.Fatalf("[-] Слишком мало рабочих DNSCrypt resolver'ов: %d", poolSize)
	}
	fmt.Printf("[+] Рабочий DNSCrypt pool: %d resolver'ов\n", poolSize)

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
		var samplingCIDRs []string
		if !cfg.ScanEntireASN {
			if localPrefix == "" {
				log.Fatal("[-] Target IP is not present in ASN announced prefixes. Use --scan-all-asn.")
			}
			samplingCIDRs = []string{localPrefix}
		} else {
			samplingCIDRs = cidrs
		}

		samplingRanges := MergeCIDRs(samplingCIDRs)
		sampledIPs := SampleIPs(samplingRanges, cfg.MaxIPs, cfg.Seed)
		dnsRanges := MergeCIDRs(cidrs)

		fmt.Printf("[*] Целевой IP:             %s\n", vpsQueryIP)
		fmt.Printf("[*] Announcing ASN:         AS%d\n", cfg.TargetASN)
		if !cfg.ScanEntireASN {
			fmt.Printf("[*] Фокус на IPv4 prefix:    %s (DNS-валидация по всем %d префиксам ASN)\n", localPrefix, len(cidrs))
		} else {
			fmt.Printf("[*] Фокус на все префиксы:   %d подсетей ASN\n", len(cidrs))
		}
		fmt.Printf("[*] Страна сервера:          %s (MaxMind GeoIP)\n", cfg.TargetCountry)
		fmt.Printf("[*] Подготовлено %d IP адресов для OSINT-сэмплинга. Запуск...\n\n", len(sampledIPs))

		results = RunPipeline(ctx, cfg, sampledIPs, dnsRanges, dnsPool, asnDB, countryDB)

	} else if cfg.Mode == ModeDirect {
		merged := MergeCIDRs(cfg.CIDRs)
		sampledIPs := SampleIPs(merged, cfg.MaxIPs, cfg.Seed)
		fmt.Printf("[*] Direct Mode: Подготовлено %d IP адресов. Запуск...\n", len(sampledIPs))
		results = RunPipeline(ctx, cfg, sampledIPs, merged, dnsPool, asnDB, countryDB)
	}

	if len(results) == 0 {
		fmt.Println("\n[-] Подходящих кандидатов не найдено.")
		return
	}

	fmt.Printf("\n[+] Найдено валидных HTTP/2 целей (после кластеризации): %d\n\n", len(results))
	fmt.Printf("%-32.32s | %-15.15s | %-5s | %-4s | %-4s | %-4s | %-4s | %-4s | %-5s | %-6s | %4s %4s %4s\n",
		"Цель (SNI)", "IP адрес", "SCORE", "TLS", "CERT", "H2", "SRV", "HTTP", "DSCOV", "STATUS", "TCP", "TLS", "H2")
	fmt.Println(strings.Repeat("-", 126))

	for _, r := range results {
		rs := r.RealityScore
		scoreStr := fmt.Sprintf("%.1f", r.Score)

		fmt.Printf("%-32.32s | %-15.15s | %-5s | %2.0f   | %2.0f   | %2.0f   | %2.0f   | %2.0f   | %2.0f    | %-6d | %3d %3d %3d\n",
			r.SNI, r.IP, scoreStr, rs.TLSQuality, rs.Certificate, rs.H2Profile, rs.ServerProfile, rs.HTTPBehavior, rs.DiscoveryScore, r.HTTPStatus,
			r.Timings.TCP.Milliseconds(), r.Timings.TLS.Milliseconds(), r.Timings.H2Headers.Milliseconds())
	}

	best := results[0]
	fmt.Println("\n===================================================================================================================")
	fmt.Println("                                   РЕКОМЕНДУЕМАЯ КОНФИГУРАЦИЯ DEST/SNI")
	fmt.Println("===================================================================================================================")
	fmt.Printf("\"dest\": \"%s:443\",\n", best.SNI)
	fmt.Printf("\"serverNames\": [\n  \"%s\"\n]\n\n", best.SNI)
	fmt.Printf("Подробности лучшего кандидата:\n")
	fmt.Printf("TLS: %.0f/20 | CERT: %.0f/20 | H2: %.0f/20 | SERVER: %.0f/10 | HTTP: %.0f/10 | DSCOV: %.0f/10 | LATENCY: TCP %dms, TLS %dms, H2 %dms\n",
		best.RealityScore.TLSQuality, best.RealityScore.Certificate, best.RealityScore.H2Profile, best.RealityScore.ServerProfile, best.RealityScore.HTTPBehavior, best.RealityScore.DiscoveryScore,
		best.Timings.TCP.Milliseconds(), best.Timings.TLS.Milliseconds(), best.Timings.H2Headers.Milliseconds())
	fmt.Printf("-------------------------------------------------------------------------------------------------------------------\n")
	fmt.Printf("BASE SCORE: %.1f | PENALTY: -%.1f | FINAL REALITY SCORE: %.1f/100 (HTTP: %d, Total Probe Latency: %d ms)\n",
		best.RealityScore.Total, best.DomainPenalty, best.Score, best.HTTPStatus, best.Timings.TotalProbeLatency().Milliseconds())
}
