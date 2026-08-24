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

	maxDiscoveryRoots = 30
	dnsFastPoolSize   = 16
)

var (
	cdnStrong = []string{"cloudflare", "fastly", "akamai", "ddos-guard", "qrator", "sucuri"}
	cdnWeak   = []string{"x-cache", "x-served-by", "x-edge"}
	junkTLDs  = []string{".xyz", ".top", ".site", ".fun", ".online", ".space", ".pw", ".cc", ".icu", ".click", ".win", ".bid", ".date"}
	dynDNS    = []string{"duckdns.org", "mooo.com", "ddns.net", "freeddns.org", "crabdance.com", "eu.org", "cloudns.cc", "hopto.org", "zapto.org", "sytes.net", "dyn.com", "no-ip.org"}

	domainRe    = regexp.MustCompile(`^[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(\.[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+$`)
	numRe       = regexp.MustCompile(`(?i)(^|\.)\d+\.[a-z]{2,}$`)
	stampRe     = regexp.MustCompile(`^sdns://[A-Za-z0-9_-]+=*$`)
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
	
	NoPTR            bool
	NoCT             bool
	NoPassive        bool
	NoReverseIP      bool

	// API Keys
	VTKey          string
	URLScanKey     string
	ChaosKey       string
	SecTrailsKey   string
}

// ================= DOMAIN PROVENANCE =================

type DomainSource uint32

const (
	SourceSeed DomainSource = 1 << iota
	SourcePTR
	SourceCRTSh
	SourceCertSpotter
	SourceAlienVault
	SourceWayback
	SourceHackerTarget
	SourceVirusTotal
	SourceSecurityTrails
	SourceChaos
	SourceURLScan
)

func (s DomainSource) Has(flag DomainSource) bool {
	return s&flag != 0
}

// ================= MODELS =================

type Timings struct {
	TCP          time.Duration
	TLS          time.Duration
	H2FirstFrame time.Duration
	H2Headers    time.Duration
}

func (t Timings) TotalProbeLatency() time.Duration {
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
	DiscoveryScore float64
	Latency        float64
	Total          float64
}

type CDNStatus string

const (
	CDNConfirmed CDNStatus = "Confirmed"
	CDNLikely    CDNStatus = "Likely"
	CDNUnknown   CDNStatus = "Unknown"
)

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
	CDNProvider       string
	CDNConfidence     int
	CDNStatus         CDNStatus
	Score             float64
	DomainPenalty     float64
	RealityScore      RealityScore
	CertChainValid    bool
	EndStreamSeen     bool
	StreamReset       bool
	GoAwaySeen        bool

	Sources       DomainSource
	DomainQuality string

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
	IP      string
	SNI     string
	Sources DomainSource
}

// ================= TELEMETRY & CACHES =================

type ProviderStats struct {
	Attempts int
	Success  int
	Failed   int
	Timeouts int
	Names    int
	Category DiscoveryCategory
}

type PipelineStats struct {
	mu                  sync.Mutex
	IPSampled           int
	IPWithPTR           int
	DNSQueries          int
	DNSSuccess          int
	DNSFailed           int
	DNSNXDomain         int
	DNSTimeout          int
	DNSTemporary        int
	DNSNoIPv4           int
	DNSOtherErr         int
	DNSResolvedIPs      int
	DNSIPsInTargetRange int
	DNSTargetDomains    int
	DNSValidPairs       int
	TCPConnected        int
	TLSHandshake        int
	TLSValidation       int
	H2HeadersOK         int
	EndStreamOK         int

	ASNFiltered     int
	CountryFiltered int
	CDNDropped      int

	ProviderStats map[string]*ProviderStats
}

var stats = PipelineStats{
	ProviderStats: make(map[string]*ProviderStats),
}

func recordProviderStat(name string, cat DiscoveryCategory, success bool, isTimeout bool, names int) {
	stats.mu.Lock()
	defer stats.mu.Unlock()
	ps, ok := stats.ProviderStats[name]
	if !ok {
		ps = &ProviderStats{Category: cat}
		stats.ProviderStats[name] = ps
	}
	ps.Attempts++
	if success {
		ps.Success++
		ps.Names += names
	} else {
		ps.Failed++
		if isTimeout {
			ps.Timeouts++
		}
	}
}

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
	provCache = NewSafeCache()
	provGroup singleflight.Group
	dnsCache  = NewSafeCache()
	dnsGroup  singleflight.Group
)

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

var ErrDNSNXDomain = errors.New("dns nxdomain")

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
	r.DisabledTo = time.Time{}
	r.mu.Unlock()
	r.ConsecutiveFailure.Store(0)
	return nil
}

type DNSPool struct {
	mu         sync.RWMutex
	resolvers  []*DNSResolver
	Discovered atomic.Uint64
	Checked    atomic.Uint64
	Healthy    atomic.Uint64
	Queries    atomic.Uint64
	Successes  atomic.Uint64
	Failures   atomic.Uint64
	Retries    atomic.Uint64
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
			if time.Since(cache.Timestamp) < 24*time.Hour && len(cache.Stamps) > 0 {
				fmt.Printf("[DNS] Загружено %d stamps из локального кэша\n", len(cache.Stamps))
				return cache.Stamps, nil
			}
		}
	}

	var all []string
	for _, urlStr := range resolverListURLsV3 {
		stamps, err := downloadResolverList(ctx, urlStr)
		if err != nil {
			fmt.Printf("[DNS] V3 source failed: %s: %v\n", urlStr, err)
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

	cacheData, _ := json.Marshal(StampCache{Timestamp: time.Now(), Stamps: all})
	os.WriteFile(dnsPoolCacheFile, cacheData, 0644)
	return all, nil
}

func checkDNSResolver(ctx context.Context, stamp string) (*DNSResolver, error) {
	client := &dnscrypt.Client{Net: "udp", Timeout: 3 * time.Second}
	start := time.Now()
	info, err := client.Dial(stamp)
	if err != nil {
		return nil, fmt.Errorf("dial: %w", err)
	}
	dialRTT := time.Since(start)

	tests := []struct {
		Name string
		Type uint16
	}{
		{"example.com.", mdns.TypeA},
		{"cloudflare.com.", mdns.TypeA},
		{"iana.org.", mdns.TypeA},
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
		if resp == nil || resp.Rcode != mdns.RcodeSuccess {
			return nil, fmt.Errorf("bad response for %s", t.Name)
		}
	}

	return &DNSResolver{Stamp: stamp, Info: info, RTT: dialRTT + totalRTT/3}, nil
}

func buildDNSPool(ctx context.Context, stamps []string) *DNSPool {
	pool := &DNSPool{}
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
	total := 0

	for i := 0; i < n; i++ {
		r := available[i]
		r.mu.Lock()
		rtt := r.RTT.Milliseconds()
		r.mu.Unlock()

		weight := 1000 / int(max64(10, rtt))
		if weight < 1 {
			weight = 1
		}
		weights = append(weights, weight)
		total += weight
	}

	if total == 0 {
		return available[0]
	}

	x := rand.Intn(total)
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

func (p *DNSPool) exchange(ctx context.Context, req *mdns.Msg) (*mdns.Msg, *DNSResolver, time.Duration, error) {
	p.Queries.Add(1)
	var lastErr error

	for attempt := 0; attempt < 3; attempt++ {
		if err := ctx.Err(); err != nil {
			return nil, nil, 0, err
		}
		if attempt > 0 {
			p.Retries.Add(1)
		}
		resolver := p.pickWeighted()
		if resolver == nil {
			return nil, nil, 0, fmt.Errorf("DNSCrypt pool is empty")
		}

		client := &dnscrypt.Client{Net: "udp", Timeout: 2500 * time.Millisecond}
		info := resolver.getInfo()

		start := time.Now()
		resp, err := client.Exchange(req, info)
		elapsed := time.Since(start)

		if err != nil {
			resolver.Failures.Add(1)
			failures := resolver.ConsecutiveFailure.Add(1)

			if failures == 1 {
				if refreshErr := resolver.refresh(); refreshErr == nil {
					info = resolver.getInfo()
					start = time.Now()
					resp, err = client.Exchange(req, info)
					elapsed = time.Since(start)
				}
			}

			if err != nil {
				if failures >= 3 {
					p.onFailure(resolver)
				}
				lastErr = err
				continue
			}
			resolver.ConsecutiveFailure.Store(0)
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
			resolver.Failures.Add(1)
			continue
		case mdns.RcodeRefused:
			lastErr = fmt.Errorf("REFUSED")
			resolver.Failures.Add(1)
			continue
		default:
			lastErr = fmt.Errorf("rcode=%s", mdns.RcodeToString[resp.Rcode])
			resolver.Failures.Add(1)
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
}

func (e *ProviderHTTPError) Error() string {
	return fmt.Sprintf("http %d", e.StatusCode)
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

type SNIProvider interface {
	Name() string
	Category() DiscoveryCategory
	QueryType() ProviderQueryType
	SourceBit() DomainSource
	MaxRoots() int
	Fetch(ctx context.Context, query string, client *http.Client) ([]string, error)
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

type ProviderConfig struct {
	Timeout       time.Duration
	MaxConcurrent int
	MinInterval   time.Duration
	MaxNames      int
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

func (r *ProviderRunner) waitRate(ctx context.Context) error {
	if r.Config.MinInterval <= 0 {
		return nil
	}

	r.mu.Lock()
	now := time.Now()
	allowed := r.nextAllowed
	if now.After(allowed) {
		allowed = now
	}
	next := allowed.Add(r.Config.MinInterval)
	wait := time.Until(allowed)
	r.nextAllowed = next
	r.mu.Unlock()

	if wait <= 0 {
		return nil
	}

	timer := time.NewTimer(wait)
	defer timer.Stop()

	select {
	case <-timer.C:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

func (r *ProviderRunner) Execute(ctx context.Context, query string, client *http.Client) []string {
	cacheKey := fmt.Sprintf("%s:%s", r.Name(), query)
	if cached, ok := provCache.Get(cacheKey); ok {
		return cached
	}

	v, _, _ := provGroup.Do(cacheKey, func() (interface{}, error) {
		r.mu.Lock()
		if time.Now().Before(r.cbUntil) {
			r.mu.Unlock()
			return nil, nil
		}
		r.mu.Unlock()

		if err := r.waitRate(ctx); err != nil {
			return nil, err
		}

		if r.sem != nil {
			select {
			case r.sem <- struct{}{}:
				defer func() { <-r.sem }()
			case <-ctx.Done():
				return nil, ctx.Err()
			}
		}

		reqCtx, cancel := context.WithTimeout(ctx, r.Config.Timeout)
		defer cancel()

		res, err := r.Fetch(reqCtx, query, client)
		isTimeout := errors.Is(err, context.DeadlineExceeded) || os.IsTimeout(err)

		r.mu.Lock()
		if err != nil {
			var httpErr *ProviderHTTPError
			is5xx := errors.As(err, &httpErr) && httpErr.StatusCode >= 500
			isLimit := strings.Contains(strings.ToLower(err.Error()), "limit") || strings.Contains(strings.ToLower(err.Error()), "too many")

			if isTimeout || is5xx || isLimit {
				r.cbFailures++
				if r.cbFailures >= 5 && r.cbUntil.IsZero() {
					r.cbUntil = time.Now().Add(5 * time.Minute)
					fmt.Printf("[!] %s временно отключен на 5м после 5 сбоев.\n", r.Name())
				}
			}
		} else {
			r.cbFailures = 0
			r.cbUntil = time.Time{}
		}
		r.mu.Unlock()

		if err != nil {
			recordProviderStat(r.Name(), r.Category(), false, isTimeout, 0)
			return nil, err
		}

		cleanRes := uniqueStrings(res)
		if r.Config.MaxNames > 0 && len(cleanRes) > r.Config.MaxNames {
			cleanRes = cleanRes[:r.Config.MaxNames]
		}

		recordProviderStat(r.Name(), r.Category(), true, false, len(cleanRes))
		provCache.Put(cacheKey, cleanRes)
		return cleanRes, nil
	})

	if v != nil {
		return v.([]string)
	}
	return nil
}

// -------------------------------------------------
// Implementations: Enterprise API Providers
// -------------------------------------------------

type vtDomainProvider struct { Key string }
func (p *vtDomainProvider) Name() string                 { return "VirusTotal" }
func (p *vtDomainProvider) Category() DiscoveryCategory  { return CatPassiveDNS }
func (p *vtDomainProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *vtDomainProvider) SourceBit() DomainSource      { return SourceVirusTotal }
func (p *vtDomainProvider) MaxRoots() int                { return 100 }
func (p *vtDomainProvider) Fetch(ctx context.Context, query string, client *http.Client) ([]string, error) {
	u := fmt.Sprintf("https://www.virustotal.com/api/v3/domains/%s/subdomains?limit=40", url.QueryEscape(query))
	req, _ := http.NewRequestWithContext(ctx, "GET", u, nil)
	req.Header.Add("x-apikey", p.Key)
	resp, err := client.Do(req)
	if err != nil { return nil, err }
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK { return nil, &ProviderHTTPError{StatusCode: resp.StatusCode} }
	var res struct { Data []struct { Id string `json:"id"` } `json:"data"` }
	if err := json.NewDecoder(resp.Body).Decode(&res); err != nil { return nil, err }
	var subs []string
	for _, item := range res.Data {
		if d := CleanDomain(item.Id); d != "" { subs = append(subs, d) }
	}
	return subs, nil
}

type vtIPProvider struct { Key string }
func (p *vtIPProvider) Name() string                 { return "VirusTotal" }
func (p *vtIPProvider) Category() DiscoveryCategory  { return CatReverseIP }
func (p *vtIPProvider) QueryType() ProviderQueryType { return QueryIP }
func (p *vtIPProvider) SourceBit() DomainSource      { return SourceVirusTotal }
func (p *vtIPProvider) MaxRoots() int                { return 0 }
func (p *vtIPProvider) Fetch(ctx context.Context, query string, client *http.Client) ([]string, error) {
	u := fmt.Sprintf("https://www.virustotal.com/api/v3/ip_addresses/%s/resolutions?limit=40", url.QueryEscape(query))
	req, _ := http.NewRequestWithContext(ctx, "GET", u, nil)
	req.Header.Add("x-apikey", p.Key)
	resp, err := client.Do(req)
	if err != nil { return nil, err }
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK { return nil, &ProviderHTTPError{StatusCode: resp.StatusCode} }
	var res struct { Data []struct { Attributes struct { HostName string `json:"host_name"` } `json:"attributes"` } `json:"data"` }
	if err := json.NewDecoder(resp.Body).Decode(&res); err != nil { return nil, err }
	var subs []string
	for _, item := range res.Data {
		if d := CleanDomain(item.Attributes.HostName); d != "" { subs = append(subs, d) }
	}
	return subs, nil
}

type urlScanDomainProvider struct { Key string }
func (p *urlScanDomainProvider) Name() string                 { return "URLScan" }
func (p *urlScanDomainProvider) Category() DiscoveryCategory  { return CatArchive }
func (p *urlScanDomainProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *urlScanDomainProvider) SourceBit() DomainSource      { return SourceURLScan }
func (p *urlScanDomainProvider) MaxRoots() int                { return 100 }
func (p *urlScanDomainProvider) Fetch(ctx context.Context, query string, client *http.Client) ([]string, error) {
	u := fmt.Sprintf("https://urlscan.io/api/v1/search/?q=domain:%s", url.QueryEscape(query))
	req, _ := http.NewRequestWithContext(ctx, "GET", u, nil)
	req.Header.Add("API-Key", p.Key)
	resp, err := client.Do(req)
	if err != nil { return nil, err }
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK { return nil, &ProviderHTTPError{StatusCode: resp.StatusCode} }
	var res struct { Results []struct { Page struct { Domain string `json:"domain"` } `json:"page"` } `json:"results"` }
	if err := json.NewDecoder(resp.Body).Decode(&res); err != nil { return nil, err }
	var subs []string
	for _, item := range res.Results {
		if d := CleanDomain(item.Page.Domain); d != "" { subs = append(subs, d) }
	}
	return subs, nil
}

type urlScanIPProvider struct { Key string }
func (p *urlScanIPProvider) Name() string                 { return "URLScan" }
func (p *urlScanIPProvider) Category() DiscoveryCategory  { return CatArchive }
func (p *urlScanIPProvider) QueryType() ProviderQueryType { return QueryIP }
func (p *urlScanIPProvider) SourceBit() DomainSource      { return SourceURLScan }
func (p *urlScanIPProvider) MaxRoots() int                { return 0 }
func (p *urlScanIPProvider) Fetch(ctx context.Context, query string, client *http.Client) ([]string, error) {
	u := fmt.Sprintf("https://urlscan.io/api/v1/search/?q=page.ip:%s", url.QueryEscape(query))
	req, _ := http.NewRequestWithContext(ctx, "GET", u, nil)
	req.Header.Add("API-Key", p.Key)
	resp, err := client.Do(req)
	if err != nil { return nil, err }
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK { return nil, &ProviderHTTPError{StatusCode: resp.StatusCode} }
	var res struct { Results []struct { Page struct { Domain string `json:"domain"` } `json:"page"` } `json:"results"` }
	if err := json.NewDecoder(resp.Body).Decode(&res); err != nil { return nil, err }
	var subs []string
	for _, item := range res.Results {
		if d := CleanDomain(item.Page.Domain); d != "" { subs = append(subs, d) }
	}
	return subs, nil
}

type securityTrailsProvider struct { Key string }
func (p *securityTrailsProvider) Name() string                 { return "SecurityTrails" }
func (p *securityTrailsProvider) Category() DiscoveryCategory  { return CatPassiveDNS }
func (p *securityTrailsProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *securityTrailsProvider) SourceBit() DomainSource      { return SourceSecurityTrails }
func (p *securityTrailsProvider) MaxRoots() int                { return 100 }
func (p *securityTrailsProvider) Fetch(ctx context.Context, query string, client *http.Client) ([]string, error) {
	u := fmt.Sprintf("https://api.securitytrails.com/v1/domain/%s/subdomains", url.QueryEscape(query))
	req, _ := http.NewRequestWithContext(ctx, "GET", u, nil)
	req.Header.Add("APIKEY", p.Key)
	resp, err := client.Do(req)
	if err != nil { return nil, err }
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK { return nil, &ProviderHTTPError{StatusCode: resp.StatusCode} }
	var res struct { Subdomains []string `json:"subdomains"` }
	if err := json.NewDecoder(resp.Body).Decode(&res); err != nil { return nil, err }
	var subs []string
	for _, sub := range res.Subdomains {
		if d := CleanDomain(sub + "." + query); d != "" { subs = append(subs, d) }
	}
	return subs, nil
}

type chaosProvider struct { Key string }
func (p *chaosProvider) Name() string                 { return "Chaos" }
func (p *chaosProvider) Category() DiscoveryCategory  { return CatPassiveDNS }
func (p *chaosProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *chaosProvider) SourceBit() DomainSource      { return SourceChaos }
func (p *chaosProvider) MaxRoots() int                { return 100 }
func (p *chaosProvider) Fetch(ctx context.Context, query string, client *http.Client) ([]string, error) {
	u := fmt.Sprintf("https://dns.projectdiscovery.io/dns/%s/subdomains", url.QueryEscape(query))
	req, _ := http.NewRequestWithContext(ctx, "GET", u, nil)
	req.Header.Add("Authorization", p.Key)
	resp, err := client.Do(req)
	if err != nil { return nil, err }
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK { return nil, &ProviderHTTPError{StatusCode: resp.StatusCode} }
	var res struct { Subdomains []string `json:"subdomains"` }
	if err := json.NewDecoder(resp.Body).Decode(&res); err != nil { return nil, err }
	var subs []string
	for _, sub := range res.Subdomains {
		if d := CleanDomain(sub + "." + query); d != "" { subs = append(subs, d) }
	}
	return subs, nil
}

// -------------------------------------------------
// Implementations: Public Providers
// -------------------------------------------------

type crtShProvider struct{}

func (p *crtShProvider) Name() string                 { return "crt.sh" }
func (p *crtShProvider) Category() DiscoveryCategory  { return CatCertificate }
func (p *crtShProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *crtShProvider) SourceBit() DomainSource      { return SourceCRTSh }
func (p *crtShProvider) MaxRoots() int                { return 30 }
func (p *crtShProvider) Fetch(ctx context.Context, query string, client *http.Client) ([]string, error) {
	u := fmt.Sprintf("https://crt.sh/?q=%%25.%s&output=json", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, "GET", u, nil)
	if err != nil {
		return nil, err
	}
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, &ProviderHTTPError{StatusCode: resp.StatusCode}
	}
	var ctRes []struct{ NameValue string `json:"name_value"` }
	if err := json.NewDecoder(resp.Body).Decode(&ctRes); err != nil {
		return nil, err
	}
	var subs []string
	for _, rec := range ctRes {
		for _, part := range strings.Split(rec.NameValue, "\n") {
			if d := CleanDomain(part); d != "" {
				subs = append(subs, d)
			}
		}
	}
	return subs, nil
}

type certSpotterProvider struct{}

func (p *certSpotterProvider) Name() string                 { return "CertSpotter" }
func (p *certSpotterProvider) Category() DiscoveryCategory  { return CatCertificate }
func (p *certSpotterProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *certSpotterProvider) SourceBit() DomainSource      { return SourceCertSpotter }
func (p *certSpotterProvider) MaxRoots() int                { return 30 }
func (p *certSpotterProvider) Fetch(ctx context.Context, query string, client *http.Client) ([]string, error) {
	u := fmt.Sprintf("https://api.certspotter.com/v1/issuances?domain=%s&include_subdomains=true&expand=dns_names", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, "GET", u, nil)
	if err != nil {
		return nil, err
	}
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, &ProviderHTTPError{StatusCode: resp.StatusCode}
	}
	var issuances []struct{ DNSNames []string `json:"dns_names"` }
	if err := json.NewDecoder(resp.Body).Decode(&issuances); err != nil {
		return nil, err
	}
	var result []string
	for _, iss := range issuances {
		for _, name := range iss.DNSNames {
			if d := CleanDomain(name); d != "" {
				result = append(result, d)
			}
		}
	}
	return result, nil
}

type alienVaultProvider struct{}

func (p *alienVaultProvider) Name() string                 { return "AlienVault" }
func (p *alienVaultProvider) Category() DiscoveryCategory  { return CatPassiveDNS }
func (p *alienVaultProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *alienVaultProvider) SourceBit() DomainSource      { return SourceAlienVault }
func (p *alienVaultProvider) MaxRoots() int                { return 100 }
func (p *alienVaultProvider) Fetch(ctx context.Context, query string, client *http.Client) ([]string, error) {
	u := fmt.Sprintf("https://otx.alienvault.com/api/v1/indicators/domain/%s/passive_dns", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, "GET", u, nil)
	if err != nil {
		return nil, err
	}
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, &ProviderHTTPError{StatusCode: resp.StatusCode}
	}
	var otxRes struct {
		PassiveDNS []struct{ Hostname string `json:"hostname"` } `json:"passive_dns"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&otxRes); err != nil {
		return nil, err
	}
	var result []string
	for _, entry := range otxRes.PassiveDNS {
		if d := CleanDomain(entry.Hostname); d != "" {
			result = append(result, d)
		}
	}
	return result, nil
}

type waybackProvider struct{}

func (p *waybackProvider) Name() string                 { return "WaybackMachine" }
func (p *waybackProvider) Category() DiscoveryCategory  { return CatArchive }
func (p *waybackProvider) QueryType() ProviderQueryType { return QueryDomain }
func (p *waybackProvider) SourceBit() DomainSource      { return SourceWayback }
func (p *waybackProvider) MaxRoots() int                { return 100 }
func (p *waybackProvider) Fetch(ctx context.Context, query string, client *http.Client) ([]string, error) {
	u := fmt.Sprintf("http://web.archive.org/cdx/search/cdx?url=*.%s/*&output=json&collapse=urlkey&fl=original&limit=1000", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, "GET", u, nil)
	if err != nil {
		return nil, err
	}
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, &ProviderHTTPError{StatusCode: resp.StatusCode}
	}
	var cdx [][]string
	if err := json.NewDecoder(resp.Body).Decode(&cdx); err != nil {
		return nil, err
	}
	var result []string
	for i, row := range cdx {
		if i == 0 || len(row) < 1 {
			continue // Skip header
		}
		if parsed, err := url.Parse(row[0]); err == nil && parsed.Hostname() != "" {
			if d := CleanDomain(parsed.Hostname()); d != "" {
				result = append(result, d)
			}
		}
	}
	return result, nil
}

type hackerTargetProvider struct{}

func (p *hackerTargetProvider) Name() string                 { return "HackerTarget" }
func (p *hackerTargetProvider) Category() DiscoveryCategory  { return CatReverseIP }
func (p *hackerTargetProvider) QueryType() ProviderQueryType { return QueryIP }
func (p *hackerTargetProvider) SourceBit() DomainSource      { return SourceHackerTarget }
func (p *hackerTargetProvider) MaxRoots() int                { return 0 }
func (p *hackerTargetProvider) Fetch(ctx context.Context, query string, client *http.Client) ([]string, error) {
	u := fmt.Sprintf("https://api.hackertarget.com/reverseiplookup/?q=%s", url.QueryEscape(query))
	req, err := http.NewRequestWithContext(ctx, "GET", u, nil)
	if err != nil {
		return nil, err
	}
	resp, err := client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, &ProviderHTTPError{StatusCode: resp.StatusCode}
	}
	buf := new(bytes.Buffer)
	_, _ = buf.ReadFrom(resp.Body)
	content := buf.String()

	if strings.Contains(content, "API count exceeded") {
		return nil, fmt.Errorf("limit")
	}

	var result []string
	for _, line := range strings.Split(content, "\n") {
		if d := CleanDomain(line); d != "" {
			result = append(result, d)
		}
	}
	return result, nil
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
		pool.Successes.Add(1)
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
	pool.Successes.Add(1)
	return ips, nil
}

func resolveIPv4Cached(ctx context.Context, pool *DNSPool, domain string) ([]string, error) {
	domain = CleanDomain(domain)
	if domain == "" {
		return nil, fmt.Errorf("invalid domain")
	}
	v, err, _ := dnsGroup.Do(domain, func() (interface{}, error) {
		if cached, ok := dnsCache.Get(domain); ok {
			return cached, nil
		}

		ips, err := resolveIPv4DNSCrypt(ctx, pool, domain)
		if err != nil {
			return nil, err
		}

		dnsCache.Put(domain, ips)
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
	binary.BigEndian.PutUint16(payload[0:2], 1)       // HEADER_TABLE_SIZE
	binary.BigEndian.PutUint32(payload[2:6], 65536)
	binary.BigEndian.PutUint16(payload[6:8], 2)       // ENABLE_PUSH
	binary.BigEndian.PutUint32(payload[8:12], 0)
	binary.BigEndian.PutUint16(payload[12:14], 3)     // MAX_CONCURRENT_STREAMS
	binary.BigEndian.PutUint32(payload[14:18], 1000)
	binary.BigEndian.PutUint16(payload[18:20], 4)     // INITIAL_WINDOW_SIZE
	binary.BigEndian.PutUint32(payload[20:24], 6291456)
	binary.BigEndian.PutUint16(payload[24:26], 6)     // MAX_HEADER_LIST_SIZE
	binary.BigEndian.PutUint32(payload[26:30], 262144)
	return buildH2Frame(FrameSettings, 0, 0, payload)
}

func buildWindowUpdateFrame(streamID uint32, increment uint32) []byte {
	payload := make([]byte, 4)
	binary.BigEndian.PutUint32(payload, increment&0x7FFFFFFF)
	return buildH2Frame(FrameWindowUpdate, 0, streamID, payload)
}

func ProbeH2(ctx context.Context, ip, sni string, sources DomainSource, cfg Config) (*Candidate, *ProbeError) {
	cand := &Candidate{
		IP:            ip,
		SNI:           sni,
		Sources:       sources,
		DomainQuality: classifyDomainQuality(sni),
		CDNStatus:     CDNUnknown,
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
			case FrameSettings:
				if streamID != 0 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("SETTINGS on non-zero stream")}
				}
				if flags&FlagAck != 0 {
					cand.H2SettingsAckReceived = true
					cand.SettingsAckCount++
					if length != 0 {
						return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("SETTINGS ACK with non-zero payload")}
					}
					break
				}

				cand.SettingsFramesCount++

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
						return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("duplicate SETTINGS identifier")}
					}
					seenSettings[id] = true

					switch id {
					case 1:
						prof.HeaderTableSize = val
						prof.HasHeaderTableSize = true
						decoder.SetMaxDynamicTableSize(val)
					case 2:
						if val > 1 {
							return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("invalid SETTINGS_ENABLE_PUSH")}
						}
						prof.EnablePush = val
						prof.HasEnablePush = true
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
				if streamID == 0 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("HEADERS frame with stream ID 0")}
				}
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
				if streamID == 0 {
					return cand, &ProbeError{Stage: ProbeStageH2, Err: fmt.Errorf("DATA frame with stream ID 0")}
				}
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
				inc := binary.BigEndian.Uint32(payload) & 0x7fffffff
				if inc == 0 {
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

	return cand, nil
}

func parseHeaders(cand *Candidate, headers []hpack.HeaderField) {
	weakCount := 0
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
					cand.CDNStatus = CDNConfirmed
					cand.CDNProvider = cdn
				}
			}
		}
		if hName == "content-type" {
			cand.ContentType = hVal
		}
		if hName == "location" {
			cand.Location = h.Value
		}

		if hName == "cf-ray" {
			cand.CDNStatus = CDNConfirmed
			cand.CDNProvider = "cloudflare"
		} else if strings.HasPrefix(hName, "x-amz-cf-") || strings.HasPrefix(hName, "x-sucuri-") || strings.HasPrefix(hName, "x-akamai-") {
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
	if cand.CDNStatus == CDNUnknown && weakCount > 0 {
		cand.CDNStatus = CDNLikely
	}
}

// ================= SCORING & ENRICHMENT =================

func scoreH2Profile(c *Candidate) float64 {
	score := 0.0
	if c.H2SettingsReceived {
		score += 4.0
	}

	prof := c.InitialPeerSettings
	if prof.HasMaxConcurrentStreams && prof.MaxConcurrentStreams >= 100 {
		score += 2.0
	}

	if prof.HasInitialWindowSize {
		if prof.InitialWindowSize == 65535 {
			score += 1.0
		} else if prof.InitialWindowSize > 65535 {
			score += 3.0
		}
	}

	if prof.HasMaxFrameSize {
		if prof.MaxFrameSize == 16384 {
			score += 1.0
		} else if prof.MaxFrameSize > 16384 {
			score += 3.0
		}
	}

	if c.H2DataFrames > 0 {
		score += 2.0
	}
	if c.BodyBytes > 0 {
		score += 1.0
	}
	if c.EndStreamSeen {
		score += 1.0
	}

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
	if cand.CDNStatus == CDNConfirmed {
		stats.mu.Lock()
		stats.CDNDropped++
		stats.mu.Unlock()
		return false
	}

	rs := RealityScore{}

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

	sourceCount := 0
	for _, src := range []DomainSource{SourcePTR, SourceCRTSh, SourceCertSpotter, SourceAlienVault, SourceWayback, SourceHackerTarget, SourceSeed, SourceVirusTotal, SourceSecurityTrails, SourceChaos, SourceURLScan} {
		if cand.Sources.Has(src) {
			sourceCount++
		}
	}

	discovery := 0.0
	if cand.Sources.Has(SourcePTR) {
		discovery += 3.0
	}
	if cand.Sources.Has(SourceHackerTarget) {
		discovery += 3.0
	}
	if cand.Sources.Has(SourceCRTSh) {
		discovery += 2.0
	}
	if cand.Sources.Has(SourceCertSpotter) {
		discovery += 2.0
	}
	if cand.Sources.Has(SourceAlienVault) {
		discovery += 1.0
	}
	if cand.Sources.Has(SourceWayback) {
		discovery += 1.0
	}
	if cand.Sources.Has(SourceSeed) {
		discovery += 2.0
	}

	diversity := 0
	if cand.Sources.Has(SourcePTR) || cand.Sources.Has(SourceHackerTarget) || cand.Sources.Has(SourceVirusTotal) {
		diversity++
	}
	if cand.Sources.Has(SourceCRTSh) || cand.Sources.Has(SourceCertSpotter) {
		diversity++
	}
	if cand.Sources.Has(SourceAlienVault) || cand.Sources.Has(SourceWayback) || cand.Sources.Has(SourceSecurityTrails) || cand.Sources.Has(SourceChaos) || cand.Sources.Has(SourceURLScan) {
		diversity++
	}
	if cand.Sources.Has(SourceSeed) {
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
	var mu sync.Mutex
	httpClient := &http.Client{Timeout: 10 * time.Second}

	stats.IPSampled = len(sampledIPs)
	fmt.Printf("[*] Этап 1: OSINT, DNS & Source Provenance Gathering...\n")

	domainSources := make(map[string]DomainSource)
	pairSources := make(map[string]DomainSource)

	addDomainSource := func(d string, src DomainSource) {
		mu.Lock()
		domainSources[d] |= src
		mu.Unlock()
	}

	addPairSource := func(ip, d string, src DomainSource) {
		mu.Lock()
		domainSources[d] |= src
		key := ip + "\x00" + d
		pairSources[key] |= src
		mu.Unlock()
	}

	for _, d := range cfg.Domains {
		if cleaned := CleanDomain(d); cleaned != "" {
			addDomainSource(cleaned, SourceSeed)
		}
	}

	var extProviders []*ProviderRunner
	if !cfg.NoCT {
		extProviders = append(extProviders, NewRunner(&crtShProvider{}, ProviderConfig{Timeout: 6 * time.Second, MaxConcurrent: 1, MinInterval: 12 * time.Second, MaxNames: 100}))
		extProviders = append(extProviders, NewRunner(&certSpotterProvider{}, ProviderConfig{Timeout: 5 * time.Second, MaxConcurrent: 4, MaxNames: 100}))
	}
	if !cfg.NoPassive {
		extProviders = append(extProviders, NewRunner(&alienVaultProvider{}, ProviderConfig{Timeout: 8 * time.Second, MaxConcurrent: 2, MinInterval: 1 * time.Second, MaxNames: 100}))
		extProviders = append(extProviders, NewRunner(&waybackProvider{}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 3, MaxNames: 100}))
	}
	if !cfg.NoReverseIP {
		extProviders = append(extProviders, NewRunner(&hackerTargetProvider{}, ProviderConfig{Timeout: 6 * time.Second, MinInterval: 2 * time.Second, MaxNames: 200}))
	}

	if cfg.VTKey != "" {
		extProviders = append(extProviders, NewRunner(&vtDomainProvider{Key: cfg.VTKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MinInterval: 1 * time.Second, MaxNames: 200}))
		extProviders = append(extProviders, NewRunner(&vtIPProvider{Key: cfg.VTKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MinInterval: 1 * time.Second, MaxNames: 200}))
	}
	if cfg.URLScanKey != "" {
		extProviders = append(extProviders, NewRunner(&urlScanDomainProvider{Key: cfg.URLScanKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MaxNames: 200}))
		extProviders = append(extProviders, NewRunner(&urlScanIPProvider{Key: cfg.URLScanKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MaxNames: 200}))
	}
	if cfg.SecTrailsKey != "" {
		extProviders = append(extProviders, NewRunner(&securityTrailsProvider{Key: cfg.SecTrailsKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MaxNames: 200}))
	}
	if cfg.ChaosKey != "" {
		extProviders = append(extProviders, NewRunner(&chaosProvider{Key: cfg.ChaosKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MaxNames: 200}))
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

	g1a, gCtx1a := errgroup.WithContext(ctx)
	g1a.SetLimit(cfg.Workers)
	for _, ip := range sampledIPs {
		ip := ip
		g1a.Go(func() error {
			if !cfg.NoPTR {
				names, err := resolvePTRDNSCrypt(gCtx1a, pool, ip)
				if err == nil && len(names) > 0 {
					for _, n := range names {
						addPairSource(ip, n, SourcePTR)
					}
					stats.mu.Lock()
					stats.IPWithPTR++
					stats.mu.Unlock()
				}
			}

			for _, p := range ipProviders {
				res := p.Execute(gCtx1a, ip, httpClient)
				for _, d := range res {
					addPairSource(ip, d, p.SourceBit())
				}
			}
			return nil
		})
	}
	_ = g1a.Wait()

	rootProvenance := make(map[string]DomainSource)
	for d, src := range domainSources {
		if r := GetRootDomain(d); r != "" {
			rootProvenance[r] |= src
		}
	}

	type rankedRoot struct {
		domain string
		source DomainSource
	}
	var rootsRanked []rankedRoot
	for r, src := range rootProvenance {
		rootsRanked = append(rootsRanked, rankedRoot{r, src})
	}

	sort.SliceStable(rootsRanked, func(i, j int) bool {
		score := func(s DomainSource) int {
			sc := 0
			if s.Has(SourcePTR) {
				sc += 10
			}
			if s.Has(SourceHackerTarget) {
				sc += 8
			}
			if s.Has(SourceVirusTotal) {
				sc += 6
			}
			if s.Has(SourceSecurityTrails) {
				sc += 5
			}
			if s.Has(SourceChaos) {
				sc += 5
			}
			if s.Has(SourceCRTSh) {
				sc += 4
			}
			if s.Has(SourceCertSpotter) {
				sc += 4
			}
			if s.Has(SourceAlienVault) {
				sc += 3
			}
			if s.Has(SourceURLScan) {
				sc += 3
			}
			if s.Has(SourceWayback) {
				sc += 2
			}
			if s.Has(SourceSeed) {
				sc += 5
			}
			return sc
		}
		si, sj := score(rootsRanked[i].source), score(rootsRanked[j].source)
		if si != sj {
			return si > sj
		}
		return rootsRanked[i].domain < rootsRanked[j].domain
	})

	var roots []string
	for _, r := range rootsRanked {
		roots = append(roots, r.domain)
	}

	if len(roots) > maxDiscoveryRoots {
		roots = roots[:maxDiscoveryRoots]
	}

	if len(domainProviders) > 0 {
		g1b, gCtx1b := errgroup.WithContext(ctx)
		g1b.SetLimit(cfg.Workers)

		for _, p := range domainProviders {
			limit := p.MaxRoots()
			pRoots := roots
			if limit > 0 && len(pRoots) > limit {
				pRoots = pRoots[:limit]
			}

			for _, root := range pRoots {
				root := root
				p := p
				g1b.Go(func() error {
					res := p.Execute(gCtx1b, root, httpClient)
					for _, d := range res {
						addDomainSource(d, p.SourceBit())
					}
					return nil
				})
			}
		}
		_ = g1b.Wait()
	}

	var allDomains []string
	for d := range domainSources {
		allDomains = append(allDomains, d)
	}

	var validPairs []TargetPair
	var pairSeen sync.Map

	if cfg.Mode == ModeDirect && cfg.DirectSNI != "" {
		sni := CleanDomain(cfg.DirectSNI)
		if sni != "" {
			for _, ip := range sampledIPs {
				key := ip + "\x00" + sni
				if _, loaded := pairSeen.LoadOrStore(key, true); !loaded {
					mu.Lock()
					validPairs = append(validPairs, TargetPair{
						IP:      ip,
						SNI:     sni,
						Sources: SourceSeed,
					})
					mu.Unlock()
				}
			}
		}
	}

	var uniqueResolvedIPs sync.Map
	var uniqueTargetIPs sync.Map

	g1c, gCtx1c := errgroup.WithContext(ctx)
	g1c.SetLimit(cfg.Workers)
	for _, dom := range allDomains {
		if cfg.Mode == ModeDirect && dom == CleanDomain(cfg.DirectSNI) {
			continue
		}
		dom := dom
		g1c.Go(func() error {
			stats.mu.Lock()
			stats.DNSQueries++
			stats.mu.Unlock()

			ips, err := resolveIPv4Cached(gCtx1c, pool, dom)

			stats.mu.Lock()
			if err != nil {
				if errors.Is(err, ErrDNSNXDomain) {
					stats.DNSSuccess++
					stats.DNSNXDomain++
				} else {
					stats.DNSFailed++
					var dnsErr *net.DNSError
					if errors.Is(err, context.DeadlineExceeded) || os.IsTimeout(err) {
						stats.DNSTimeout++
					} else if errors.As(err, &dnsErr) {
						if dnsErr.Timeout() {
							stats.DNSTimeout++
						} else if dnsErr.Temporary() {
							stats.DNSTemporary++
						} else {
							stats.DNSOtherErr++
						}
					} else {
						stats.DNSOtherErr++
					}
				}
				stats.mu.Unlock()
				return nil
			}

			if len(ips) == 0 {
				stats.DNSSuccess++
				stats.DNSNoIPv4++
				stats.mu.Unlock()
				return nil
			}

			stats.DNSSuccess++
			stats.DNSResolvedIPs += len(ips)
			stats.mu.Unlock()

			matched := false
			for _, resolvedIP := range ips {
				uniqueResolvedIPs.Store(resolvedIP, struct{}{})

				if ipInRanges(resolvedIP, scanRanges) {
					uniqueTargetIPs.Store(resolvedIP, struct{}{})
					matched = true

					pairKey := resolvedIP + "\x00" + dom
					if _, loaded := pairSeen.LoadOrStore(pairKey, true); !loaded {
						mu.Lock()
						genericMask := domainSources[dom] &^ (SourcePTR | SourceHackerTarget | SourceVirusTotal | SourceURLScan)
						specificMask := pairSources[pairKey]
						finalMask := genericMask | specificMask

						validPairs = append(validPairs, TargetPair{
							IP:      resolvedIP,
							SNI:     dom,
							Sources: finalMask,
						})
						mu.Unlock()
					}
				}
			}
			if matched {
				stats.mu.Lock()
				stats.DNSTargetDomains++
				stats.mu.Unlock()
			}
			return nil
		})
	}
	_ = g1c.Wait()

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

	stats.mu.Lock()
	stats.DNSValidPairs = len(validPairs)
	fmt.Printf("[+] Этап 1 завершен. Подтверждено DNS-пар (IP+SNI): %d\n", stats.DNSValidPairs)
	stats.mu.Unlock()

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
			cand, pErr := ProbeH2(gCtx2, p.IP, p.SNI, p.Sources, cfg)

			tcpOK := pErr == nil || pErr.Stage > ProbeStageTCP
			tlsOK := pErr == nil || pErr.Stage > ProbeStageTLS

			stats.mu.Lock()
			if tcpOK {
				stats.TCPConnected++
			}
			if tlsOK {
				stats.TLSHandshake++
			}
			if pErr != nil && pErr.Stage == ProbeStageTLSValidation {
				stats.TLSValidation++
			}
			if cand != nil && cand.H2HeadersReceived {
				stats.H2HeadersOK++
			}
			if cand != nil && cand.EndStreamSeen {
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

	// IP Clustering: 1 Best SNI per IP
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
			return cluster[i].Timings.TotalProbeLatency() < cluster[j].Timings.TotalProbeLatency()
		})
		clusteredCandidates = append(clusteredCandidates, cluster[0])
	}

	sort.Slice(clusteredCandidates, func(i, j int) bool {
		if clusteredCandidates[i].Score != clusteredCandidates[j].Score {
			return clusteredCandidates[i].Score > clusteredCandidates[j].Score
		}
		return clusteredCandidates[i].Timings.TotalProbeLatency() < clusteredCandidates[j].Timings.TotalProbeLatency()
	})

	stats.mu.Lock()
	fmt.Println("\n===================================================================================================================")
	fmt.Println("                                   ТЕЛЕМЕТРИЯ СКАНИРОВАНИЯ (PIPELINE STATS)")
	fmt.Println("===================================================================================================================")
	fmt.Printf("[*] IP отобрано для пула:      %d\n", stats.IPSampled)
	fmt.Printf("[*] IP с чистым PTR (Hosts):   %d\n", stats.IPWithPTR)

	fmt.Println("\nSNI/Hostname Discovery Providers:")

	categories := map[DiscoveryCategory][]string{}
	catMap := make(map[string]DiscoveryCategory)

	providersInfo := []struct {
		n string
		c DiscoveryCategory
	}{
		{"crt.sh", CatCertificate}, {"CertSpotter", CatCertificate},
		{"AlienVault", CatPassiveDNS}, {"WaybackMachine", CatArchive}, {"HackerTarget", CatReverseIP},
		{"VirusTotal", CatReverseIP}, {"URLScan", CatArchive}, {"SecurityTrails", CatPassiveDNS}, {"Chaos", CatPassiveDNS},
	}
	for _, p := range providersInfo {
		catMap[p.n] = p.c
	}

	for name := range stats.ProviderStats {
		cat := catMap[name]
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
			p := stats.ProviderStats[name]
			fmt.Printf("    %-15s : Попыток: %d (Успех: %d, Ошибок: %d, Таймаутов: %d) -> Найдено имён: %d\n", name, p.Attempts, p.Success, p.Failed, p.Timeouts, p.Names)
		}
	}

	fmt.Println("\n[DNSCrypt Pool Telemetry]")
	fmt.Printf("  DNS Queries:                 %d (Успех: %d, Ошибок: %d, Ретраи: %d)\n", pool.Queries.Load(), pool.Successes.Load(), pool.Failures.Load(), pool.Retries.Load())
	
	fmt.Printf("\n[*] Общие DNS Lookups:         %d (Успех: %d, Ошибок: %d)\n", stats.DNSQueries, stats.DNSSuccess, stats.DNSFailed)
	fmt.Printf("    Детали DNS успехов:        Resolved IPs (Total): %d, NXDOMAIN: %d, NoIPv4: %d\n", stats.DNSResolvedIPs, stats.DNSNXDomain, stats.DNSNoIPv4)
	fmt.Printf("    Детали DNS ошибок:         Timeout: %d, Temporary: %d, Other: %d\n", stats.DNSTimeout, stats.DNSTemporary, stats.DNSOtherErr)
	fmt.Printf("[*] DNS Unique IPs:            %d\n", uniqueResolvedCount)
	fmt.Printf("[*] DNS Unique Target IPs:     %d\n", uniqueTargetCount)
	fmt.Printf("[*] DNS доменов с Target IP:   %d\n", stats.DNSTargetDomains)
	fmt.Printf("[*] Подтверждено DNS-пар:      %d\n", stats.DNSValidPairs)
	fmt.Printf("[*] Успешных TCP соединений:   %d\n", stats.TCPConnected)
	fmt.Printf("[*] Успешных TLS хэндшейков:   %d\n", stats.TLSHandshake)
	fmt.Printf("[*] Ошибок валидации TLS:      %d\n", stats.TLSValidation)
	fmt.Printf("[*] С откликом H2 Headers:     %d\n", stats.H2HeadersOK)
	fmt.Printf("[*] Финальных IP-кластеров:    %d\n", len(clusteredCandidates))
	stats.mu.Unlock()

	return clusteredCandidates
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

	flag.BoolVar(&cfg.NoPTR, "no-ptr", false, "Disable Reverse DNS PTR lookups")
	flag.BoolVar(&cfg.NoCT, "no-ct", false, "Disable Certificate Transparency lookups (crt.sh/CertSpotter)")
	flag.BoolVar(&cfg.NoPassive, "no-passive", false, "Disable Passive DNS OSINT (AlienVault, Wayback)")
	flag.BoolVar(&cfg.NoReverseIP, "no-reverse-ip", false, "Disable Reverse IP lookups (HackerTarget)")

	// Интегрированные дефолтные API ключи:
	flag.StringVar(&cfg.VTKey, "vt-key", "dea2ba0b84a3d88ea20a5fb14165e94d170cbe369529dbc57119757e04f1efb5", "VirusTotal API Key")
	flag.StringVar(&cfg.URLScanKey, "urlscan-key", "01a032ae-681d-7718-821b-c6fd33aa11a7", "URLScan.io API Key")
	flag.StringVar(&cfg.ChaosKey, "chaos-key", "e3c91ed9-2f79-4147-807f-43dd150003e4", "ProjectDiscovery Chaos API Key")
	flag.StringVar(&cfg.SecTrailsKey, "sectrails-key", "", "SecurityTrails API Key")

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
	if cfg.Mode == ModeDirect && len(cfg.CIDRs) == 0 {
		log.Fatal("[-] Direct mode requires at least one IPv4 CIDR")
	}

	if cfg.MaxIPs == -1 {
		fmt.Printf("[!] ВНИМАНИЕ: Выбран режим полного сканирования (--max-ips=-1). Для крупных ASN это может занять очень много времени!\n")
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
	dnsPool.sortByRTT()
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
				log.Fatal("[-] Target IP is not present in ASN announced prefixes. Use --scan-all-asn to force full scan.")
			}
			samplingCIDRs = []string{localPrefix}
		} else {
			samplingCIDRs = cidrs
		}

		samplingRanges := MergeCIDRs(samplingCIDRs)
		sampledIPs := SampleIPs(samplingRanges, cfg.MaxIPs, cfg.Seed)

		dnsRanges := MergeCIDRs(cidrs)

		fmt.Printf("[*] Целевой IP:             %s\n", vpsQueryIP)
		fmt.Printf("[*] Announcing ASN:        AS%d\n", cfg.TargetASN)
		if !cfg.ScanEntireASN {
			fmt.Printf("[*] Фокус на IPv4 prefix:    %s (DNS-валидация по всем %d префиксам ASN)\n", localPrefix, len(cidrs))
		} else {
			fmt.Printf("[*] Фокус на все префиксы:   %d подсетей ASN\n", len(cidrs))
		}
		fmt.Printf("[*] Страна сервера:          %s (MaxMind GeoIP)\n", cfg.TargetCountry)
		fmt.Printf("[*] Подготовлено %d IP адресов для OSINT-сэмплинга. Запуск...\n", len(sampledIPs))

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
	fmt.Printf("TLS: %.0f/10 | CERT: %.0f/20 | H2: %.0f/20 | SERVER: %.0f/10 | HTTP: %.0f/10 | DSCOV: %.0f/10 | LATENCY: TCP %dms, TLS %dms, H2 %dms\n",
		best.RealityScore.TLSQuality, best.RealityScore.Certificate, best.RealityScore.H2Profile, best.RealityScore.ServerProfile, best.RealityScore.HTTPBehavior, best.RealityScore.DiscoveryScore,
		best.Timings.TCP.Milliseconds(), best.Timings.TLS.Milliseconds(), best.Timings.H2Headers.Milliseconds())
	fmt.Printf("-------------------------------------------------------------------------------------------------------------------\n")
	fmt.Printf("BASE SCORE: %.1f | PENALTY: -%.1f | FINAL REALITY SCORE: %.1f/90 (HTTP: %d, Total Probe Latency: %d ms)\n",
		best.RealityScore.Total, best.DomainPenalty, best.Score, best.HTTPStatus, best.Timings.TotalProbeLatency().Milliseconds())
}
