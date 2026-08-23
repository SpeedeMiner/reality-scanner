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

	maxProviderNamesPerRoot = 100
	maxDiscoveryRoots       = 30
)

var (
	cdnStrong = []string{"cloudflare", "fastly", "akamai", "ddos-guard", "qrator", "sucuri"}
	cdnWeak   = []string{"x-cache", "x-served-by", "x-edge"}
	junkTLDs  = []string{".xyz", ".top", ".site", ".fun", ".online", ".space", ".pw", ".cc", ".icu", ".click", ".win", ".bid", ".date"}
	dynDNS    = []string{"duckdns.org", "mooo.com", "ddns.net", "freeddns.org", "crabdance.com", "eu.org", "cloudns.cc", "hopto.org", "zapto.org", "sytes.net", "dyn.com", "no-ip.org"}

	domainRe    = regexp.MustCompile(`^[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(\.[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+$`)
	numRe       = regexp.MustCompile(`(?i)(^|\.)\d+\.[a-z]{2,}$`)
	uuidLabelRe = regexp.MustCompile(`(?i)^[a-f0-9]{8}-[a-f0-9]{4}-[1-5][a-f0-9]{3}-[89ab][a-f0-9]{3}-[a-f0-9]{12}$`)
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
	Score             float64
	DomainPenalty     float64
	RealityScore      RealityScore
	CertChainValid    bool
	EndStreamSeen     bool
	StreamReset       bool
	GoAwaySeen        bool
	Sources           DomainSource
	DomainQuality     string

	CertIssuer            string
	CertSubject           string
	CertSANCount          int
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
	mu            sync.Mutex
	IPSampled     int
	IPWithPTR     int
	DNSValidPairs int
	TCPConnected  int
	TLSHandshake  int
	TLSValidation int
	H2HeadersOK   int
	EndStreamOK   int

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

func rankAndLimitDomains(domains []string, max int) []string {
	unique := uniqueDomains(domains)
	if max <= 0 || len(unique) == 0 {
		return nil
	}

	type rankedDomain struct {
		domain string
		score  int
	}

	ranked := make([]rankedDomain, 0, len(unique))
	scoreDomain := func(d string) int {
		s := 0
		l := len(d)
		switch {
		case l <= 15:
			s += 20
		case l <= 25:
			s += 15
		case l <= 35:
			s += 10
		default:
			s += 5
		}
		switch {
		case strings.HasPrefix(d, "www."):
			s += 20
		case strings.HasPrefix(d, "api."):
			s += 15
		case strings.HasPrefix(d, "remote."):
			s += 10
		case strings.HasPrefix(d, "web."):
			s += 10
		case strings.HasPrefix(d, "app."):
			s += 8
		}
		for _, prefix := range []string{
			"autodiscover.", "autoconfig.", "cpanel.", "webmail.",
			"panel.", "admin.", "ns1.", "ns2.", "ns3.", "ns4.",
			"smtp.", "imap.", "pop.", "mx.", "vpn.",
		} {
			if strings.HasPrefix(d, prefix) {
				s -= 15
				break
			}
		}
		labels := strings.Split(d, ".")
		if len(labels) > 0 {
			first := labels[0]
			if uuidLabelRe.MatchString(first) {
				s -= 20
			}
		}
		return s
	}

	for _, d := range unique {
		ranked = append(ranked, rankedDomain{domain: d, score: scoreDomain(d)})
	}

	sort.SliceStable(ranked, func(i, j int) bool {
		if ranked[i].score != ranked[j].score {
			return ranked[i].score > ranked[j].score
		}
		return len(ranked[i].domain) < len(ranked[j].domain)
	})

	if len(ranked) > max {
		ranked = ranked[:max]
	}

	result := make([]string, 0, len(ranked))
	for _, r := range ranked {
		result = append(result, r.domain)
	}
	return result
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
				if r.cbFailures >= 5 {
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

		cleanRes := uniqueDomains(res)
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
// Implementations
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
func (p *hackerTargetProvider) MaxRoots() int                { return 0 } // IP Provider
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
	if now.Before(cert.NotBefore) || now.After(cert.NotAfter) {
		return cand, &ProbeError{Stage: ProbeStageTLSValidation, Err: fmt.Errorf("certificate expired")}
	}

	opts := x509.VerifyOptions{
		DNSName:       sni,
		Roots:         nil,
		Intermediates: x509.NewCertPool(),
	}
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
					cand.CDNConfidence += 3
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
			cand.CDNConfidence += 3
			if cand.CDNProvider == "" {
				cand.CDNProvider = "cloudflare"
			}
		} else if strings.HasPrefix(hName, "x-amz-cf-") || strings.HasPrefix(hName, "x-sucuri-") || strings.HasPrefix(hName, "x-akamai-") {
			cand.CDNConfidence += 2
			if cand.CDNProvider == "" {
				cand.CDNProvider = "headers"
			}
		}

		for _, cdnH := range cdnWeak {
			if hName == cdnH {
				cand.CDNConfidence += 1
			}
		}
	}
}

// ================= SCORING & ENRICHMENT =================

func scorePeerSettings(prof PeerSettingsProfile) float64 {
	score := 0.0
	if prof.HasInitialWindowSize {
		if prof.InitialWindowSize == 65535 {
			score += 0.5
		} else if prof.InitialWindowSize > 65535 {
			score += 1.0
		}
	}
	if prof.HasMaxFrameSize {
		if prof.MaxFrameSize == 16384 {
			score += 0.5
		} else if prof.MaxFrameSize > 16384 {
			score += 1.0
		}
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
	if cand.CDNConfidence >= 3 {
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

	sourceCount := 0
	for _, src := range []DomainSource{SourcePTR, SourceCRTSh, SourceCertSpotter, SourceAlienVault, SourceWayback, SourceHackerTarget, SourceSeed} {
		if cand.Sources.Has(src) {
			sourceCount++
		}
	}
	
	discovery := 0.0
	if cand.Sources.Has(SourcePTR) {
		discovery += 2.0
	}
	if cand.Sources.Has(SourceHackerTarget) {
		discovery += 2.0
	}
	if cand.Sources.Has(SourceCRTSh) {
		discovery += 2.0
	}
	if cand.Sources.Has(SourceCertSpotter) {
		discovery += 2.0
	}
	if cand.Sources.Has(SourceAlienVault) {
		discovery += 2.0
	}
	if cand.Sources.Has(SourceWayback) {
		discovery += 1.0
	}
	if cand.Sources.Has(SourceSeed) {
		discovery += 1.0
	}

	if sourceCount >= 2 {
		discovery += 2.0
	}
	if sourceCount >= 3 {
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
	if cand.DomainQuality == "JunkTLD" {
		scorePenalty = 15.0
	} else if cand.DomainQuality == "DynDNS" {
		scorePenalty = 25.0
	} else if cand.DomainQuality == "Numeric" {
		scorePenalty = 30.0
	}

	cand.RealityScore = rs
	cand.DomainPenalty = scorePenalty
	cand.Score = rs.Total - scorePenalty

	return cand.Score >= 0
}

func RunPipeline(ctx context.Context, cfg Config, sampledIPs []string, asnDB, countryDB *geoip2.Reader) []Candidate {
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
				names, err := net.DefaultResolver.LookupAddr(gCtx1a, ip)
				if err == nil {
					found := false
					for _, n := range names {
						if d := CleanDomain(n); d != "" {
							addPairSource(ip, d, SourcePTR)
							found = true
						}
					}
					if found {
						stats.mu.Lock()
						stats.IPWithPTR++
						stats.mu.Unlock()
					}
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
				sc += 3
			}
			if s.Has(SourceHackerTarget) {
				sc += 3
			}
			if s.Has(SourceCRTSh) {
				sc += 3
			}
			if s.Has(SourceCertSpotter) {
				sc += 3
			}
			if s.Has(SourceAlienVault) {
				sc += 2
			}
			if s.Has(SourceWayback) {
				sc += 1
			}
			if s.Has(SourceSeed) {
				sc += 2
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

	sampledIPsSet := make(map[string]struct{}, len(sampledIPs))
	for _, ip := range sampledIPs {
		sampledIPsSet[ip] = struct{}{}
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

	g1c, gCtx1c := errgroup.WithContext(ctx)
	g1c.SetLimit(cfg.Workers)
	for _, dom := range allDomains {
		if cfg.Mode == ModeDirect && dom == CleanDomain(cfg.DirectSNI) {
			continue
		}
		dom := dom
		g1c.Go(func() error {
			ips, err := resolveIPv4Cached(gCtx1c, dom)
			if err == nil {
				for _, resolvedIP := range ips {
					if _, ok := sampledIPsSet[resolvedIP]; ok {
						pairKey := resolvedIP + "\x00" + dom
						if _, loaded := pairSeen.LoadOrStore(pairKey, true); !loaded {
							mu.Lock()
							genericMask := domainSources[dom] &^ (SourcePTR | SourceHackerTarget)
							specificMask := pairSources[pairKey]
							finalMask := genericMask | specificMask

							validPairs = append(validPairs, TargetPair{
								IP:      resolvedIP,
								SNI:     dom,
								Sources: finalMask,
							})
							if len(validPairs) <= 50 {
								fmt.Printf("  [+] DNS Match: %s -> %s\n", dom, resolvedIP)
							}
							mu.Unlock()
						}
					}
				}
			}
			return nil
		})
	}
	_ = g1c.Wait()

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

	sort.Slice(candidates, func(i, j int) bool {
		if candidates[i].Score != candidates[j].Score {
			return candidates[i].Score > candidates[j].Score
		}
		return candidates[i].Timings.TotalProbeLatency() < candidates[j].Timings.TotalProbeLatency()
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
	
	flag.BoolVar(&cfg.NoPTR, "no-ptr", false, "Disable Reverse DNS PTR lookups")
	flag.BoolVar(&cfg.NoCT, "no-ct", false, "Disable Certificate Transparency lookups (crt.sh/CertSpotter)")
	flag.BoolVar(&cfg.NoPassive, "no-passive", false, "Disable Passive DNS OSINT (AlienVault, Wayback)")
	flag.BoolVar(&cfg.NoReverseIP, "no-reverse-ip", false, "Disable Reverse IP lookups (HackerTarget)")
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
	if cfg.DirectSNI != "" {
		if cleaned := CleanDomain(cfg.DirectSNI); cleaned != "" {
			cfg.Domains = append(cfg.Domains, cleaned)
		}
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

	fmt.Println("\nSNI/Hostname Discovery Providers:")
	
	categories := map[DiscoveryCategory][]string{}
	
	stats.mu.Lock()
	for name, p := range stats.ProviderStats {
		categories[p.Category] = append(categories[p.Category], name)
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
	stats.mu.Unlock()

	fmt.Printf("\n[*] Подтверждено DNS-пар:      %d\n", stats.DNSValidPairs)
	fmt.Printf("[*] Успешных TCP соединений:   %d\n", stats.TCPConnected)
	fmt.Printf("[*] Успешных TLS хэндшейков:   %d\n", stats.TLSHandshake)
	fmt.Printf("[*] Ошибок валидации TLS:      %d\n", stats.TLSValidation)
	fmt.Printf("[*] С откликом H2 Headers:     %d\n", stats.H2HeadersOK)
	fmt.Printf("[*] Финальных кандидатов:      %d\n", len(results))

	if len(results) == 0 {
		fmt.Println("\n[-] Подходящих кандидатов не найдено.")
		return
	}

	fmt.Printf("\n[+] Найдено валидных HTTP/2 целей: %d\n\n", len(results))
	fmt.Printf("%-32.32s | %-15.15s | %-5s | %-4s | %-4s | %-4s | %-4s | %-4s | %-5s | %-6s | %-7s\n",
		"Цель (SNI)", "IP адрес", "SCORE", "TLS", "CERT", "H2", "SRV", "HTTP", "DSCOV", "STATUS", "PROBE")
	fmt.Println(strings.Repeat("-", 126))

	for _, r := range results {
		rs := r.RealityScore
		rttStr := fmt.Sprintf("%d ms", r.Timings.TotalProbeLatency().Milliseconds())
		scoreStr := fmt.Sprintf("%.1f", r.Score)

		fmt.Printf("%-32.32s | %-15.15s | %-5s | %2.0f   | %2.0f   | %2.0f   | %2.0f   | %2.0f   | %2.0f    | %-6d | %s\n",
			r.SNI, r.IP, scoreStr, rs.TLSQuality, rs.Certificate, rs.H2Profile, rs.ServerProfile, rs.HTTPBehavior, rs.DiscoveryScore, r.HTTPStatus, rttStr)
	}

	best := results[0]
	fmt.Println("\n===================================================================================================================")
	fmt.Println("                                   РЕКОМЕНДУЕМАЯ КОНФИГУРАЦИЯ DEST/SNI")
	fmt.Println("===================================================================================================================")
	fmt.Printf("\"dest\": \"%s:443\",\n", best.SNI)
	fmt.Printf("\"serverNames\": [\n  \"%s\"\n]\n\n", best.SNI)
	fmt.Printf("Подробности лучшего кандидата:\n")
	fmt.Printf("TLS: %.0f/20 | CERT: %.0f/20 | H2: %.0f/20 | SERVER: %.0f/10 | HTTP: %.0f/10 | DSCOV: %.0f/10 | PROBE: %.0f/10\n",
		best.RealityScore.TLSQuality, best.RealityScore.Certificate, best.RealityScore.H2Profile, best.RealityScore.ServerProfile, best.RealityScore.HTTPBehavior, best.RealityScore.DiscoveryScore, best.RealityScore.Latency)
	fmt.Printf("-------------------------------------------------------------------------------------------------------------------\n")
	fmt.Printf("BASE SCORE: %.1f | PENALTY: -%.1f | FINAL REALITY SCORE: %.1f/100 (HTTP: %d, Total Probe Latency: %d ms)\n",
		best.RealityScore.Total, best.DomainPenalty, best.Score, best.HTTPStatus, best.Timings.TotalProbeLatency().Milliseconds())
}
