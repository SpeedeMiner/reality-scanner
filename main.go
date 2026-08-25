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

	mdns "github.com/miekg/dns"
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
	MaxHostsPer24        = 254
	MaxSampled24         = 4

	providerMaxAttempts    = 3
	providerCBThreshold    = 10
	providerCBCooldown     = 2 * time.Minute
	provider429CBCooldown  = 5 * time.Minute
	providerMaxRetryAfter  = 60 * time.Second
)

var (
	cdnStrong = []string{"cloudflare", "fastly", "akamai", "ddos-guard", "qrator", "sucuri"}
	cdnWeak   = []string{"x-cache", "x-served-by", "x-edge"}

	bannedTLDs = map[string]bool{
		"crl": true, "ocsp": true, "der": true, "crt": true, "cer": true, "pem": true,
		"arpa": true, "local": true, "internal": true, "invalid": true, "example": true, "test": true, "localhost": true,
	}

	junkTLDs = []string{".xyz", ".top", ".site", ".fun", ".online", ".space", ".pw", ".cc", ".icu", ".click", ".win", ".bid", ".date"}
	dynDNS   = []string{"duckdns.org", "mooo.com", "ddns.net", "freeddns.org", "crabdance.com", "eu.org", "cloudns.cc", "hopto.org", "zapto.org", "sytes.net", "dyn.com", "no-ip.org"}

	domainRe = regexp.MustCompile(`^[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(\.[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+$`)
	numRe    = regexp.MustCompile(`(?i)(^|\.)\d+\.[a-z]{2,}$`)

	ErrDNSNXDomain    = errors.New("NXDOMAIN")
	ErrProviderNoData = errors.New("provider returned no data")

	uaRng *rand.Rand
	uaMu  sync.Mutex
)

type Config struct {
	Mode             Mode
	Workers          int
	DNSWorkers       int
	MaxIPs           int
	IPOSINTLimit     int
	DomainOSINTLimit int
	TCPTimeoutMs     int
	TLSTimeoutMs     int
	H2ReadTimeoutMs  int
	H2WriteTimeoutMs int
	Seed             int64
	TargetASN        string
	TargetCountry    string
	TargetIP         string
	DirectSNI        string
	CIDRs            []string
	Domains          []string
	NoPTR            bool
	NoCT             bool
	NoPassive        bool
	NoReverseIP      bool
	NoActiveTLS      bool

	VTKey      string
	URLScanKey string
	ChaosKey   string
}

// ================= EVIDENCE & PROVENANCE =================

type DomainSource uint32

const (
	SourceSeed DomainSource = 1 << iota
	SourcePTR
	SourceDirectTLS
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
	if s.Has(SourcePTR) { score += 10 }
	if s.Has(SourceHackerTarget) { score += 8 }
	if s.Has(SourceShodan) { score += 8 }
	if s.Has(SourceVirusTotalIP) || s.Has(SourceVirusTotalDomain) { score += 6 }
	if s.Has(SourceChaos) { score += 5 }
	if s.Has(SourceCRTSh) || s.Has(SourceCertSpotter) { score += 4 }
	if s.Has(SourceAlienVault) || s.Has(SourceURLScan) { score += 3 }
	if s.Has(SourceAnubis) || s.Has(SourceThreatMiner) || s.Has(SourceHTDomain) { score += 3 }
	if s.Has(SourceWayback) { score += 2 }
	if s.Has(SourceSeed) { score += 5 }
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

func (s *DiscoveryState) GetCombinedEvidence(ip, dom string) Evidence {
	s.mu.RLock()
	defer s.mu.RUnlock()
	dEv := s.domainEvidence[dom]
	pEv := s.pairEvidence[ip+"\x00"+dom]
	return Evidence{
		Direct:    dEv.Direct | pEv.Direct,
		Inherited: dEv.Inherited | pEv.Inherited,
	}
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

	HPACKErrors   bool
	MissingStatus bool
	ReadTimeout   bool
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

type TotalAllocationStats struct {
	TotalRoots            int
	AssignedRoots         int
	OverlappedAssignments int
	UnassignedRoots       int
	PrimaryAssignments    map[string]int
	OverlapAssignments    map[string]int
}

type PipelineStats struct {
	mu                    sync.Mutex
	IPSampled             int
	ActiveProbes          int
	UniqueDomains         int

	// DNS
	DNSQueries            int
	DNSSuccess            int
	DNSFailed             int
	DNSNXDomain           int
	DNSTimeout            int
	DNSTemporary          int
	DNSOtherErr           int
	DNSNoIPv4             int
	DNSResolvedIPs        int
	DNSUniqueResolvedIPs  int
	DNSUniqueTargetIPs    int
	DNSTargetRangeMatches int
	DNSTargetDomains      int
	DNSValidPairs         int

	// PTR
	PTRQueriesSent int
	PTRFound       int
	PTRErrors      int

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
	H2NoALPN          int
	H2ProtocolOK      int
	H2TimeoutNoFrames int
	H2ConnectionReset int
	H2BrokenPipe      int
	H2BadRequest      int
	H2GoAway          int
	H2EOF             int
	H2TLSAlerts       int
	H2OtherErrs       int

	H2HeadersOK   int
	H2Timeouts    int
	H2HPACKErrors int

	H2StatusOK      int
	H2InvalidStatus int
	EndStreamOK     int

	// Final
	ScoreRejected      int
	CandidatesAccepted int

	IPWithPTR       int
	IPWithDirectTLS int

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

func (s *PipelineStats) SnapshotAndPrint(clustered int, ds *DiscoveryState) {
	s.mu.Lock()
	allocStats := s.Alloc
	stageC := s.StageC
	localStats := make(map[string]ProviderStats)
	for k, v := range s.ProviderStats {
		localStats[k] = *v
	}
	s.mu.Unlock()

	ds.mu.RLock()
	droppedGlobal := ds.droppedDomainsByGlobalLimit
	droppedPairs := ds.droppedValidPairs
	ds.mu.RUnlock()

	fmt.Println("\n===================================================================================================================")
	fmt.Println("                                   ТЕЛЕМЕТРИЯ СКАНИРОВАНИЯ (PIPELINE STATS)")
	fmt.Println("===================================================================================================================")
	fmt.Printf("[*] IP отобрано для пула:      %d\n", s.IPSampled)
	fmt.Printf("[*] IP с чистым PTR (Hosts):   %d\n", s.PTRFound)
	fmt.Printf("[*] IP с сертификатами (TLS):  %d\n", s.IPWithDirectTLS)
	fmt.Printf("[*] Найдено уник. доменов:     %d\n\n", s.UniqueDomains)

	if stageC.TotalRoots > 0 {
		fmt.Printf("[*] STAGE C: Domain OSINT Pipeline Stats:\n")
		fmt.Printf("    Total Roots:           %d\n", stageC.TotalRoots)
		fmt.Printf("    Assigned (Primary+Ov): %d\n", stageC.Assigned)
		fmt.Printf("    Completed (Unique):    %d\n", stageC.CompletedRoots)
		fmt.Printf("    Deferred (CB Open):    %d\n", stageC.DeferredRoots)
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
		fmt.Println()
	}

	fmt.Printf("[*] Logical DNS Lookups (ECS): %d (Успех: %d, Ошибок: %d)\n", s.DNSQueries, s.DNSSuccess, s.DNSFailed)
	fmt.Printf("    Детали DNS успехов:        Resolved IPs: %d, NXDOMAIN: %d, NoIPv4: %d\n", s.DNSResolvedIPs, s.DNSNXDomain, s.DNSNoIPv4)
	fmt.Printf("    Детали DNS ошибок:         Timeout: %d, Temporary: %d, Other: %d\n", s.DNSTimeout, s.DNSTemporary, s.DNSOtherErr)
	fmt.Printf("    Детали PTR запросов:       Sent: %d, Found: %d, Err: %d\n", s.PTRQueriesSent, s.PTRFound, s.PTRErrors)
	fmt.Printf("[*] Target Range IP Matches:   %d\n", s.DNSTargetRangeMatches)
	fmt.Printf("[*] DNS доменов с Target IP:   %d\n", s.DNSTargetDomains)
	fmt.Printf("[*] Подтверждено DNS-пар:      %d\n", s.DNSValidPairs)
	if droppedPairs > 0 {
		fmt.Printf("[!] DNS-пар отброшено лимитом (LimitValidPairs=%d): %d\n", LimitValidPairs, droppedPairs)
	}

	fmt.Printf("\n[*] Анализ Stage E (Строгая Воронка):\n")
	fmt.Printf("    1. Целей на входе (DNS):       %d\n", s.DNSValidPairs)
	fmt.Printf("    2. Успешный TCP коннект:       %d (Потери: Timeouts=%d, Refused=%d, Other=%d)\n", s.TCPConnected, s.TCPTimeouts, s.TCPRefused, s.TCPOtherErrs)
	fmt.Printf("    3. Успешный TLS хэндшейк:      %d (Потери: Timeouts=%d, HandshakeFail=%d, UnrecName=%d, ConnReset=%d, EOF=%d, NoCert=%d, CertFail=%d, Other=%d)\n", s.TLSHandshake, s.TLSTimeouts, s.TLSHandshakeFailure, s.TLSUnrecognizedName, s.TLSConnectionReset, s.TLSEOF, s.NoPeerCertificates, s.TLSValidationFailures, s.TLSOtherErrs)
	fmt.Printf("    4. Подтверждён H2 протокол:    %d (Потери: TimeoutNoFrames=%d, ConnReset=%d, BrokenPipe=%d, BadRequest/HTTP1=%d, GoAway=%d, EOF=%d, TLSAlerts=%d, Other=%d)\n", s.H2ProtocolOK, s.H2TimeoutNoFrames, s.H2ConnectionReset, s.H2BrokenPipe, s.H2BadRequest, s.H2GoAway, s.H2EOF, s.H2TLSAlerts, s.H2OtherErrs)
	fmt.Printf("    5. Получены H2 Headers:        %d (Потери: TimeoutsNoHeaders=%d, HPACK_Err=%d)\n", s.H2HeadersOK, s.H2Timeouts, s.H2HPACKErrors)
	fmt.Printf("    6. Валидный HTTP Status:       %d (Потери: Invalid/Zero Status=%d)\n", s.H2StatusOK, s.H2InvalidStatus)
	fmt.Printf("    7. Финальные Кандидаты:        %d (Отклонено по Score=%d)\n", s.CandidatesAccepted, s.ScoreRejected)
	
	fmt.Printf("\n    *  Инфо: H2 целей без ALPN 'h2': %d\n", s.H2NoALPN)
	fmt.Printf("    *  Уникальных IP-кластеров:    %d\n", clustered)
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

// ================= ECS DNS RESOLVER =================

var ecsResolvers = []string{
	"8.8.8.8:53",
	"8.8.4.4:53",
	"208.67.222.222:53",
}

func resolveHostECS(ctx context.Context, domain, vpsIP string, rtCaches *RuntimeCaches) ([]string, error) {
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

		req := new(mdns.Msg)
		req.Id = mdns.Id()
		req.SetQuestion(mdns.Fqdn(domain), mdns.TypeA)
		req.RecursionDesired = true

		if vpsIP != "" {
			ip := net.ParseIP(vpsIP).To4()
			if ip != nil {
				opt := new(mdns.OPT)
				opt.Hdr.Name = "."
				opt.Hdr.Rrtype = mdns.TypeOPT
				e := new(mdns.EDNS0_SUBNET)
				e.Code = mdns.EDNS0SUBNET
				e.Family = 1
				e.SourceNetmask = 24
				e.SourceScope = 0
				e.Address = ip
				opt.Option = append(opt.Option, e)
				req.Extra = append(req.Extra, opt)
			}
		}

		var lastErr error
		client := &mdns.Client{Net: "udp", Timeout: 2500 * time.Millisecond}
		startIdx := rand.Intn(len(ecsResolvers))

		for i := 0; i < 3; i++ {
			if ctx.Err() != nil {
				return nil, ctx.Err()
			}

			resAddr := ecsResolvers[(startIdx+i)%len(ecsResolvers)]

			type res struct {
				r *mdns.Msg
				e error
			}
			ch := make(chan res, 1)
			go func() {
				resp, _, err := client.Exchange(req, resAddr)
				ch <- res{resp, err}
			}()

			var resp *mdns.Msg
			var errEx error
			select {
			case <-ctx.Done():
				return nil, ctx.Err()
			case r := <-ch:
				resp, errEx = r.r, r.e
			}

			if errEx != nil {
				lastErr = errEx
				continue
			}
			if resp.Rcode == mdns.RcodeNameError {
				rtCaches.DNSCache.Put(domain, &DNSCacheEntry{NXDomain: true}, 10*time.Second)
				return nil, ErrDNSNXDomain
			}
			if resp.Rcode != mdns.RcodeSuccess {
				lastErr = fmt.Errorf("rcode: %d", resp.Rcode)
				continue
			}

			seen := make(map[string]struct{})
			var ips []string
			for _, ans := range resp.Answer {
				if a, ok := ans.(*mdns.A); ok {
					ipStr := a.A.String()
					if _, exists := seen[ipStr]; !exists {
						seen[ipStr] = struct{}{}
						ips = append(ips, ipStr)
					}
				}
			}
			rtCaches.DNSCache.Put(domain, &DNSCacheEntry{IPs: ips}, 10*time.Second)
			return ips, nil
		}
		return nil, lastErr
	})

	if err != nil {
		return nil, err
	}
	return v.([]string), nil
}

// ================= API HELPERS (RIPE & IP-API) =================

func getPublicIP(targetIP string) (string, error) {
	if targetIP != "" {
		ip := net.ParseIP(targetIP)
		if ip != nil && ip.To4() != nil {
			return ip.To4().String(), nil
		}
		return "", fmt.Errorf("invalid target IPv4 format: %s", targetIP)
	}
	urls := []string{"https://api.ipify.org", "https://ifconfig.me/ip", "https://icanhazip.com"}
	client := &http.Client{Timeout: 4 * time.Second}
	for _, u := range urls {
		resp, err := client.Get(u)
		if err == nil {
			defer resp.Body.Close()
			ipBytes, _ := io.ReadAll(resp.Body)
			ipStr := strings.TrimSpace(string(ipBytes))
			ip := net.ParseIP(ipStr)
			if ip != nil && ip.To4() != nil {
				return ip.To4().String(), nil
			}
		}
	}
	return "", fmt.Errorf("could not determine public IPv4. Please provide it manually via -vps-ip")
}

func getCountry(ip string) string {
	client := &http.Client{Timeout: 4 * time.Second}
	resp, err := client.Get(fmt.Sprintf("http://ip-api.com/json/%s?fields=countryCode", ip))
	if err != nil {
		return ""
	}
	defer resp.Body.Close()

	if resp.StatusCode == 200 {
		var result struct {
			CountryCode string `json:"countryCode"`
		}
		if err := json.NewDecoder(resp.Body).Decode(&result); err == nil {
			return strings.ToUpper(result.CountryCode)
		}
	}
	return "UNKNOWN"
}

func getASNAndPrefix(ip string) (string, string) {
	var asn, prefix string
	client := &http.Client{Timeout: 6 * time.Second}

	resp, err := client.Get(fmt.Sprintf("https://stat.ripe.net/data/network-info/data.json?resource=%s", ip))
	if err == nil {
		var result struct {
			Data struct {
				ASNs   []interface{} `json:"asns"`
				Prefix string        `json:"prefix"`
			} `json:"data"`
		}
		json.NewDecoder(resp.Body).Decode(&result)
		resp.Body.Close()

		if len(result.Data.ASNs) > 0 {
			asn = fmt.Sprintf("%v", result.Data.ASNs[0])
			if !strings.HasPrefix(strings.ToUpper(asn), "AS") {
				asn = "AS" + asn
			}
		}
		prefix = result.Data.Prefix
	}

	if asn == "" {
		resp2, err2 := client.Get(fmt.Sprintf("http://ip-api.com/json/%s?fields=as", ip))
		if err2 == nil {
			var res2 struct {
				AS string `json:"as"`
			}
			json.NewDecoder(resp2.Body).Decode(&res2)
			resp2.Body.Close()

			if res2.AS != "" {
				parts := strings.Split(res2.AS, " ")
				if len(parts) > 0 {
					asn = strings.ToUpper(parts[0])
					if !strings.HasPrefix(asn, "AS") {
						asn = "AS" + asn
					}
				}
			}
		}
	}

	if asn == "" {
		asn = "UNKNOWN_ASN"
	}

	if prefix == "" {
		parsedIP := net.ParseIP(ip)
		if parsedIP != nil {
			parsedIP = parsedIP.To4()
			if parsedIP != nil {
				prefix = fmt.Sprintf("%d.%d.%d.0/24", parsedIP[0], parsedIP[1], parsedIP[2])
			}
		}
	}

	return asn, prefix
}

func getPrefixes(asn string) []string {
	if asn == "UNKNOWN_ASN" {
		return nil
	}

	client := &http.Client{Timeout: 6 * time.Second}
	resp, err := client.Get(fmt.Sprintf("https://stat.ripe.net/data/announced-prefixes/data.json?resource=%s", asn))
	if err != nil {
		return nil
	}
	defer resp.Body.Close()
	var result struct {
		Data struct {
			Prefixes []struct {
				Prefix string `json:"prefix"`
			} `json:"prefixes"`
		} `json:"data"`
	}
	json.NewDecoder(resp.Body).Decode(&result)
	var prefixes []string
	for _, p := range result.Data.Prefixes {
		if !strings.Contains(p.Prefix, ":") {
			prefixes = append(prefixes, p.Prefix)
		}
	}
	return prefixes
}

func filterPrefixesByCountry(prefixes []string, targetCountry string) []string {
	if targetCountry == "" || len(prefixes) == 0 || targetCountry == "UNKNOWN" {
		return prefixes
	}
	targetCountry = strings.ToUpper(targetCountry)

	type QueryItem struct {
		Query string `json:"query"`
	}

	queryToPrefix := make(map[string]string)
	var allQueries []QueryItem

	for _, p := range prefixes {
		ip, _, err := net.ParseCIDR(p)
		if err == nil {
			qIP := ip.String()
			queryToPrefix[qIP] = p
			allQueries = append(allQueries, QueryItem{Query: qIP})
		}
	}

	var matched []string
	batchSize := 100

	for i := 0; i < len(allQueries); i += batchSize {
		end := i + batchSize
		if end > len(allQueries) {
			end = len(allQueries)
		}
		batch := allQueries[i:end]

		reqBody, _ := json.Marshal(batch)
		resp, err := http.Post("http://ip-api.com/batch?fields=query,countryCode,status", "application/json", bytes.NewBuffer(reqBody))
		if err != nil {
			continue
		}

		var resData []struct {
			Query       string `json:"query"`
			CountryCode string `json:"countryCode"`
			Status      string `json:"status"`
		}
		json.NewDecoder(resp.Body).Decode(&resData)
		resp.Body.Close()

		for _, item := range resData {
			if item.Status == "success" && strings.ToUpper(item.CountryCode) == targetCountry {
				if pref, ok := queryToPrefix[item.Query]; ok {
					matched = append(matched, pref)
				}
			}
		}
	}
	return matched
}

// ================= UTILS =================

func gcd(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

func CleanDomain(d string) string {
	d = strings.ToLower(strings.TrimSpace(strings.TrimPrefix(d, "*.")))
	parts := strings.Split(d, ".")
	if len(parts) < 2 {
		return ""
	}
	tld := parts[len(parts)-1]
	if bannedTLDs[tld] {
		return ""
	}
	if strings.ContainsAny(d, " \t\r\n/\\:*?\"'<>|#%&={}~`!@$^()+[]") {
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

func isProviderBlocked(p *ProviderRunner) bool {
	p.mu.Lock()
	defer p.mu.Unlock()
	return !p.cbUntil.IsZero() && time.Now().Before(p.cbUntil)
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
		if isProviderBlocked(r) {
			r.mu.Lock()
			cbUntil := r.cbUntil
			r.mu.Unlock()
			pipeStats.recordProviderStat(statName, r.Category(), StatSkipped, false, 0, 0, 0, 0, 0, 0, fmt.Sprintf("circuit-open until %s", cbUntil.Format(time.RFC3339)), 0)
			return ExecResult{nil, StatSkipped}, nil
		}

		if errWait := r.waitRate(ctx); errWait != nil {
			pipeStats.recordProviderStat(statName, r.Category(), StatWaitCanceled, false, 0, 0, 0, 0, 0, 0, fmt.Sprintf("wait cancelled: %v", errWait), 0)
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
		r.cbFailures = 0
		r.cbUntil = time.Time{}
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
	u := fmt.Sprintf("https://jldc.me/anubis/subdomains/%s", url.QueryEscape(query))
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
	setBrowserHeaders(req)
	req.Header.Add("Authorization", p.Key)
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

func activeProbeIP(ctx context.Context, ip string, timeout time.Duration, noPTR bool, noTLS bool, pipeStats *PipelineStats) []TargetPair {
	var pairs []TargetPair
	sourceMap := make(map[string]DomainSource)
	var allDoms []string

	addDomain := func(d string, src DomainSource) {
		d = CleanDomain(d)
		if d == "" {
			return
		}
		if _, exists := sourceMap[d]; !exists {
			allDoms = append(allDoms, d)
		}
		sourceMap[d] |= src
	}

	// 1. Быстрый системный PTR
	if !noPTR {
		pipeStats.mu.Lock()
		pipeStats.PTRQueriesSent++
		pipeStats.mu.Unlock()

		names, err := net.LookupAddr(ip)
		if err == nil && len(names) > 0 {
			pipeStats.mu.Lock()
			pipeStats.PTRFound++
			pipeStats.mu.Unlock()

			for _, name := range names {
				ptrDomain := CleanDomain(strings.TrimSuffix(name, "."))
				if ptrDomain != "" {
					addDomain(ptrDomain, SourcePTR)

					if !noTLS {
						cDoms, _ := extractDomainsFromTLS(ctx, ip, ptrDomain, timeout)
						for _, cd := range cDoms {
							addDomain(cd, SourceDirectTLS)
						}
					}
				}
			}
		} else if err != nil {
			pipeStats.mu.Lock()
			pipeStats.PTRErrors++
			pipeStats.mu.Unlock()
		}
	}

	// 2. Если PTR пуст, обращаемся к OSINT
	if len(sourceMap) < 5 {
		osints := getOSINTDomains(ip)
		for _, osint := range osints {
			osint = CleanDomain(osint)
			if osint == "" {
				continue
			}
			addDomain(osint, SourceSeed)

			if !noTLS {
				cDoms, _ := extractDomainsFromTLS(ctx, ip, osint, timeout)
				if len(cDoms) > 0 {
					for _, cd := range cDoms {
						addDomain(cd, SourceDirectTLS)
					}
					break
				}
			}
		}
	}

	uniqueDoms := uniqueStrings(allDoms)
	sort.Slice(uniqueDoms, func(i, j int) bool {
		srcI := sourceMap[uniqueDoms[i]]
		srcJ := sourceMap[uniqueDoms[j]]

		weight := func(s DomainSource) int {
			w := 0
			if s.Has(SourceDirectTLS) {
				w += 3
			}
			if s.Has(SourcePTR) {
				w += 2
			}
			if s.Has(SourceSeed) {
				w += 1
			}
			return w
		}

		wi, wj := weight(srcI), weight(srcJ)
		if wi != wj {
			return wi > wj
		}
		return uniqueDoms[i] < uniqueDoms[j]
	})

	if len(uniqueDoms) > 25 {
		uniqueDoms = uniqueDoms[:25]
	}

	for _, d := range uniqueDoms {
		pairs = append(pairs, TargetPair{IP: ip, SNI: d, Evidence: Evidence{Direct: sourceMap[d]}})
	}

	return pairs
}

// ================= MAIN PIPELINE =================

func RunPipeline(ctx context.Context, cfg Config, sampledIPs []string, scanRanges []ipRange, vpsIP string) []Candidate {
	pipeStats := NewPipelineStats()
	pipeStats.mu.Lock()
	pipeStats.IPSampled = len(sampledIPs)
	pipeStats.mu.Unlock()

	ds := NewDiscoveryState()
	rtCaches := NewRuntimeCaches()

	var allPairs []TargetPair
	var pairsMu sync.Mutex

	fmt.Printf("[*] STAGE A: Stealth Discovery (PTR -> TLS & OSINT -> TLS)...\n")
	gA, gCtxA := errgroup.WithContext(ctx)
	gA.SetLimit(cfg.Workers)

	for _, ip := range sampledIPs {
		ip := ip
		gA.Go(func() error {
			if gCtxA.Err() != nil {
				return gCtxA.Err()
			}
			pipeStats.mu.Lock()
			pipeStats.ActiveProbes++
			pipeStats.mu.Unlock()

			pairs := activeProbeIP(gCtxA, ip, time.Duration(cfg.TLSTimeoutMs)*time.Millisecond, cfg.NoPTR, cfg.NoActiveTLS, pipeStats)
			if len(pairs) > 0 {
				pairsMu.Lock()
				allPairs = append(allPairs, pairs...)
				pairsMu.Unlock()

				ds.mu.Lock()
				for _, p := range pairs {
					if _, exists := ds.domainsToResolve[p.SNI]; !exists {
						ds.domainsToResolve[p.SNI] = struct{}{}
					}
					key := p.IP + "\x00" + p.SNI
					ev := ds.pairEvidence[key]
					ev.Direct |= p.Evidence.Direct
					ds.pairEvidence[key] = ev
				}
				ds.mu.Unlock()
			}
			return nil
		})
	}
	if err := gA.Wait(); err != nil || ctx.Err() != nil {
		fmt.Println("[-] Выполнение прервано (Stage A).")
		return nil
	}

	for _, d := range cfg.Domains {
		if cleaned := CleanDomain(d); cleaned != "" {
			ds.mu.Lock()
			ds.domainsToResolve[cleaned] = struct{}{}
			ds.mu.Unlock()
		}
	}

	pipeStats.mu.Lock()
	pipeStats.UniqueDomains = len(ds.domainsToResolve)
	pipeStats.mu.Unlock()

	fmt.Printf("[+] Этап A завершен. Найдено уникальных доменов: %d (Пар IP+SNI: %d)\n", len(ds.domainsToResolve), len(allPairs))

	rootProvenance := make(map[string]DomainSource)
	ds.mu.RLock()
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

	var extProviders []*ProviderRunner
	if !cfg.NoCT {
		extProviders = append(extProviders, NewRunner(&crtShProvider{}, ProviderConfig{Timeout: 6 * time.Second, MaxConcurrent: 1, MinInterval: 1 * time.Second, MaxNames: 1000, MaxRoots: 50, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&certSpotterProvider{}, ProviderConfig{Timeout: 5 * time.Second, MaxConcurrent: 2, MinInterval: 500 * time.Millisecond, MaxNames: 1000, MaxRoots: 100, MaxPages: 3}))
	}
	if !cfg.NoPassive {
		extProviders = append(extProviders, NewRunner(&alienVaultProvider{}, ProviderConfig{Timeout: 8 * time.Second, MaxConcurrent: 1, MinInterval: 1 * time.Second, MaxNames: 1000, MaxRoots: 150, MaxPages: 3}))
		extProviders = append(extProviders, NewRunner(&waybackProvider{}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MinInterval: 500 * time.Millisecond, MaxNames: 10000, MaxRoots: 150, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&anubisProvider{}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MinInterval: 500 * time.Millisecond, MaxNames: 1000, MaxRoots: 150, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&threatMinerProvider{}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 1, MinInterval: 1 * time.Second, MaxNames: 1000, MaxRoots: 100, MaxPages: 1}))
		extProviders = append(extProviders, NewRunner(&hackerTargetHostSearchProvider{}, ProviderConfig{Timeout: 6 * time.Second, MaxConcurrent: 1, MinInterval: 1 * time.Second, MaxNames: 1000, MaxRoots: 50, MaxPages: 1}))
	}
	if cfg.VTKey != "" {
		extProviders = append(extProviders, NewRunner(&vtDomainProvider{Key: cfg.VTKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MinInterval: 1 * time.Second, MaxNames: 2000, MaxRoots: 100, MaxPages: 3}))
	}
	if cfg.URLScanKey != "" {
		extProviders = append(extProviders, NewRunner(&urlScanDomainProvider{Key: cfg.URLScanKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 2, MaxNames: 10000, MaxRoots: 100, MaxPages: 5}))
	}
	if cfg.ChaosKey != "" {
		extProviders = append(extProviders, NewRunner(&chaosProvider{Key: cfg.ChaosKey}, ProviderConfig{Timeout: 10 * time.Second, MaxConcurrent: 1, MinInterval: 1 * time.Second, MaxNames: 2000, MaxRoots: 100, MaxPages: 1}))
	}

	if len(rootsRanked) > 0 {
		fmt.Printf("[*] STAGE C: Domain OSINT (Distributing %d Roots)...\n", len(rootsRanked))
		httpClient := &http.Client{Timeout: 15 * time.Second}
		RunStageC(ctx, rootsRanked, extProviders, cfg, httpClient, pipeStats, rtCaches, ds, rootProvenance)
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
					validPairs = append(validPairs, TargetPair{
						IP:       ip,
						SNI:      sni,
						Evidence: Evidence{Direct: SourceSeed},
					})
				}
			}
		}
	}

	fmt.Printf("[*] STAGE D: ECS DNS Validation (%d Domains)...\n", len(allDomains))
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

			// Используем ECS с пробросом IP VPS для корректного гео-определения CDN
			ips, err := resolveHostECS(gCtxD, dom, vpsIP, rtCaches)

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
						ev := ds.GetCombinedEvidence(resolvedIP, dom)
						pairsMu.Lock()
						if len(validPairs) < LimitValidPairs {
							validPairs = append(validPairs, TargetPair{
								IP:       resolvedIP,
								SNI:      dom,
								Evidence: ev,
							})
						}
						pairsMu.Unlock()
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

	fmt.Printf("[+] Stage D Завершён.\n")
	fmt.Printf("    - DNS Queries: %d (Success: %d, Failed: %d)\n", pipeStats.DNSQueries, pipeStats.DNSSuccess, pipeStats.DNSFailed)
	fmt.Printf("    - NXDOMAIN: %d, Timeout: %d, OtherErr: %d, NoIPv4: %d\n", pipeStats.DNSNXDomain, pipeStats.DNSTimeout, pipeStats.DNSOtherErr, pipeStats.DNSNoIPv4)
	fmt.Printf("    - Подтверждено DNS-пар (IP+SNI): %d\n", pipeStats.DNSValidPairs)
	pipeStats.mu.Unlock()

	if len(validPairs) == 0 {
		return nil
	}

	fmt.Printf("[*] STAGE E: Active HTTP/2 Scanning & TLS Enrichment (%d targets)...\n", len(validPairs))
	var candidates []Candidate
	var candMu sync.Mutex

	h2jobs := make(chan TargetPair, len(validPairs))
	var wgE sync.WaitGroup

	tcpTimeout := time.Duration(cfg.TCPTimeoutMs) * time.Millisecond
	if tcpTimeout < 3000*time.Millisecond {
		tcpTimeout = 3000 * time.Millisecond
	}
	cfg.TCPTimeoutMs = int(tcpTimeout.Milliseconds())

	tlsTimeout := time.Duration(cfg.TLSTimeoutMs) * time.Millisecond
	if tlsTimeout < 3000*time.Millisecond {
		tlsTimeout = 3000 * time.Millisecond
	}
	cfg.TLSTimeoutMs = int(tlsTimeout.Milliseconds())

	for i := 0; i < cfg.Workers; i++ {
		wgE.Add(1)
		go func() {
			defer wgE.Done()
			for p := range h2jobs {
				if ctx.Err() != nil {
					return
				}

				cand, pErr := ProbeH2(ctx, p.IP, p.SNI, p.Evidence.Direct, cfg)

				pipeStats.mu.Lock()

				if pErr != nil && pErr.Stage == ProbeStageTCP {
					errStr := pErr.Err.Error()
					if os.IsTimeout(pErr.Err) || strings.Contains(errStr, "deadline") || strings.Contains(errStr, "i/o timeout") {
						pipeStats.TCPTimeouts++
					} else if strings.Contains(errStr, "refused") {
						pipeStats.TCPRefused++
					} else {
						pipeStats.TCPOtherErrs++
					}
					pipeStats.mu.Unlock()
					continue
				}
				pipeStats.TCPConnected++

				if pErr != nil && (pErr.Stage == ProbeStageTLS || pErr.Stage == ProbeStageTLSValidation) {
					errStr := pErr.Err.Error()
					if os.IsTimeout(pErr.Err) || strings.Contains(errStr, "deadline") || strings.Contains(errStr, "i/o timeout") {
						pipeStats.TLSTimeouts++
					} else if strings.Contains(errStr, "no peer certificates") {
						pipeStats.NoPeerCertificates++
					} else if strings.Contains(errStr, "handshake failure") {
						pipeStats.TLSHandshakeFailure++
					} else if strings.Contains(errStr, "unrecognized name") {
						pipeStats.TLSUnrecognizedName++
					} else if strings.Contains(errStr, "connection reset") {
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

				if cand != nil && cand.ALPN != "h2" {
					pipeStats.H2NoALPN++
				}

				if pErr != nil {
					errStr := pErr.Err.Error()
					if os.IsTimeout(pErr.Err) || strings.Contains(errStr, "deadline") || strings.Contains(errStr, "i/o timeout") || (cand != nil && cand.ReadTimeout) {
						pipeStats.H2TimeoutNoFrames++
					} else if strings.Contains(errStr, "connection reset") {
						pipeStats.H2ConnectionReset++
					} else if strings.Contains(errStr, "broken pipe") {
						pipeStats.H2BrokenPipe++
					} else if strings.Contains(errStr, "400 Bad Request") || strings.Contains(errStr, "HTTP/1.1") {
						pipeStats.H2BadRequest++
					} else if cand != nil && cand.GoAwaySeen {
						pipeStats.H2GoAway++
					} else if errors.Is(pErr.Err, io.EOF) || strings.Contains(errStr, "EOF") {
						pipeStats.H2EOF++
					} else if strings.Contains(errStr, "tls:") {
						pipeStats.H2TLSAlerts++
					} else {
						pipeStats.H2OtherErrs++
					}
					pipeStats.mu.Unlock()
					continue
				}

				if cand == nil || !cand.H2ProtocolConfirmed {
					pipeStats.H2OtherErrs++
					pipeStats.mu.Unlock()
					continue
				}
				pipeStats.H2ProtocolOK++

				if !cand.H2HeadersReceived {
					if cand.ReadTimeout {
						pipeStats.H2Timeouts++
					} else if cand.HPACKErrors {
						pipeStats.H2HPACKErrors++
					} else {
						pipeStats.H2OtherErrs++
					}
					pipeStats.mu.Unlock()
					continue
				}
				pipeStats.H2HeadersOK++

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

				if !validateAndEnrich(cand, cfg, pipeStats) {
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

	sort.Slice(candidates, func(i, j int) bool {
		if candidates[i].Score != candidates[j].Score {
			return candidates[i].Score > candidates[j].Score
		}
		if candidates[i].Timings.TotalProbeLatency() != candidates[j].Timings.TotalProbeLatency() {
			return candidates[i].Timings.TotalProbeLatency() < candidates[j].Timings.TotalProbeLatency()
		}
		return candidates[i].SNI < candidates[j].SNI
	})

	pipeStats.SnapshotAndPrint(len(ipClusters), ds)

	return candidates
}

// ================= MAIN =================

func main() {
	uaRng = rand.New(rand.NewSource(time.Now().UnixNano()))

	cfg := Config{}
	var modeStr, domainsStr string

	flag.StringVar(&modeStr, "mode", "autonomous", "autonomous | direct")
	flag.IntVar(&cfg.Workers, "w", 1000, "Worker pool size for TLS/TCP probing")
	flag.IntVar(&cfg.DNSWorkers, "dns-workers", 128, "Worker pool size for DNS validation")
	flag.IntVar(&cfg.MaxIPs, "max-ips", 0, "Limit for IP sampling (0 = no hard limit, will scan all generated IPs)")
	flag.IntVar(&cfg.TCPTimeoutMs, "tcp-timeout", 3000, "TCP timeout ms")
	flag.IntVar(&cfg.TLSTimeoutMs, "tls-timeout", 3000, "TLS timeout ms")
	flag.IntVar(&cfg.H2ReadTimeoutMs, "h2-read", 3000, "H2 Read timeout ms")
	flag.IntVar(&cfg.H2WriteTimeoutMs, "h2-write", 2000, "H2 Write timeout ms")
	flag.Int64Var(&cfg.Seed, "seed", time.Now().UnixNano(), "Random seed")
	flag.StringVar(&cfg.TargetCountry, "c", "", "Hard Filter: Target Country Code")
	flag.StringVar(&cfg.TargetASN, "asn", "", "Hard Filter: Target ASN constraint (e.g., AS12345)")
	flag.StringVar(&cfg.TargetIP, "vps-ip", "", "IP сервера для поиска сети (запуск с ПК)")
	flag.StringVar(&cfg.DirectSNI, "sni", "", "Fallback SNI for Direct mode")
	flag.StringVar(&domainsStr, "domains", "", "Comma-separated seed domains for OSINT")

	flag.BoolVar(&cfg.NoPTR, "no-ptr", false, "Disable Reverse DNS PTR lookups")
	flag.BoolVar(&cfg.NoCT, "no-ct", false, "Disable Certificate Transparency OSINT")
	flag.BoolVar(&cfg.NoPassive, "no-passive", false, "Disable Passive DNS OSINT")
	flag.BoolVar(&cfg.NoReverseIP, "no-reverse-ip", false, "Disable Reverse IP OSINT")
	flag.BoolVar(&cfg.NoActiveTLS, "no-tls-probe", false, "Disable direct IP TLS certificate extraction")

	flag.StringVar(&cfg.VTKey, "vt-key", "dea2ba0b84a3d88ea20a5fb14165e94d170cbe369529dbc57119757e04f1efb5", "VirusTotal API Key")
	flag.StringVar(&cfg.URLScanKey, "urlscan-key", "01a032ae-681d-7718-821b-c6fd33aa11a7", "URLScan.io API Key")
	flag.StringVar(&cfg.ChaosKey, "chaos-key", "e3c91ed9-2f79-4147-807f-43dd150003e4", "ProjectDiscovery Chaos API Key")

	flag.Parse()

	if cfg.Seed != 0 {
		uaMu.Lock()
		uaRng = rand.New(rand.NewSource(cfg.Seed))
		uaMu.Unlock()
	}

	if cfg.Workers < 1 {
		cfg.Workers = 1
	}
	if cfg.DNSWorkers < 1 {
		cfg.DNSWorkers = 1
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

	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer cancel()

	var vpsQueryIP string

	if cfg.Mode == ModeAuto {
		ip, err := getPublicIP(cfg.TargetIP)
		if err != nil {
			log.Fatalf("[-] %v\n", err)
		}
		vpsQueryIP = ip

		if cfg.TargetASN == "" || cfg.TargetCountry == "" {
			asn, _ := getASNAndPrefix(vpsQueryIP)
			country := getCountry(vpsQueryIP)
			if cfg.TargetASN == "" {
				cfg.TargetASN = asn
			}
			if cfg.TargetCountry == "" {
				cfg.TargetCountry = country
			}
		}
	}

	var results []Candidate

	if cfg.Mode == ModeAuto {
		allPrefixes := getPrefixes(cfg.TargetASN)
		if len(allPrefixes) == 0 {
			log.Fatalf("[-] Failed to fetch CIDRs for %s", cfg.TargetASN)
		}

		var targetPrefixes []string
		if cfg.TargetCountry != "" && cfg.TargetCountry != "UNKNOWN" {
			targetPrefixes = filterPrefixesByCountry(allPrefixes, cfg.TargetCountry)

			vpsIPObj := net.ParseIP(vpsQueryIP)
			foundLocal := false
			var localPrefix string
			for _, c := range allPrefixes {
				_, ipnet, _ := net.ParseCIDR(c)
				if ipnet != nil && ipnet.Contains(vpsIPObj) {
					localPrefix = c
					break
				}
			}

			for _, p := range targetPrefixes {
				if p == localPrefix {
					foundLocal = true
					break
				}
			}
			if !foundLocal && localPrefix != "" {
				targetPrefixes = append([]string{localPrefix}, targetPrefixes...)
			}
		} else {
			targetPrefixes = allPrefixes
		}

		sampledIPs := generateIPs(targetPrefixes, cfg.MaxIPs)
		dnsRanges := MergeCIDRs(allPrefixes)

		fmt.Printf("[*] Целевой IP:             %s\n", vpsQueryIP)
		fmt.Printf("[*] Announcing ASN:         %s\n", cfg.TargetASN)
		fmt.Printf("[*] Фокус на префиксы:       %d подсетей ASN (С учетом страны)\n", len(targetPrefixes))
		fmt.Printf("[*] Страна сервера:          %s (ip-api)\n", cfg.TargetCountry)
		fmt.Printf("[*] ВНИМАНИЕ: DNS валидация проверяет все %d префиксов ASN для расширения покрытия.\n", len(allPrefixes))
		fmt.Printf("[*] Подготовлено %d IP адресов для сэмплинга. Запуск...\n\n", len(sampledIPs))

		results = RunPipeline(ctx, cfg, sampledIPs, dnsRanges)

	} else if cfg.Mode == ModeDirect {
		merged := MergeCIDRs(cfg.CIDRs)
		sampledIPs := generateIPs(cfg.CIDRs, cfg.MaxIPs)
		fmt.Printf("[*] Direct Mode: Подготовлено %d IP адресов. Запуск...\n", len(sampledIPs))
		results = RunPipeline(ctx, cfg, sampledIPs, merged)
	}

	if len(results) == 0 {
		fmt.Println("\n[-] Подходящих кандидатов не найдено.")
		return
	}

	fmt.Printf("\n[+] Найдено валидных HTTP/2 целей (без обрезки по IP): %d\n\n", len(results))
	fmt.Printf("%-36s | %-15s | %-5s | %-4s | %-4s | %-4s | %-4s | %-4s | %-5s | %-6s | %4s %4s %4s\n",
		"Цель (SNI)", "IP адрес", "SCORE", "TLS", "CERT", "H2", "SRV", "HTTP", "DSCOV", "STATUS", "TCP", "TLS", "H2")
	fmt.Println(strings.Repeat("-", 126))

	for _, r := range results {
		rs := r.RealityScore
		scoreStr := fmt.Sprintf("%.1f", r.Score)

		fmt.Printf("%-36s | %-15s | %-5s | %2.0f   | %2.0f   | %2.0f   | %2.0f   | %2.0f   | %2.0f    | %-6d | %3d %3d %3d\n",
			limitStr(r.SNI, 36), r.IP, scoreStr, rs.TLSQuality, rs.Certificate, rs.H2Profile, rs.ServerProfile, rs.HTTPBehavior, rs.DiscoveryScore, r.HTTPStatus,
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
