package main

import (
	"bytes"
	"context"
	"crypto/tls"
	"encoding/binary"
	"encoding/json"
	"flag"
	"fmt"
	"log"
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
	"golang.org/x/sync/errgroup"
)

// ================= CONFIG & CONSTANTS =================

type Mode string

const (
	ModePassive Mode = "passive"
	ModeHybrid  Mode = "hybrid"
	ModeDirect  Mode = "direct"
	ModeAuto    Mode = "autonomous"

	FrameData         = 0x00
	FrameHeaders      = 0x01
	FrameRSTStream    = 0x03
	FrameSettings     = 0x04
	FrameGoAway       = 0x07
	FrameContinuation = 0x09

	FlagEndStream  = 0x01
	FlagEndHeaders = 0x04
	FlagAck        = 0x01

	SettingMaxFrameSize = 0x05
)

var (
	cdnServers = []string{"cloudflare", "fastly", "akamai", "ddos-guard", "qrator", "sucuri"}
	cdnHeaders = []string{"x-cache", "x-served-by", "cf-ray"}
	domainRe   = regexp.MustCompile(`^[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(\.[a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+$`)
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
	DirectSNI        string
	CIDRs            []string
	Domains          []string
	GeoIPPath        string
	ASNPath          string
}

// ================= MODELS =================

type Timings struct {
	TCP  time.Duration
	TLS  time.Duration
	TTFB time.Duration
}

func (t Timings) Total() time.Duration { return t.TCP + t.TLS + t.TTFB }

type Candidate struct {
	IP             string
	SNI            string
	ALPN           string
	HTTPStatus     int
	DataBytes      int
	Server         string
	Timings        Timings
	Sources        map[string]bool
	ASN            uint
	Country        string
	CDNConfidence  int
	Score          float64
	CertValidDates bool
	CertSANs       []string
}

// ================= UTILS & DEDUP =================

type Deduplicator struct {
	seen sync.Map
}

func (d *Deduplicator) IsNew(key string) bool {
	_, loaded := d.seen.LoadOrStore(key, true)
	return !loaded
}

func CleanDomain(d string) string {
	d = strings.ToLower(strings.TrimSpace(d))
	d = strings.TrimPrefix(d, "*.")
	d = strings.TrimSuffix(d, ".")
	if d == "localhost" || strings.HasPrefix(d, "localhost.") { return "" }
	if !domainRe.MatchString(d) { return "" }
	return d
}

// ================= AUTO DETECTION & RIPE STAT API =================

type ipAPIResp struct {
	Status      string `json:"status"`
	CountryCode string `json:"countryCode"`
	AS          string `json:"as"`
	Query       string `json:"query"`
}

func autoDetectVPS() (uint, string, string, error) {
	client := &http.Client{Timeout: 5 * time.Second}
	resp, err := client.Get("http://ip-api.com/json/?fields=status,countryCode,as,query")
	if err != nil { return 0, "", "", err }
	defer resp.Body.Close()

	var geo ipAPIResp
	if err := json.NewDecoder(resp.Body).Decode(&geo); err != nil { return 0, "", "", err }
	if geo.Status != "success" { return 0, "", "", fmt.Errorf("api returned non-success status") }

	var asn uint
	parts := strings.Fields(geo.AS)
	if len(parts) > 0 && strings.HasPrefix(strings.ToUpper(parts[0]), "AS") {
		fmt.Sscanf(strings.ToUpper(parts[0]), "AS%d", &asn)
	}
	return asn, geo.CountryCode, geo.Query, nil
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
	if err != nil { return nil, err }
	defer resp.Body.Close()

	var stat RipeStatResponse
	if err := json.NewDecoder(resp.Body).Decode(&stat); err != nil { return nil, err }

	var cidrs []string
	for _, p := range stat.Data.Prefixes {
		if !strings.Contains(p.Prefix, ":") { cidrs = append(cidrs, p.Prefix) }
	}
	return cidrs, nil
}

// ================= CIDR MERGE & SAMPLER =================

type ipRange struct {
	start uint32
	end   uint32
}

func MergeCIDRs(cidrs []string) []ipRange {
	var ranges []ipRange
	for _, c := range cidrs {
		_, ipnet, err := net.ParseCIDR(c)
		if err != nil { continue }
		ones, bits := ipnet.Mask.Size()
		if bits != 32 { continue }
		startInt := binary.BigEndian.Uint32(ipnet.IP)
		count := uint32(1) << (32 - ones)
		ranges = append(ranges, ipRange{start: startInt, end: startInt + count - 1})
	}

	if len(ranges) == 0 { return nil }
	sort.Slice(ranges, func(i, j int) bool { return ranges[i].start < ranges[j].start })
	
	var merged []ipRange
	for _, r := range ranges {
		if len(merged) == 0 {
			merged = append(merged, r)
			continue
		}
		last := &merged[len(merged)-1]
		if r.start <= last.end+1 {
			if r.end > last.end { last.end = r.end }
		} else {
			merged = append(merged, r)
		}
	}
	return merged
}

func SampleIPs(blocks []ipRange, maxIPs int, seed int64) []string {
	var totalIPs uint64
	for _, b := range blocks { totalIPs += uint64(b.end - b.start + 1) }
	if totalIPs == 0 { return nil }

	sampleSize := uint64(maxIPs)
	if sampleSize > totalIPs { sampleSize = totalIPs }

	rng := rand.New(rand.NewSource(seed))
	startIdx := rng.Uint64() % totalIPs
	var step uint64 = 1
	if totalIPs > 1 { step = (rng.Uint64() % (totalIPs - 1)) | 1 }

	var result []string
	currIdx := startIdx

	for i := uint64(0); i < sampleSize; i++ {
		var offset uint64 = currIdx
		for _, b := range blocks {
			count := uint64(b.end - b.start + 1)
			if offset < count {
				targetInt := b.start + uint32(offset)
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

// ================= OSINT FRAMEWORK =================

type TargetQuery struct {
	IPs     []string
	Domains []string
}

type DomainEvidence struct {
	Domain string
	Source string
}

type OSINTSource interface {
	Name() string
	SupportsIP() bool
	SupportsDomain() bool
	Search(ctx context.Context, q TargetQuery) ([]DomainEvidence, error)
}

type CrtShSource struct {
	client *http.Client
}
func (s *CrtShSource) Name() string           { return "Crt.sh" }
func (s *CrtShSource) SupportsIP() bool       { return false }
func (s *CrtShSource) SupportsDomain() bool   { return true }
func (s *CrtShSource) Search(ctx context.Context, q TargetQuery) ([]DomainEvidence, error) {
	var results []DomainEvidence
	for _, domain := range q.Domains {
		select { case <-ctx.Done(): return nil, ctx.Err(); default: }
		
		urlStr := fmt.Sprintf("https://crt.sh/?q=%%25.%s&output=json", url.QueryEscape(domain))
		req, _ := http.NewRequestWithContext(ctx, "GET", urlStr, nil)
		resp, err := s.client.Do(req)
		if err != nil || resp.StatusCode != 200 { 
			if resp != nil { resp.Body.Close() }
			continue 
		}
		
		var ctRes []struct { NameValue string `json:"name_value"` }
		if err := json.NewDecoder(resp.Body).Decode(&ctRes); err == nil {
			for _, rec := range ctRes {
				for _, part := range strings.Split(rec.NameValue, "\n") {
					if d := CleanDomain(part); d != "" {
						results = append(results, DomainEvidence{Domain: d, Source: s.Name()})
					}
				}
			}
		}
		resp.Body.Close()
	}
	return results, nil
}

type PTRSource struct{}
func (s *PTRSource) Name() string           { return "PTR" }
func (s *PTRSource) SupportsIP() bool       { return true }
func (s *PTRSource) SupportsDomain() bool   { return false }
func (s *PTRSource) Search(ctx context.Context, q TargetQuery) ([]DomainEvidence, error) {
	var results []DomainEvidence
	for _, ip := range q.IPs {
		names, err := net.DefaultResolver.LookupAddr(ctx, ip)
		if err == nil {
			for _, n := range names {
				if d := CleanDomain(n); d != "" {
					results = append(results, DomainEvidence{Domain: d, Source: s.Name()})
				}
			}
		}
	}
	return results, nil
}

func GatherOSINT(ctx context.Context, q TargetQuery, sources []OSINTSource) []DomainEvidence {
	var mu sync.Mutex
	evidenceMap := make(map[string]map[string]bool)
	g, gCtx := errgroup.WithContext(ctx)

	for _, src := range sources {
		s := src
		if (len(q.IPs) > 0 && !s.SupportsIP()) || (len(q.Domains) > 0 && !s.SupportsDomain()) { continue }
		g.Go(func() error {
			evidences, err := s.Search(gCtx, q)
			if err == nil {
				mu.Lock()
				for _, ev := range evidences {
					if evidenceMap[ev.Domain] == nil { evidenceMap[ev.Domain] = make(map[string]bool) }
					evidenceMap[ev.Domain][ev.Source] = true
				}
				mu.Unlock()
			}
			return nil
		})
	}
	_ = g.Wait()

	var result []DomainEvidence
	for dom, srcMap := range evidenceMap {
		for src := range srcMap {
			result = append(result, DomainEvidence{Domain: dom, Source: src})
		}
	}
	return result
}

// ================= HTTP/2 VALIDATOR =================

func writeH2(conn net.Conn, b []byte, timeout time.Duration) error {
	conn.SetWriteDeadline(time.Now().Add(timeout))
	n, err := conn.Write(b)
	if err != nil { return err }
	if n != len(b) { return fmt.Errorf("short write") }
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
	encoder.WriteField(hpack.HeaderField{Name: "accept", Value: "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8"})
	encoder.WriteField(hpack.HeaderField{Name: "accept-encoding", Value: "gzip, deflate, br, zstd"})
	encoder.WriteField(hpack.HeaderField{Name: "accept-language", Value: "en-US,en;q=0.9,ru;q=0.8"})
	encoder.WriteField(hpack.HeaderField{Name: "sec-ch-ua", Value: `"Not A(Brand";v="8", "Chromium";v="151", "Google Chrome";v="151"`})
	encoder.WriteField(hpack.HeaderField{Name: "sec-ch-ua-mobile", Value: "?0"})
	encoder.WriteField(hpack.HeaderField{Name: "sec-ch-ua-platform", Value: `"Windows"`})
	encoder.WriteField(hpack.HeaderField{Name: "sec-fetch-dest", Value: "document"})
	encoder.WriteField(hpack.HeaderField{Name: "sec-fetch-mode", Value: "navigate"})
	encoder.WriteField(hpack.HeaderField{Name: "sec-fetch-site", Value: "none"})
	encoder.WriteField(hpack.HeaderField{Name: "sec-fetch-user", Value: "?1"})
	encoder.WriteField(hpack.HeaderField{Name: "upgrade-insecure-requests", Value: "1"})

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

func ProbeH2(ctx context.Context, ip, sni string, cfg Config) (*Candidate, error) {
	cand := &Candidate{IP: ip, SNI: sni, Sources: make(map[string]bool)}
	
	t0 := time.Now()
	dialer := &net.Dialer{Timeout: time.Duration(cfg.TCPTimeoutMs) * time.Millisecond}
	conn, err := dialer.DialContext(ctx, "tcp", net.JoinHostPort(ip, "443"))
	if err != nil { return nil, err }
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
	if err := uConn.HandshakeContext(ctx); err != nil { return nil, err }
	cand.Timings.TLS = time.Since(t1)

	if uConn.ConnectionState().NegotiatedProtocol == "h2" {
		cand.ALPN = "h2"
	} else {
		cand.ALPN = "h2 (no ALPN)" // Смягченный ALPN фильтр
	}

	state := uConn.ConnectionState()
	if len(state.PeerCertificates) > 0 {
		cert := state.PeerCertificates[0]
		now := time.Now()
		cand.CertValidDates = now.After(cert.NotBefore) && now.Before(cert.NotAfter)
		cand.CertSANs = cert.DNSNames
	}

	t2 := time.Now()
	wTo := time.Duration(cfg.H2WriteTimeoutMs) * time.Millisecond
	
	if err := writeH2(uConn, []byte("PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"), wTo); err != nil { return nil, err }
	if err := writeH2(uConn, buildH2Frame(FrameSettings, 0, 0, []byte{}), wTo); err != nil { return nil, err }
	if err := writeH2(uConn, buildH2Frame(FrameHeaders, FlagEndHeaders|FlagEndStream, 1, buildH2HeadersEncoder(sni)), wTo); err != nil { return nil, err }

	uConn.SetReadDeadline(time.Now().Add(time.Duration(cfg.H2ReadTimeoutMs) * time.Millisecond))
	
	maxInboundFrameSize := uint32(16384)
	buf := make([]byte, maxInboundFrameSize)
	recvBuf := bytes.Buffer{}
	headerBlocks := bytes.Buffer{}
	decoder := hpack.NewDecoder(4096, nil)
	
	gotFirstByte := false
	var expectingContinuation bool
	var activeStreamID uint32
	var endStreamSeen bool

ReadLoop:
	for {
		if ctx.Err() != nil { return nil, ctx.Err() }
		n, err := uConn.Read(buf)
		if n > 0 {
			if !gotFirstByte {
				cand.Timings.TTFB = time.Since(t2)
				gotFirstByte = true
			}
			recvBuf.Write(buf[:n])
		}

		for recvBuf.Len() >= 9 {
			data := recvBuf.Bytes()
			length := uint32(data[0])<<16 | uint32(data[1])<<8 | uint32(data[2])
			
			if length > maxInboundFrameSize { return nil, fmt.Errorf("frame size exceeds max") }
			if uint32(recvBuf.Len()) < 9+length { break }

			frameType, flags := data[3], data[4]
			streamID := binary.BigEndian.Uint32(data[5:9]) & 0x7FFFFFFF
			payload := data[9 : 9+length]
			recvBuf.Next(int(9 + length))

			if expectingContinuation && (frameType != FrameContinuation || streamID != activeStreamID) {
				return nil, fmt.Errorf("expected CONTINUATION")
			}

			switch frameType {
			case FrameSettings:
				if streamID != 0 { return nil, fmt.Errorf("SETTINGS stream != 0") }
				if (flags & FlagAck) == 0 {
					if length%6 == 0 {
						_ = writeH2(uConn, buildH2Frame(FrameSettings, FlagAck, 0, []byte{}), wTo)
						for i := 0; i < int(length); i += 6 {
							if binary.BigEndian.Uint16(payload[i:i+2]) == SettingMaxFrameSize {
								val := binary.BigEndian.Uint32(payload[i+2 : i+6])
								if val >= 16384 && val <= 16777215 { 
									maxInboundFrameSize = val
									if maxInboundFrameSize > 1<<20 { maxInboundFrameSize = 1<<20 }
								}
							}
						}
					}
				}
			case FrameHeaders:
				if streamID == 1 {
					if (flags & FlagEndStream) != 0 { endStreamSeen = true }
					headerBlocks.Write(payload)
					if (flags & FlagEndHeaders) == 0 {
						expectingContinuation = true
						activeStreamID = streamID
					} else {
						expectingContinuation = false
						headers, err := decoder.DecodeFull(headerBlocks.Bytes())
						if err != nil { return nil, err }
						parseHeaders(cand, headers)
						headerBlocks.Reset()
					}
				}
			case FrameContinuation:
				if streamID == 1 {
					headerBlocks.Write(payload)
					if (flags & FlagEndHeaders) != 0 {
						expectingContinuation = false
						headers, err := decoder.DecodeFull(headerBlocks.Bytes())
						if err != nil { return nil, err }
						parseHeaders(cand, headers)
						headerBlocks.Reset()
					}
				}
			case FrameData:
				if streamID == 1 {
					if (flags & FlagEndStream) != 0 { endStreamSeen = true }
					cand.DataBytes += len(payload)
				}
			}

			if streamID == 1 && endStreamSeen && !expectingContinuation { break ReadLoop }
		}
		if err != nil { break }
	}

	// Оставляем ВСЕ статусы (2xx, 3xx, 4xx, 5xx), если сервер ответил хоть что-то по HTTP/2
	if cand.HTTPStatus == 0 { return nil, fmt.Errorf("no http status code") }
	return cand, nil
}

func parseHeaders(cand *Candidate, headers []hpack.HeaderField) {
	for _, h := range headers {
		hName, hVal := strings.ToLower(h.Name), strings.ToLower(h.Value)
		if hName == ":status" { fmt.Sscanf(hVal, "%d", &cand.HTTPStatus) }
		if hName == "server" {
			cand.Server = h.Value
			for _, cdn := range cdnServers { if strings.Contains(hVal, cdn) { cand.CDNConfidence += 30 } }
		}
		for _, cdnH := range cdnHeaders { if hName == cdnH { cand.CDNConfidence += 20 } }
	}
}

// ================= PIPELINES =================

func validateAndEnrich(cand *Candidate, asnDB, countryDB *geoip2.Reader, cfg Config) bool {
	parsedIP := net.ParseIP(cand.IP)
	if parsedIP != nil {
		if asnDB != nil { if r, err := asnDB.ASN(parsedIP); err == nil { cand.ASN = r.AutonomousSystemNumber } }
		if countryDB != nil { if r, err := countryDB.Country(parsedIP); err == nil { cand.Country = r.Country.IsoCode } }
	}

	if cfg.TargetASN != 0 && cand.ASN != cfg.TargetASN { return false }
	if cfg.TargetCountry != "" && !strings.EqualFold(cand.Country, cfg.TargetCountry) { return false }

	cand.Score = 50.0
	if !cand.CertValidDates { cand.Score -= 30.0 }
	cand.Score -= float64(cand.CDNConfidence)

	if cand.Score <= 0 { return false } // Отсеиваем только гарантированный мусор и CDNs
	return true
}

func RunDirectPipeline(ctx context.Context, cfg Config, sampledIPs []string, dedup *Deduplicator, asnDB, countryDB *geoip2.Reader, sources []OSINTSource) []Candidate {
	var mu sync.Mutex
	ipSniMap := make(map[string]map[string]bool)
	
	// ЭТАП 1: Разведка (PTR/OSINT)
	g1, gCtx1 := errgroup.WithContext(ctx)
	g1.SetLimit(cfg.Workers)
	
	for _, ip := range sampledIPs {
		ip := ip
		g1.Go(func() error {
			evidences := GatherOSINT(gCtx1, TargetQuery{IPs: []string{ip}}, sources)
			
			if len(evidences) == 0 && cfg.DirectSNI != "" {
				evidences = append(evidences, DomainEvidence{Domain: cfg.DirectSNI, Source: "Fallback"})
			}

			mu.Lock()
			for _, ev := range evidences {
				if ipSniMap[ip] == nil { ipSniMap[ip] = make(map[string]bool) }
				ipSniMap[ip][ev.Domain] = true
			}
			mu.Unlock()
			return nil
		})
	}
	_ = g1.Wait()

	uniqueIPs := 0
	for _, snis := range ipSniMap {
		if len(snis) > 0 { uniqueIPs++ }
	}
	fmt.Printf("\n[+] Этап 1 завершен. Найдено чистых IP с доменами: %d\n\n", uniqueIPs)

	type Pair struct { IP, SNI string; Src map[string]bool }
	var pairs []Pair
	for ip, snis := range ipSniMap {
		for sni, srcMap := range snis {
			if dedup.IsNew(ip + ":" + sni) { pairs = append(pairs, Pair{IP: ip, SNI: sni, Src: srcMap}) }
		}
	}

	// ЭТАП 2: Пробинг HTTP/2
	var candidates []Candidate
	g2, gCtx2 := errgroup.WithContext(ctx)
	g2.SetLimit(cfg.Workers)

	for _, p := range pairs {
		p := p
		g2.Go(func() error {
			cand, err := ProbeH2(gCtx2, p.IP, p.SNI, cfg)
			if err != nil { return nil }

			cand.Sources = p.Src
			if validateAndEnrich(cand, asnDB, countryDB, cfg) {
				mu.Lock()
				candidates = append(candidates, *cand)
				mu.Unlock()
			}
			return nil
		})
	}
	_ = g2.Wait()

	// Сортировка по минимальному RTT для выдачи лучшего результата наверх
	sort.Slice(candidates, func(i, j int) bool { return candidates[i].Timings.Total() < candidates[j].Timings.Total() })
	return candidates
}

// ================= MAIN =================

func main() {
	cfg := Config{}
	var modeStr, domainsStr string
	
	flag.StringVar(&modeStr, "mode", "passive", "passive | direct | hybrid")
	flag.IntVar(&cfg.Workers, "w", 30, "Worker pool size")
	flag.IntVar(&cfg.MaxIPs, "max-ips", 0, "Limit for IP sampling")
	flag.IntVar(&cfg.TCPTimeoutMs, "tcp-timeout", 2000, "TCP timeout ms")
	flag.IntVar(&cfg.TLSTimeoutMs, "tls-timeout", 2000, "TLS timeout ms")
	flag.IntVar(&cfg.H2ReadTimeoutMs, "h2-read", 3000, "H2 Read timeout ms")
	flag.IntVar(&cfg.H2WriteTimeoutMs, "h2-write", 2000, "H2 Write timeout ms")
	flag.Int64Var(&cfg.Seed, "seed", time.Now().UnixNano(), "Random seed")
	flag.StringVar(&cfg.TargetCountry, "c", "", "Hard Filter: Target Country Code")
	flag.UintVar(&cfg.TargetASN, "asn", 0, "Hard Filter: Target ASN constraint")
	flag.StringVar(&cfg.DirectSNI, "sni", "", "Fallback SNI for Direct mode")
	flag.StringVar(&domainsStr, "domains", "", "Comma-separated seed domains for Passive mode")
	flag.StringVar(&cfg.GeoIPPath, "geoip", "GeoLite2-Country.mmdb", "Path to Country DB")
	flag.StringVar(&cfg.ASNPath, "asn-db", "GeoLite2-ASN.mmdb", "Path to ASN DB")
	flag.Parse()

	if cfg.Workers < 1 { cfg.Workers = 1 }
	cfg.Mode = Mode(modeStr)
	cfg.CIDRs = flag.Args()
	if domainsStr != "" { cfg.Domains = strings.Split(domainsStr, ",") }

	if len(cfg.Domains) == 0 && len(cfg.CIDRs) == 0 {
		cfg.Mode = ModeAuto
	}

	var vpsASN uint
	var vpsCountry, vpsIP, localPrefix string
	var err error

	if cfg.Mode == ModeAuto || (cfg.TargetASN == 0 && cfg.TargetCountry == "") {
		vpsASN, vpsCountry, vpsIP, err = autoDetectVPS()
		if err == nil {
			cfg.TargetASN = vpsASN
			cfg.TargetCountry = vpsCountry
		}
	}

	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer cancel()

	var asnDB, countryDB *geoip2.Reader
	if db, err := geoip2.Open(cfg.ASNPath); err == nil { asnDB = db; defer db.Close() }
	if db, err := geoip2.Open(cfg.GeoIPPath); err == nil { countryDB = db; defer db.Close() }

	sources := []OSINTSource{&PTRSource{}, &CrtShSource{client: &http.Client{Timeout: 10 * time.Second}}}
	dedup := &Deduplicator{}
	var results []Candidate

	if cfg.Mode == ModeAuto {
		if cfg.TargetASN == 0 { log.Fatal("[-] Autonomous mode failed: Could not determine ASN.") }
		cidrs, err := fetchASNCIDRs(cfg.TargetASN)
		if err != nil || len(cidrs) == 0 { log.Fatalf("[-] Failed to fetch CIDRs for AS%d", cfg.TargetASN) }
		
		cfg.CIDRs = cidrs
		merged := MergeCIDRs(cidrs)
		
		vpsIPObj := net.ParseIP(vpsIP)
		for _, c := range cidrs {
			_, ipnet, _ := net.ParseCIDR(c)
			if ipnet != nil && ipnet.Contains(vpsIPObj) {
				localPrefix = c
				break
			}
		}

		sampledIPs := SampleIPs(merged, cfg.MaxIPs, cfg.Seed)
		
		fmt.Printf("[*] Используем указанный IP VPS: %s\n", vpsIP)
		fmt.Printf("[*] Announcing ASN:          AS%d (Локальный префикс: %s)\n", cfg.TargetASN, localPrefix)
		fmt.Printf("[*] Параллелизм:             %d горутин\n", cfg.Workers)
		fmt.Printf("[*] Страна сервера:          %s (GeoIP)\n", cfg.TargetCountry)
		fmt.Printf("[*] Подсетей для скана:      %d (из %d)\n", len(merged), len(cidrs))
		fmt.Printf("[*] Подготовлено %d IP адресов. Запуск...\n", len(sampledIPs))

		results = RunDirectPipeline(ctx, cfg, sampledIPs, dedup, asnDB, countryDB, sources)

	} else if cfg.Mode == ModeDirect {
		merged := MergeCIDRs(cfg.CIDRs)
		sampledIPs := SampleIPs(merged, cfg.MaxIPs, cfg.Seed)
		fmt.Printf("[*] Direct Mode: Подготовлено %d IP адресов. Запуск...\n", len(sampledIPs))
		results = RunDirectPipeline(ctx, cfg, sampledIPs, dedup, asnDB, countryDB, sources)
	} else {
		log.Fatal("[-] Only autonomous and direct modes are fully formatted in this block.")
	}

	if len(results) == 0 {
		fmt.Println("[-] Подходящих кандидатов не найдено.")
		return
	}

	fmt.Printf("[+] Найдено валидных HTTP/2 целей: %d\n\n", len(results))

	fmt.Printf("%-37.37s | %-15.15s | %-13.13s | %-5s | %-9s | %-20.20s | %s\n", "Цель (SNI)", "IP адрес", "ALPN", "HTTP", "DATA", "Сервер", "RTT")
	fmt.Println(strings.Repeat("-", 115))

	for _, r := range results {
		srv := r.Server
		if srv == "" { srv = "-" }
		if len(srv) > 20 { srv = srv[:20] }

		dataStr := fmt.Sprintf("%d B", r.DataBytes)
		rttStr := fmt.Sprintf("%d ms", r.Timings.Total().Milliseconds())

		fmt.Printf("%-37.37s | %-15.15s | %-13.13s | %-5d | %-9s | %-20.20s | %s\n",
			r.SNI, r.IP, r.ALPN, r.HTTPStatus, dataStr, srv, rttStr)
	}

	best := results[0]
	fmt.Println("\n===================================================================================================================")
	fmt.Println("                                   РЕКОМЕНДУЕМАЯ КОНФИГУРАЦИЯ REALITY (HTTP/2)")
	fmt.Println("===================================================================================================================")
	fmt.Printf("\"dest\": \"%s:443\",\n", best.SNI)
	fmt.Printf("\"serverNames\": [\n  \"%s\"\n]\n\n", best.SNI)
	fmt.Printf("Параметры: ALPN: %s, HTTP Status: %d, Server: %s, Body: %d B, RTT: %d ms\n", 
		best.ALPN, best.HTTPStatus, best.Server, best.DataBytes, best.Timings.Total().Milliseconds())
}
