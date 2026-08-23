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
	Debug            bool
}

// ================= MODELS =================

type Timings struct {
	TCP  time.Duration
	TLS  time.Duration
	TTFB time.Duration
}

type Candidate struct {
	IP             string
	SNI            string
	Sources        map[string]bool
	ASN            uint
	Country        string
	Timings        Timings
	HTTPStatus     int
	Server         string
	CDNConfidence  int
	DataBytes      int
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
	if d == "localhost" || strings.HasPrefix(d, "localhost.") {
		return ""
	}
	if !domainRe.MatchString(d) {
		return ""
	}
	return d
}

// ================= AUTO DETECTION =================

type ipAPIResp struct {
	Status      string `json:"status"`
	CountryCode string `json:"countryCode"`
	AS          string `json:"as"`
}

func autoDetectVPS() (uint, string, error) {
	client := &http.Client{Timeout: 5 * time.Second}
	resp, err := client.Get("http://ip-api.com/json/?fields=status,countryCode,as")
	if err != nil {
		return 0, "", err
	}
	defer resp.Body.Close()

	var geo ipAPIResp
	if err := json.NewDecoder(resp.Body).Decode(&geo); err != nil {
		return 0, "", err
	}
	if geo.Status != "success" {
		return 0, "", fmt.Errorf("api returned non-success status")
	}

	var asn uint
	parts := strings.Fields(geo.AS)
	if len(parts) > 0 && strings.HasPrefix(strings.ToUpper(parts[0]), "AS") {
		fmt.Sscanf(strings.ToUpper(parts[0]), "AS%d", &asn)
	}

	return asn, geo.CountryCode, nil
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
		if err != nil {
			continue
		}
		ones, bits := ipnet.Mask.Size()
		if bits != 32 {
			continue // IPv4 only
		}
		startInt := binary.BigEndian.Uint32(ipnet.IP)
		count := uint32(1) << (32 - ones)
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
		totalIPs += uint64(b.end - b.start + 1)
	}
	if totalIPs == 0 {
		return nil
	}

	sampleSize := uint64(maxIPs)
	if sampleSize > totalIPs {
		sampleSize = totalIPs
	}

	rng := rand.New(rand.NewSource(seed))
	startIdx := rng.Uint64() % totalIPs
	var step uint64 = 1
	if totalIPs > 1 {
		step = (rng.Uint64() % (totalIPs - 1)) | 1 
	}

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
func (s *CrtShSource) Name() string           { return "Crt.sh(CT)" }
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
		if (len(q.IPs) > 0 && !s.SupportsIP()) || (len(q.Domains) > 0 && !s.SupportsDomain()) {
			continue
		}
		g.Go(func() error {
			evidences, err := s.Search(gCtx, q)
			if err == nil {
				mu.Lock()
				for _, ev := range evidences {
					if evidenceMap[ev.Domain] == nil {
						evidenceMap[ev.Domain] = make(map[string]bool)
					}
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
	
	encoder.WriteField(hpack.HeaderField{
		Name:  "user-agent", 
		Value: "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/151.0.0.0 Safari/537.36",
	})
	encoder.WriteField(hpack.HeaderField{
		Name:  "accept", 
		Value: "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7",
	})
	encoder.WriteField(hpack.HeaderField{
		Name:  "accept-encoding", 
		Value: "gzip, deflate, br, zstd",
	})
	encoder.WriteField(hpack.HeaderField{
		Name:  "accept-language", 
		Value: "en-US,en;q=0.9,ru;q=0.8",
	})
	
	encoder.WriteField(hpack.HeaderField{
		Name:  "sec-ch-ua", 
		Value: `"Not A(Brand";v="8", "Chromium";v="151", "Google Chrome";v="151"`,
	})
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
	if err != nil { return nil, fmt.Errorf("tcp dial: %w", err) }
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
	if err := uConn.HandshakeContext(ctx); err != nil { return nil, fmt.Errorf("tls handshake: %w", err) }
	cand.Timings.TLS = time.Since(t1)

	if uConn.ConnectionState().NegotiatedProtocol != "h2" { return nil, fmt.Errorf("protocol is not h2") }

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
			
			if length > maxInboundFrameSize { return nil, fmt.Errorf("frame size %d exceeds max", length) }
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
				if (flags & FlagAck) != 0 {
					if length != 0 { return nil, fmt.Errorf("SETTINGS ACK length != 0") }
				} else {
					if length%6 != 0 { return nil, fmt.Errorf("SETTINGS length mod 6 != 0") }
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
			case FrameGoAway:
				if streamID != 0 { return nil, fmt.Errorf("GOAWAY stream != 0") }
			case FrameRSTStream:
				if length != 4 { return nil, fmt.Errorf("RST_STREAM length != 4") }
				if streamID == 1 { return nil, fmt.Errorf("stream 1 reset") }
			case FrameHeaders:
				if streamID == 0 { return nil, fmt.Errorf("HEADERS stream == 0") }
				if streamID == 1 {
					if (flags & FlagEndStream) != 0 { endStreamSeen = true }
					headerBlocks.Write(payload)
					if (flags & FlagEndHeaders) == 0 {
						expectingContinuation = true
						activeStreamID = streamID
					} else {
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
				if streamID == 0 { return nil, fmt.Errorf("DATA stream == 0") }
				if streamID == 1 {
					if (flags & FlagEndStream) != 0 { endStreamSeen = true }
					cand.DataBytes += len(payload)
				}
			}

			if streamID == 1 && endStreamSeen && !expectingContinuation { break ReadLoop }
		}
		if err != nil { break }
	}

	if cand.HTTPStatus < 200 || cand.HTTPStatus >= 300 { return nil, fmt.Errorf("bad http status: %d", cand.HTTPStatus) }
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

	var score float64 = 50.0
	score -= float64(cand.CDNConfidence)

	ttfbMs := float64(cand.Timings.TTFB.Milliseconds())
	if ttfbMs < 50 { score += 15.0 } else if ttfbMs > 300 { score -= (ttfbMs - 300) / 10.0 }
	if cand.HTTPStatus == 200 { score += 10.0 }
	
	if !cand.CertValidDates { score -= 20.0 }
	certMatch := false
	for _, san := range cand.CertSANs {
		if strings.EqualFold(san, cand.SNI) { certMatch = true; break }
	}
	if certMatch { score += 30.0 }

	if score > 100 { score = 100 }
	if score < 0 { score = 0 }
	cand.Score = score
	return true
}

func RunPassivePipeline(ctx context.Context, cfg Config, dedup *Deduplicator, asnDB, countryDB *geoip2.Reader, sources []OSINTSource) []Candidate {
	var qDomains []string
	for _, d := range cfg.Domains {
		if cl := CleanDomain(d); cl != "" { qDomains = append(qDomains, cl) }
	}
	if len(qDomains) == 0 { return nil }

	log.Printf("[*] Passive Mode: CT Expanding %d seed domains...", len(qDomains))
	evidences := GatherOSINT(ctx, TargetQuery{Domains: qDomains}, sources)
	
	domMap := make(map[string]map[string]bool)
	for _, ev := range evidences {
		if domMap[ev.Domain] == nil { domMap[ev.Domain] = make(map[string]bool) }
		domMap[ev.Domain][ev.Source] = true
	}

	var candidates []Candidate
	var mu sync.Mutex
	g, gCtx := errgroup.WithContext(ctx)
	g.SetLimit(cfg.Workers)

	for dom, srcMap := range domMap {
		dom, srcMap := dom, srcMap
		g.Go(func() error {
			addrs, err := net.DefaultResolver.LookupHost(gCtx, dom)
			if err != nil || len(addrs) == 0 { return nil }

			for _, ip := range addrs {
				if net.ParseIP(ip).To4() == nil { continue }
				if !dedup.IsNew(ip + ":" + dom) { continue }
				
				tempCand := &Candidate{IP: ip}
				if !validateAndEnrich(tempCand, asnDB, countryDB, cfg) { continue }

				cand, err := ProbeH2(gCtx, ip, dom, cfg)
				if err != nil { continue }

				cand.Sources = srcMap
				if validateAndEnrich(cand, asnDB, countryDB, cfg) && cand.Score > 20 {
					mu.Lock()
					candidates = append(candidates, *cand)
					mu.Unlock()
				}
			}
			return nil
		})
	}
	_ = g.Wait()
	return candidates
}

func RunDirectPipeline(ctx context.Context, cfg Config, dedup *Deduplicator, asnDB, countryDB *geoip2.Reader, sources []OSINTSource) []Candidate {
	mergedBlocks := MergeCIDRs(cfg.CIDRs)
	sampledIPs := SampleIPs(mergedBlocks, cfg.MaxIPs, cfg.Seed)
	log.Printf("[*] Direct Mode: Sampled %d unique IPs from merged CIDRs", len(sampledIPs))

	var candidates []Candidate
	var mu sync.Mutex
	g, gCtx := errgroup.WithContext(ctx)
	g.SetLimit(cfg.Workers)

	for _, ip := range sampledIPs {
		ip := ip
		g.Go(func() error {
			evidences := GatherOSINT(gCtx, TargetQuery{IPs: []string{ip}}, sources)
			
			sniMap := make(map[string]map[string]bool)
			for _, e := range evidences {
				if sniMap[e.Domain] == nil { sniMap[e.Domain] = make(map[string]bool) }
				sniMap[e.Domain][e.Source] = true
			}
			
			if len(sniMap) == 0 && cfg.DirectSNI != "" {
				sniMap[cfg.DirectSNI] = map[string]bool{"FallbackSNI": true}
			}

			for sni, srcMap := range sniMap {
				if !dedup.IsNew(ip + ":" + sni) { continue }
				
				cand, err := ProbeH2(gCtx, ip, sni, cfg)
				if err != nil { continue }

				cand.Sources = srcMap
				if validateAndEnrich(cand, asnDB, countryDB, cfg) && cand.Score > 20 {
					mu.Lock()
					candidates = append(candidates, *cand)
					mu.Unlock()
				}
			}
			return nil
		})
	}
	_ = g.Wait()
	return candidates
}

// ================= MAIN =================

func main() {
	cfg := Config{}
	var modeStr, domainsStr string
	
	flag.StringVar(&modeStr, "mode", "passive", "passive | direct | hybrid")
	flag.IntVar(&cfg.Workers, "w", 30, "Worker pool size")
	flag.IntVar(&cfg.MaxIPs, "max-ips", 100000, "Limit for IP sampling")
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

	// Auto-detect Geo and ASN if not explicitly set
	if cfg.TargetASN == 0 && cfg.TargetCountry == "" {
		log.Println("[*] Auto-detecting VPS ASN and Country...")
		asn, country, err := autoDetectVPS()
		if err != nil {
			log.Printf("[!] Failed to auto-detect VPS location: %v. Proceeding without hard scope.", err)
		} else {
			cfg.TargetASN = asn
			cfg.TargetCountry = country
			log.Printf("[+] Auto-detected: ASN=%d, Country=%s", cfg.TargetASN, cfg.TargetCountry)
		}
	}

	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer cancel()

	var asnDB, countryDB *geoip2.Reader
	if db, err := geoip2.Open(cfg.ASNPath); err == nil { asnDB = db; defer db.Close() } else { log.Printf("[!] ASN DB error: %v", err) }
	if db, err := geoip2.Open(cfg.GeoIPPath); err == nil { countryDB = db; defer db.Close() } else { log.Printf("[!] GeoIP DB error: %v", err) }

	sources := []OSINTSource{&PTRSource{}, &CrtShSource{client: &http.Client{Timeout: 10 * time.Second}}}
	dedup := &Deduplicator{}
	var results []Candidate

	switch cfg.Mode {
	case ModePassive:
		if len(cfg.Domains) == 0 { log.Fatal("[-] Passive mode requires --domains") }
		results = RunPassivePipeline(ctx, cfg, dedup, asnDB, countryDB, sources)
	case ModeDirect:
		if len(cfg.CIDRs) == 0 { log.Fatal("[-] Direct mode requires CIDR args") }
		results = RunDirectPipeline(ctx, cfg, dedup, asnDB, countryDB, sources)
	case ModeHybrid:
		log.Println("[*] Hybrid Mode Pipeline")
		if len(cfg.Domains) > 0 { results = RunPassivePipeline(ctx, cfg, dedup, asnDB, countryDB, sources) }
		
		goodCount := 0
		for _, r := range results { if r.Score >= 70 { goodCount++ } }
		
		if goodCount < 3 && len(cfg.CIDRs) > 0 {
			log.Printf("[!] Yield low (%d good candidates), initiating Direct phase...", goodCount)
			results = append(results, RunDirectPipeline(ctx, cfg, dedup, asnDB, countryDB, sources)...)
		}
	}

	if len(results) == 0 { log.Println("[-] No viable candidates found."); return }
	sort.Slice(results, func(i, j int) bool { return results[i].Score > results[j].Score })

	fmt.Printf("\n%-25s | %-15s | %-5s | %-5s | %-18s | %-6s\n", "SNI", "IP Address", "Score", "ASN", "TCP/TLS/TTFB", "Status")
	fmt.Println(strings.Repeat("-", 90))
	for _, r := range results {
		fmt.Printf("%-25s | %-15s | %-5.0f | %-5d | %-4d/%-4d/%-4d ms | %-6d\n",
			r.SNI, r.IP, r.Score, r.ASN,
			r.Timings.TCP.Milliseconds(), r.Timings.TLS.Milliseconds(), r.Timings.TTFB.Milliseconds(), r.HTTPStatus)
	}
}
