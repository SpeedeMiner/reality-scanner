package main

import (
	"bytes"
	"context"
	"crypto/tls"
	"encoding/binary"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"math/rand"
	"net"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/oschwald/geoip2-golang"
	utls "github.com/refraction-networking/utls"
	"golang.org/x/net/http2/hpack"
)

// ================= HTTP/2 КОНСТАНТЫ =================
const (
	FrameData         = 0x00
	FrameHeaders      = 0x01
	FrameRSTStream    = 0x03
	FrameSettings     = 0x04
	FrameGoAway       = 0x07
	FrameContinuation = 0x09

	FlagEndStream  = 0x01
	FlagEndHeaders = 0x04
)

const (
	geoCountryURL = "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb"
	geoAsnURL     = "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-ASN.mmdb"
	MaxSampled24  = 4
)

var bannedTLDs = map[string]bool{
	"crl": true, "ocsp": true, "der": true, "crt": true, "cer": true, "pem": true,
	"arpa": true, "local": true, "internal": true, "invalid": true, "example": true, "test": true, "localhost": true,
}

var cdnHeaders = []string{"cf-ray", "x-amz-cf-id", "x-cache", "x-served-by", "cdn-loop"}
var cdnServers = []string{"cloudflare", "fastly", "akamai", "ddos-guard", "qrator", "sucuri"}
var cdnPTRs = []string{".cloudfront.net", ".fastly.net", ".akamaiedge.net", ".cloudflare.net"}

var tldRe = regexp.MustCompile(`^[a-z]{2,24}$`)

// ================= УТИЛИТЫ =================
func addAPIJitter(rng *rand.Rand) {
	time.Sleep(time.Duration(50+rng.Intn(150)) * time.Millisecond)
}

func limitStr(s string, limit int) string {
	runes := []rune(s)
	if len(runes) > limit {
		return string(runes[:limit])
	}
	return s
}

// ================= AUTO-PROVISIONING =================
func ensureDBExists(targetPath, downloadURL string) error {
	if _, err := os.Stat(targetPath); err == nil {
		return nil
	}

	log.Printf("[*] База %s не найдена. Начинаем скачивание...", targetPath)
	dir := filepath.Dir(targetPath)
	tmpFile, err := os.CreateTemp(dir, ".mmdb-*.tmp")
	if err != nil {
		return fmt.Errorf("создание temp файла: %v", err)
	}
	tmpPath := tmpFile.Name()
	defer os.Remove(tmpPath)

	client := &http.Client{Timeout: 10 * time.Minute}
	resp, err := client.Get(downloadURL)
	if err != nil {
		tmpFile.Close()
		return fmt.Errorf("ошибка HTTP GET: %v", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		tmpFile.Close()
		return fmt.Errorf("статус скачивания: %s", resp.Status)
	}

	if _, err := io.Copy(tmpFile, resp.Body); err != nil {
		tmpFile.Close()
		return fmt.Errorf("ошибка записи: %v", err)
	}
	tmpFile.Close()

	testDB, err := geoip2.Open(tmpPath)
	if err != nil {
		return fmt.Errorf("скачанный файл повреждён: %v", err)
	}
	testDB.Close()

	if err := os.Rename(tmpPath, targetPath); err != nil {
		return fmt.Errorf("ошибка rename: %v", err)
	}
	log.Printf("[+] База %s успешно загружена.", targetPath)
	return nil
}

// ================= ИНФРАСТРУКТУРА IP / ASN =================
func getPublicIP(ctx context.Context) (string, error) {
	urls := []string{"https://api.ipify.org", "https://ifconfig.me/ip"}
	client := &http.Client{Timeout: 5 * time.Second}
	for _, u := range urls {
		req, _ := http.NewRequestWithContext(ctx, "GET", u, nil)
		resp, err := client.Do(req)
		if err == nil {
			defer resp.Body.Close()
			ipBytes, _ := io.ReadAll(resp.Body)
			ipStr := strings.TrimSpace(string(ipBytes))
			if net.ParseIP(ipStr) != nil {
				return ipStr, nil
			}
		}
	}
	return "", fmt.Errorf("не удалось определить внешний IP")
}

func getASNAndCountryLocal(ip string, asnDB, countryDB *geoip2.Reader) (uint, string, string) {
	parsedIP := net.ParseIP(ip)
	if parsedIP == nil {
		return 0, "UNKNOWN_ASN", ""
	}
	var asn uint
	var asnName = "UNKNOWN_ASN"
	var country = ""

	if asnDB != nil {
		if record, err := asnDB.ASN(parsedIP); err == nil {
			asn = record.AutonomousSystemNumber
			asnName = fmt.Sprintf("AS%d", asn)
		}
	}
	if countryDB != nil {
		if record, err := countryDB.Country(parsedIP); err == nil {
			country = record.Country.IsoCode
		}
	}
	return asn, asnName, country
}

func getPrefixes(ctx context.Context, asn uint) []string {
	if asn == 0 { return nil }
	client := &http.Client{Timeout: 10 * time.Second}
	url := fmt.Sprintf("https://stat.ripe.net/data/announced-prefixes/data.json?resource=AS%d", asn)
	req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)
	resp, err := client.Do(req)
	if err != nil { return nil }
	defer resp.Body.Close()

	var result struct {
		Data struct {
			Prefixes []struct{ Prefix string `json:"prefix"` } `json:"prefixes"`
		} `json:"data"`
	}
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil { return nil }
	var prefixes []string
	for _, p := range result.Data.Prefixes {
		if !strings.Contains(p.Prefix, ":") { prefixes = append(prefixes, p.Prefix) }
	}
	return prefixes
}

// ================= ГЕНЕРАТОР IP =================
func generateAndShuffleIPs(prefixes []string, maxIPs int, rng *rand.Rand) []string {
	var allIPs []string
	for _, pStr := range prefixes {
		_, ipnet, err := net.ParseCIDR(pStr)
		if err != nil { continue }

		ones, _ := ipnet.Mask.Size()
		var subnets []string
		if ones < 24 {
			for ip := ipnet.IP.Mask(ipnet.Mask); ipnet.Contains(ip); incIPBy(ip, 256) {
				subnets = append(subnets, fmt.Sprintf("%d.%d.%d.0/24", ip[0], ip[1], ip[2]))
			}
			rng.Shuffle(len(subnets), func(i, j int) { subnets[i], subnets[j] = subnets[j], subnets[i] })
			if len(subnets) > MaxSampled24 { subnets = subnets[:MaxSampled24] }
		} else {
			subnets = []string{pStr}
		}

		for _, sub := range subnets {
			subIP, subNet, _ := net.ParseCIDR(sub)
			for ip := subIP.Mask(subNet.Mask); subNet.Contains(ip); inc(ip) {
				ip4 := ip.To4()
				if ip4 != nil {
					if ip4[3] == 0 || ip4[3] == 255 { continue }
					allIPs = append(allIPs, ip.String())
				}
			}
		}
	}
	rng.Shuffle(len(allIPs), func(i, j int) { allIPs[i], allIPs[j] = allIPs[j], allIPs[i] })
	if maxIPs > 0 && len(allIPs) > maxIPs { allIPs = allIPs[:maxIPs] }
	return allIPs
}

func inc(ip net.IP) {
	for j := len(ip) - 1; j >= 0; j-- {
		ip[j]++
		if ip[j] > 0 { break }
	}
}

func incIPBy(ip net.IP, val uint32) {
	ipInt := binary.BigEndian.Uint32(ip.To4())
	binary.BigEndian.PutUint32(ip.To4(), ipInt+val)
}

// ================= OSINT =================
type Target struct {
	IP      string
	Domains []string
}

type ValidResult struct {
	Dest, SNI, IP, ALPN, Status, Server string
	RTT                                 int64
	DataBytes                           int
}

func cleanDomain(d string) string {
	d = strings.ToLower(strings.TrimSpace(strings.TrimPrefix(d, "*.")))
	parts := strings.Split(d, ".")
	if len(parts) < 2 { return "" }
	tld := parts[len(parts)-1]
	if !tldRe.MatchString(tld) || bannedTLDs[tld] { return "" }
	if strings.ContainsAny(d, " \t\r\n/\\:*?\"'<>|#%&={}~`!@$^()+[]") { return "" }
	return d
}

func isCDNDomain(d string) bool {
	for _, ptr := range cdnPTRs {
		if strings.HasSuffix(d, ptr) { return true }
	}
	return false
}

func getPassiveDNS(ip string, rng *rand.Rand) []string {
	addAPIJitter(rng)
	var domains []string
	client := &http.Client{Timeout: 5 * time.Second}
	req, _ := http.NewRequest("GET", fmt.Sprintf("https://otx.alienvault.com/api/v1/indicators/IPv4/%s/passive_dns", ip), nil)
	req.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/151.0.0.0 Safari/537.36")
	if resp, err := client.Do(req); err == nil {
		defer resp.Body.Close()
		var res struct {
			PassiveDNS []struct{ Hostname string `json:"hostname"` } `json:"passive_dns"`
		}
		json.NewDecoder(resp.Body).Decode(&res)
		for _, r := range res.PassiveDNS {
			if d := cleanDomain(r.Hostname); d != "" && !isCDNDomain(d) { domains = append(domains, d) }
		}
	}
	return domains
}

func getPTR(ctx context.Context, ip string) []string {
	names, err := net.DefaultResolver.LookupAddr(ctx, ip)
	var res []string
	if err == nil {
		for _, n := range names {
			if d := cleanDomain(strings.TrimSuffix(n, ".")); d != "" && !isCDNDomain(d) { res = append(res, d) }
		}
	}
	return res
}

func validateFCrDNS(ctx context.Context, ip string, domains []string) []string {
	var valid []string
	seen := make(map[string]bool)
	for _, d := range domains {
		if seen[d] { continue }
		seen[d] = true
		addrs, err := net.DefaultResolver.LookupHost(ctx, d)
		if err != nil { continue }
		for _, a := range addrs {
			if a == ip {
				valid = append(valid, d)
				break
			}
		}
	}
	return valid
}

func probeIPStealth(ctx context.Context, ip string, rng *rand.Rand) (string, []string) {
	candidateDomains := getPTR(ctx, ip)
	if len(candidateDomains) == 0 { candidateDomains = append(candidateDomains, getPassiveDNS(ip, rng)...) }
	if len(candidateDomains) == 0 { return ip, nil }

	validated := validateFCrDNS(ctx, ip, candidateDomains)
	if len(validated) > 5 { validated = validated[:5] }
	return ip, validated
}

// ================= HTTP/2 =================
func buildH2HeadersEncoder(sni string) []byte {
	var buf bytes.Buffer
	encoder := hpack.NewEncoder(&buf)
	encoder.WriteField(hpack.HeaderField{Name: ":method", Value: "GET"})
	encoder.WriteField(hpack.HeaderField{Name: ":scheme", Value: "https"})
	encoder.WriteField(hpack.HeaderField{Name: ":path", Value: "/"})
	encoder.WriteField(hpack.HeaderField{Name: ":authority", Value: sni})
	encoder.WriteField(hpack.HeaderField{Name: "user-agent", Value: "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/151.0.0.0 Safari/537.36"})
	return buf.Bytes()
}

func buildH2Frame(frameType, flags byte, streamId uint32, payload []byte) []byte {
	length := len(payload)
	header := make([]byte, 9)
	header[0] = byte(length >> 16)
	header[1] = byte(length >> 8)
	header[2] = byte(length)
	header[3] = frameType
	header[4] = flags
	binary.BigEndian.PutUint32(header[5:9], streamId&0x7FFFFFFF)
	return append(header, payload...)
}

func verifyH2(ctx context.Context, ip, sni string, dialTimeout time.Duration, debug bool) *ValidResult {
	t0 := time.Now()
	dialer := &net.Dialer{Timeout: dialTimeout}
	conn, err := dialer.DialContext(ctx, "tcp", net.JoinHostPort(ip, "443"))
	if err != nil {
		if debug { log.Printf("[DEBUG] %s (%s) - TCP Dial Fail: %v", sni, ip, err) }
		return nil
	}
	defer conn.Close()

	uConn := utls.UClient(conn, &utls.Config{
		ServerName:         sni,
		InsecureSkipVerify: true,
		NextProtos:         []string{"h2"},
		MinVersion:         tls.VersionTLS13,
		MaxVersion:         tls.VersionTLS13,
	}, utls.HelloChrome_Auto)

	uConn.SetDeadline(time.Now().Add(dialTimeout))
	if err := uConn.HandshakeContext(ctx); err != nil {
		if debug { log.Printf("[DEBUG] %s (%s) - TLS Handshake Fail: %v", sni, ip, err) }
		return nil
	}

	rtt := time.Since(t0).Milliseconds()
	alpn := uConn.ConnectionState().NegotiatedProtocol
	if alpn != "h2" {
		if debug { log.Printf("[DEBUG] %s (%s) - Отклонён (ALPN: '%s')", sni, ip, alpn) }
		return nil
	}

	uConn.Write([]byte("PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"))
	uConn.Write(buildH2Frame(FrameSettings, 0, 0, []byte{}))
	uConn.Write(buildH2Frame(FrameHeaders, FlagEndHeaders|FlagEndStream, 1, buildH2HeadersEncoder(sni)))

	buf := make([]byte, 8192)
	recvBuf := bytes.Buffer{}
	headerBlocks := bytes.Buffer{}
	decoder := hpack.NewDecoder(4096, nil)

	status, server := "", "-"
	dataBytes := 0
	isCDN := false

	uConn.SetReadDeadline(time.Now().Add(1500 * time.Millisecond))

ReadLoop:
	for {
		if ctx.Err() != nil { return nil }
		n, err := uConn.Read(buf)
		if n > 0 { recvBuf.Write(buf[:n]) }

		if bytes.HasPrefix(recvBuf.Bytes(), []byte("HTTP/1.")) {
			if debug { log.Printf("[DEBUG] %s (%s) - Вернул HTTP/1.1 вместо H2 фрейма", sni, ip) }
			return nil
		}

		for recvBuf.Len() >= 9 {
			data := recvBuf.Bytes()
			length := int(data[0])<<16 | int(data[1])<<8 | int(data[2])
			if recvBuf.Len() < 9+length { break }

			frameType := data[3]
			flags := data[4]
			payload := data[9 : 9+length]
			recvBuf.Next(9 + length)

			if frameType == FrameGoAway || frameType == FrameRSTStream {
				if debug { log.Printf("[DEBUG] %s (%s) - Сервер прислал GOAWAY/RST", sni, ip) }
				return nil
			}
			if frameType == FrameSettings && (flags&0x01) == 0 {
				uConn.Write(buildH2Frame(FrameSettings, 0x01, 0, []byte{}))
			}
			if frameType == FrameHeaders || frameType == FrameContinuation {
				headerBlocks.Write(payload)
				if (flags & FlagEndHeaders) != 0 {
					headers, _ := decoder.DecodeFull(headerBlocks.Bytes())
					headerBlocks.Reset()
					for _, h := range headers {
						hName := strings.ToLower(h.Name)
						if hName == ":status" { status = h.Value }
						if hName == "server" { server = h.Value }
						for _, ch := range cdnHeaders {
							if hName == ch { isCDN = true }
						}
					}
				}
			}
			if frameType == FrameData { dataBytes += len(payload) }
			
			// БАГФИКС ЗДЕСЬ: Проверяем END_STREAM ТОЛЬКО для фреймов DATA или HEADERS. 
			// Иначе мы рвали соединение на служебном SETTINGS ACK.
			if (frameType == FrameData || frameType == FrameHeaders) && (flags&FlagEndStream) != 0 {
				break ReadLoop
			}
		}

		if err != nil || recvBuf.Len() > 32768 {
			if debug && err != io.EOF { log.Printf("[DEBUG] %s (%s) - Ошибка чтения/EOF: %v", sni, ip, err) }
			break
		}
	}

	if status == "" || isCDN {
		if debug { log.Printf("[DEBUG] %s (%s) - Отклонён (Status: %s, isCDN: %v)", sni, ip, status, isCDN) }
		return nil
	}

	serverLower := strings.ToLower(server)
	for _, cdn := range cdnServers {
		if strings.Contains(serverLower, cdn) {
			if debug { log.Printf("[DEBUG] %s (%s) - Обнаружен CDN Server: %s", sni, ip, server) }
			return nil
		}
	}

	if debug { log.Printf("[DEBUG] %s (%s) - УСПЕХ! H2 200 OK", sni, ip) }
	return &ValidResult{Dest: sni + ":443", SNI: sni, IP: ip, RTT: rtt, ALPN: "h2", Status: status, Server: server, DataBytes: dataBytes}
}

// ================= MAIN =================
func main() {
	workers := flag.Int("w", 20, "Количество воркеров")
	maxIPs := flag.Int("max-ips", 0, "Лимит IP для проверки")
	timeoutMs := flag.Int("t", 2000, "Таймаут TCP/TLS в мс")
	vpsIP := flag.String("vps-ip", "", "Принудительный IP сервера")
	countryFlag := flag.String("c", "", "Код страны (RU, US и т.д.)")
	dbCountry := flag.String("geoip", "GeoLite2-Country.mmdb", "Путь к GeoLite2-Country.mmdb")
	dbASN := flag.String("asn", "GeoLite2-ASN.mmdb", "Путь к GeoLite2-ASN.mmdb")
	debugMode := flag.Bool("debug", false, "Выводить причины отбрасывания целей (Фаза 2)")
	flag.Parse()

	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer cancel()

	log.SetFlags(log.Ltime)
	fmt.Println(strings.Repeat("=", 115))
	fmt.Println("      STEALTH REALITY SCANNER (OSINT-First + FCrDNS + H2 + AutoDB)")
	fmt.Println(strings.Repeat("=", 115))

	if err := ensureDBExists(*dbCountry, geoCountryURL); err != nil { log.Fatalf("[-] %v", err) }
	if err := ensureDBExists(*dbASN, geoAsnURL); err != nil { log.Fatalf("[-] %v", err) }

	countryDB, _ := geoip2.Open(*dbCountry)
	asnDB, _ := geoip2.Open(*dbASN)
	defer countryDB.Close()
	defer asnDB.Close()

	myIP := *vpsIP
	if myIP == "" {
		ip, err := getPublicIP(ctx)
		if err != nil { log.Fatalf("[-] %v", err) }
		myIP = ip
	}

	asnNum, asnStr, country := getASNAndCountryLocal(myIP, asnDB, countryDB)
	if *countryFlag != "" { country = strings.ToUpper(*countryFlag) }

	log.Printf("[*] IP сервера:        %s", myIP)
	log.Printf("[*] ASN:               %s (Local MMDB)", asnStr)
	log.Printf("[*] Страна поиска:     %s", country)

	allPrefixes := getPrefixes(ctx, asnNum)
	var targetPrefixes []string
	if country == "" {
		targetPrefixes = allPrefixes
	} else {
		for _, p := range allPrefixes {
			ip, _, err := net.ParseCIDR(p)
			if err != nil { continue }
			if record, err := countryDB.Country(ip); err == nil && strings.ToUpper(record.Country.IsoCode) == country {
				targetPrefixes = append(targetPrefixes, p)
			}
		}
	}

	rng := rand.New(rand.NewSource(time.Now().UnixNano()))
	ips := generateAndShuffleIPs(targetPrefixes, *maxIPs, rng)
	totalIPs := len(ips)
	log.Printf("[*] Подготовлено IP:   %d (Shuffled & Sampled)", totalIPs)

	if totalIPs == 0 { return }

	jobs := make(chan string, totalIPs)
	results1 := make(chan Target, totalIPs)
	var wg sync.WaitGroup

	for i := 0; i < *workers; i++ {
		wg.Add(1)
		go func(workerID int) {
			defer wg.Done()
			localRng := rand.New(rand.NewSource(time.Now().UnixNano() + int64(workerID)))
			for ip := range jobs {
				if ctx.Err() != nil { return }
				ctxReq, cancelReq := context.WithTimeout(ctx, 4*time.Second)
				_, doms := probeIPStealth(ctxReq, ip, localRng)
				cancelReq()
				if len(doms) > 0 { results1 <- Target{IP: ip, Domains: doms} }
			}
		}(i)
	}

	go func() {
		for _, ip := range ips {
			if ctx.Err() != nil { break }
			jobs <- ip
		}
		close(jobs)
	}()

	wg.Wait()
	close(results1)

	var targets []Target
	for t := range results1 { targets = append(targets, t) }

	if ctx.Err() != nil {
		log.Println("[!] Прервано. Промежуточные результаты...")
	} else {
		log.Printf("\n[+] OSINT фаза завершена. Найдено IP с FCrDNS доменами: %d", len(targets))
	}
	if len(targets) == 0 { return }

	type ValidateJob struct{ IP, SNI string }
	jobs2 := make(chan ValidateJob, len(targets)*5)
	results2 := make(chan *ValidResult, len(targets)*5)
	dialTimeout := time.Duration(*timeoutMs) * time.Millisecond

	for i := 0; i < *workers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := range jobs2 {
				if ctx.Err() != nil { return }
				if res := verifyH2(ctx, j.IP, j.SNI, dialTimeout, *debugMode); res != nil {
					results2 <- res
				}
			}
		}()
	}

	go func() {
		for _, t := range targets {
			for _, d := range t.Domains {
				if ctx.Err() != nil { break }
				jobs2 <- ValidateJob{IP: t.IP, SNI: d}
			}
		}
		close(jobs2)
	}()

	wg.Wait()
	close(results2)

	var finalResults []*ValidResult
	for r := range results2 { finalResults = append(finalResults, r) }

	if len(finalResults) == 0 {
		log.Println("[-] Подходящих HTTP/2 целей не обнаружено.")
		return
	}

	sort.Slice(finalResults, func(i, j int) bool { return finalResults[i].RTT < finalResults[j].RTT })

	fmt.Printf("\n%-36s | %-15s | %-5s | %-9s | %-20s | %-7s\n", "Цель (SNI)", "IP адрес", "HTTP", "DATA", "Сервер", "RTT")
	fmt.Println(strings.Repeat("-", 110))
	for _, r := range finalResults {
		fmt.Printf("%-36s | %-15s | %-5s | %-9s | %-20s | %d ms\n",
			limitStr(r.SNI, 36), r.IP, r.Status, fmt.Sprintf("%d B", r.DataBytes), limitStr(r.Server, 20), r.RTT)
	}

	best := finalResults[0]
	fmt.Println("\n" + strings.Repeat("=", 110))
	fmt.Println("             РЕКОМЕНДУЕМАЯ КОНФИГУРАЦИЯ REALITY (STEALTH)")
	fmt.Println(strings.Repeat("=", 110))
	fmt.Printf("\"dest\": \"%s\",\n", best.Dest)
	fmt.Println("\"serverNames\": [")
	fmt.Printf("  \"%s\"\n", best.SNI)
	fmt.Println("]")
}
