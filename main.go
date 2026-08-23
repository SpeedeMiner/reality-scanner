package main

import (
	"bytes"
	"crypto/rand"
	"crypto/tls"
	"encoding/binary"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"math/big"
	"net"
	"net/http"
	"os"
	"regexp"
	"sort"
	"strings"
	"sync"
	"time"

	"github.com/oschwald/geoip2-golang"
	utls "github.com/refraction-networking/utls"
	"golang.org/x/net/http2/hpack"
)

// ================= НАСТРОЙКИ =================
const ConnectTimeout = 2000 * time.Millisecond
const MaxHostsPer24 = 254
const MaxSampled24 = 4

// URL для скачивания свежих баз, если их нет локально
const geoCountryURL = "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb"
const geoAsnURL = "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-ASN.mmdb"

var bannedTLDs = map[string]bool{
	"crl": true, "ocsp": true, "der": true, "crt": true, "cer": true, "pem": true,
	"arpa": true, "local": true, "internal": true, "invalid": true, "example": true, "test": true, "localhost": true,
}

var bannedServers = []string{"cloudflare", "fastly", "akamai", "ddos-guard", "qrator", "sucuri"}

// ================= СТРУКТУРЫ =================
type Target struct {
	IP      string
	Domains []string
}

type ValidResult struct {
	Dest      string
	SNI       string
	IP        string
	RTT       int64
	ALPN      string
	Status    string
	Server    string
	DataBytes int
}

// ================= AUTO-PROVISIONING (СКАЧИВАНИЕ БД) =================
func ensureDBExists(filepath, downloadURL string) error {
	if _, err := os.Stat(filepath); err == nil {
		return nil // Файл уже существует
	}

	fmt.Printf("[*] База %s не найдена. Скачивание (может занять около минуты)...\n", filepath)

	out, err := os.Create(filepath)
	if err != nil {
		return fmt.Errorf("ошибка создания файла: %v", err)
	}
	defer out.Close()

	resp, err := http.Get(downloadURL)
	if err != nil {
		return fmt.Errorf("ошибка загрузки: %v", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("сервер вернул статус: %s", resp.Status)
	}

	_, err = io.Copy(out, resp.Body)
	if err != nil {
		return fmt.Errorf("ошибка сохранения: %v", err)
	}

	fmt.Printf("[+] База успешно скачана: %s\n", filepath)
	return nil
}

// ================= ANTI-ABUSE И JITTER =================
func addJitter() {
	n, _ := rand.Int(rand.Reader, big.NewInt(151))
	sleepTime := 50 + n.Int64()
	time.Sleep(time.Duration(sleepTime) * time.Millisecond)
}

// ================= ЛОКАЛЬНЫЙ GEOIP И ASN (MMDB) =================
func getPublicIP() string {
	urls := []string{"https://api.ipify.org", "https://ifconfig.me/ip"}
	client := &http.Client{Timeout: 4 * time.Second}
	for _, u := range urls {
		addJitter()
		resp, err := client.Get(u)
		if err == nil {
			defer resp.Body.Close()
			ipBytes, _ := io.ReadAll(resp.Body)
			ipStr := strings.TrimSpace(string(ipBytes))
			if net.ParseIP(ipStr) != nil {
				return ipStr
			}
		}
	}
	return "127.0.0.1"
}

func getASNAndCountryLocal(ip string, asnDB, countryDB *geoip2.Reader) (uint, string, string) {
	parsedIP := net.ParseIP(ip)
	if parsedIP == nil {
		return 0, "UNKNOWN_ASN", ""
	}

	var asn uint = 0
	var asnName = "UNKNOWN_ASN"
	var country = ""

	if asnDB != nil {
		record, err := asnDB.ASN(parsedIP)
		if err == nil {
			asn = record.AutonomousSystemNumber
			asnName = fmt.Sprintf("AS%d", asn)
		}
	}

	if countryDB != nil {
		record, err := countryDB.Country(parsedIP)
		if err == nil {
			country = record.Country.IsoCode
		}
	}

	return asn, asnName, country
}

// ================= СБОР ПОДСЕТЕЙ =================
func getPrefixes(asn uint) []string {
	if asn == 0 {
		return nil
	}
	client := &http.Client{Timeout: 8 * time.Second}
	addJitter()
	url := fmt.Sprintf("https://stat.ripe.net/data/announced-prefixes/data.json?resource=AS%d", asn)
	resp, err := client.Get(url)
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
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil
	}

	var prefixes []string
	for _, p := range result.Data.Prefixes {
		if !strings.Contains(p.Prefix, ":") { // Игнорируем IPv6
			prefixes = append(prefixes, p.Prefix)
		}
	}
	return prefixes
}

func filterPrefixesByCountryLocal(prefixes []string, targetCountry string, countryDB *geoip2.Reader) []string {
	if targetCountry == "" || countryDB == nil {
		return prefixes
	}
	targetCountry = strings.ToUpper(targetCountry)
	var matched []string

	for _, p := range prefixes {
		ip, _, err := net.ParseCIDR(p)
		if err != nil {
			continue
		}
		record, err := countryDB.Country(ip)
		if err == nil && strings.ToUpper(record.Country.IsoCode) == targetCountry {
			matched = append(matched, p)
		}
	}
	return matched
}

// ================= ГЕНЕРАТОР И РАНДОМИЗАЦИЯ IP =================
func generateAndShuffleIPs(prefixes []string, maxIPs int) []string {
	var ips []string
	seen := make(map[string]bool)

	for _, pStr := range prefixes {
		if maxIPs > 0 && len(ips) >= maxIPs {
			break
		}
		ip, ipnet, err := net.ParseCIDR(pStr)
		if err != nil {
			continue
		}

		ones, _ := ipnet.Mask.Size()
		limit := MaxHostsPer24
		if ones < 24 {
			limit = MaxHostsPer24 * MaxSampled24
		}

		count := 0
		for ip := ip.Mask(ipnet.Mask); ipnet.Contains(ip); inc(ip) {
			ipStr := ip.String()
			if !seen[ipStr] && !strings.HasSuffix(ipStr, ".0") && !strings.HasSuffix(ipStr, ".255") {
				seen[ipStr] = true
				ips = append(ips, ipStr)
				count++
				if maxIPs > 0 && len(ips) >= maxIPs {
					goto Shuffle
				}
				if count >= limit {
					break
				}
			}
		}
	}

Shuffle:
	for i := len(ips) - 1; i > 0; i-- {
		n, _ := rand.Int(rand.Reader, big.NewInt(int64(i+1)))
		j := int(n.Int64())
		ips[i], ips[j] = ips[j], ips[i]
	}
	return ips
}

func inc(ip net.IP) {
	for j := len(ip) - 1; j >= 0; j-- {
		ip[j]++
		if ip[j] > 0 {
			break
		}
	}
}

// ================= OSINT И ПАССИВНЫЙ DNS (ФАЗА 1) =================
func cleanDomain(d string) string {
	d = strings.ToLower(strings.TrimSpace(strings.TrimPrefix(d, "*.")))
	parts := strings.Split(d, ".")
	if len(parts) < 2 {
		return ""
	}
	tld := parts[len(parts)-1]
	matched, _ := regexp.MatchString(`^[a-z]{2,24}$`, tld)
	if !matched || bannedTLDs[tld] {
		return ""
	}
	if strings.ContainsAny(d, " \t\r\n/\\:*?\"'<>|#%&={}~`!@$^()+[]") {
		return ""
	}
	return d
}

func getPassiveDNS(ip string) []string {
	addJitter()
	var domains []string
	client := &http.Client{Timeout: 5 * time.Second}

	req, _ := http.NewRequest("GET", fmt.Sprintf("https://otx.alienvault.com/api/v1/indicators/IPv4/%s/passive_dns", ip), nil)
	req.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64)")
	if resp, err := client.Do(req); err == nil {
		defer resp.Body.Close()
		var res struct {
			PassiveDNS []struct {
				Hostname string `json:"hostname"`
			} `json:"passive_dns"`
		}
		json.NewDecoder(resp.Body).Decode(&res)
		for _, r := range res.PassiveDNS {
			if d := cleanDomain(r.Hostname); d != "" {
				domains = append(domains, d)
			}
		}
	}
	return domains
}

func getPTR(ip string) []string {
	addJitter()
	names, err := net.LookupAddr(ip)
	var res []string
	if err == nil {
		for _, n := range names {
			if d := cleanDomain(strings.TrimSuffix(n, ".")); d != "" {
				res = append(res, d)
			}
		}
	}
	return res
}

func validateFCrDNS(ip string, domains []string) []string {
	var valid []string
	seen := make(map[string]bool)

	for _, d := range domains {
		if seen[d] {
			continue
		}
		seen[d] = true

		addJitter()
		addrs, err := net.LookupHost(d)
		if err != nil {
			continue
		}

		for _, a := range addrs {
			if a == ip {
				valid = append(valid, d)
				break
			}
		}
	}
	return valid
}

func probeIPStealth(ip string) (string, []string) {
	var candidateDomains []string
	candidateDomains = append(candidateDomains, getPTR(ip)...)
	
	if len(candidateDomains) == 0 {
		candidateDomains = append(candidateDomains, getPassiveDNS(ip)...)
	}

	if len(candidateDomains) == 0 {
		return ip, nil 
	}

	validatedDomains := validateFCrDNS(ip, candidateDomains)

	if len(validatedDomains) > 5 {
		validatedDomains = validatedDomains[:5]
	}

	return ip, validatedDomains
}

// ================= HTTP/2 ВАЛИДАЦИЯ (ФАЗА 2) =================
func buildH2Headers(sni string) []byte {
	var payload []byte
	payload = append(payload, 0x82, 0x87, 0x84)
	sniBytes := []byte(sni)
	payload = append(payload, 0x01, byte(len(sniBytes)))
	payload = append(payload, sniBytes...)
	ua := []byte("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36")
	payload = append(payload, 0x0F, 0x2B, byte(len(ua)))
	payload = append(payload, ua...)
	return payload
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

func verifyH2(ip, sni string) *ValidResult {
	addJitter() 
	
	t0 := time.Now()
	dialer := &net.Dialer{Timeout: ConnectTimeout}
	conn, err := dialer.Dial("tcp", net.JoinHostPort(ip, "443"))
	if err != nil {
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
	
	uConn.SetDeadline(time.Now().Add(ConnectTimeout))

	if err := uConn.Handshake(); err != nil {
		return nil
	}

	rtt := time.Since(t0).Milliseconds()
	alpn := uConn.ConnectionState().NegotiatedProtocol
	if alpn != "h2" {
		return nil 
	}

	uConn.Write([]byte("PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"))
	uConn.Write(buildH2Frame(0x04, 0, 0, []byte{}))
	uConn.Write(buildH2Frame(0x01, 0x05, 1, buildH2Headers(sni)))

	buf := make([]byte, 8192)
	recvBuf := bytes.Buffer{}
	decoder := hpack.NewDecoder(4096, nil)
	
	status := ""
	server := "-"
	dataBytes := 0
	isH2 := false

	uConn.SetReadDeadline(time.Now().Add(1 * time.Second))
	for {
		n, err := uConn.Read(buf)
		if n > 0 {
			recvBuf.Write(buf[:n])
		}
		if err != nil || recvBuf.Len() > 16384 {
			break
		}

		if bytes.HasPrefix(recvBuf.Bytes(), []byte("HTTP/1.")) {
			return nil
		}

		for recvBuf.Len() >= 9 {
			data := recvBuf.Bytes()
			length := int(data[0])<<16 | int(data[1])<<8 | int(data[2])
			if recvBuf.Len() < 9+length {
				break
			}

			frameType := data[3]
			flags := data[4]
			streamId := binary.BigEndian.Uint32(data[5:9]) & 0x7FFFFFFF
			payload := data[9 : 9+length]
			recvBuf.Next(9 + length)

			if frameType == 0 || frameType == 1 || frameType == 4 {
				isH2 = true
			}

			if frameType == 0x04 && (flags&0x01) == 0 {
				uConn.Write(buildH2Frame(0x04, 0x01, 0, []byte{}))
			} else if frameType == 0x01 && streamId == 1 {
				headers, _ := decoder.DecodeFull(payload)
				for _, h := range headers {
					if h.Name == ":status" {
						status = h.Value
					}
					if h.Name == "server" {
						server = h.Value
					}
				}
			} else if frameType == 0x00 && streamId == 1 {
				dataBytes += len(payload)
			}
		}

		if isH2 && status != "" && (dataBytes > 0 || server != "-") {
			break
		}
	}

	if !isH2 || status == "" {
		return nil
	}

	serverLower := strings.ToLower(server)
	for _, cdn := range bannedServers {
		if strings.Contains(serverLower, cdn) {
			return nil
		}
	}

	return &ValidResult{
		Dest:      sni + ":443",
		SNI:       sni,
		IP:        ip,
		RTT:       rtt,
		ALPN:      alpn,
		Status:    status,
		Server:    server,
		DataBytes: dataBytes,
	}
}

// ================= MAIN =================
func main() {
	workers := flag.Int("w", 15, "Количество воркеров (рекомендуется 10-25 для anti-abuse)")
	maxIPs := flag.Int("max-ips", 0, "Лимит IP для проверки")
	vpsIP := flag.String("vps-ip", "", "IP сервера для ручного старта")
	countryFlag := flag.String("c", "", "Принудительно код страны (например, RU, US, NL)")
	dbCountryPath := flag.String("geoip", "GeoLite2-Country.mmdb", "Путь к базе GeoLite2-Country.mmdb")
	dbASNPath := flag.String("asn", "GeoLite2-ASN.mmdb", "Путь к базе GeoLite2-ASN.mmdb")
	flag.Parse()

	fmt.Println(strings.Repeat("=", 115))
	fmt.Println("      STEALTH REALITY SCANNER (OSINT-First + FCrDNS + H2 + AutoDB)")
	fmt.Println(strings.Repeat("=", 115))

	// Загружаем базы, если их нет
	if err := ensureDBExists(*dbCountryPath, geoCountryURL); err != nil {
		log.Printf("[-] Ошибка с базой Country: %v\n", err)
	}
	if err := ensureDBExists(*dbASNPath, geoAsnURL); err != nil {
		log.Printf("[-] Ошибка с базой ASN: %v\n", err)
	}

	// Инициализация локальных MMDB
	var countryDB, asnDB *geoip2.Reader
	var err error
	
	countryDB, err = geoip2.Open(*dbCountryPath)
	if err != nil {
		log.Printf("[-] Не удалось открыть GeoIP БД: %v (Фильтрация по странам будет неточной)", err)
	} else {
		defer countryDB.Close()
	}

	asnDB, err = geoip2.Open(*dbASNPath)
	if err != nil {
		log.Printf("[-] Не удалось открыть ASN БД: %v", err)
	} else {
		defer asnDB.Close()
	}

	var myIP string
	if *vpsIP != "" {
		myIP = *vpsIP
		fmt.Printf("[*] Указан IP VPS:           %s\n", myIP)
	} else {
		myIP = getPublicIP()
		fmt.Printf("[*] Внешний IP (Авто):       %s\n", myIP)
	}

	asnNum, asnStr, country := getASNAndCountryLocal(myIP, asnDB, countryDB)
	if *countryFlag != "" {
		country = strings.ToUpper(*countryFlag)
	}

	fmt.Printf("[*] ASN Сервера:             %s (Local MMDB)\n", asnStr)
	fmt.Printf("[*] Страна поиска:           %s\n", country)
	fmt.Printf("[*] Воркеров (Горутин):      %d (Low-Profile)\n", *workers)

	allPrefixes := getPrefixes(asnNum)
	targetPrefixes := filterPrefixesByCountryLocal(allPrefixes, country, countryDB)
	
	fmt.Printf("[*] Подсетей для скана:      %d (из %d)\n", len(targetPrefixes), len(allPrefixes))

	ips := generateAndShuffleIPs(targetPrefixes, *maxIPs)
	totalIPs := len(ips)
	fmt.Printf("[*] Подготовлено %d IP (Fisher-Yates Shuffled). Запуск OSINT...\n", totalIPs)

	if totalIPs == 0 {
		fmt.Println("[-] Нет IP-адресов для сканирования.")
		return
	}

	// ФАЗА 1: Скрытый OSINT-пробинг
	jobs := make(chan string, totalIPs)
	results1 := make(chan Target, totalIPs)
	var wg sync.WaitGroup

	for i := 0; i < *workers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for ip := range jobs {
				_, doms := probeIPStealth(ip)
				if len(doms) > 0 {
					results1 <- Target{IP: ip, Domains: doms}
				}
			}
		}()
	}

	for _, ip := range ips {
		jobs <- ip
	}
	close(jobs)
	wg.Wait()
	close(results1)

	var targets []Target
	for t := range results1 {
		targets = append(targets, t)
	}
	fmt.Printf("\n[+] Этап 1 завершен. Найдено чистых IP с FCrDNS доменами: %d\n", len(targets))

	if len(targets) == 0 {
		fmt.Println("[-] Ни один IP не прошел OSINT-фильтр FCrDNS.")
		return
	}

	// ФАЗА 2: Точечная валидация
	type ValidateJob struct {
		IP  string
		SNI string
	}
	jobs2 := make(chan ValidateJob, len(targets)*5)
	results2 := make(chan *ValidResult, len(targets)*5)

	for i := 0; i < *workers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := range jobs2 {
				if res := verifyH2(j.IP, j.SNI); res != nil {
					results2 <- res
				}
			}
		}()
	}

	for _, t := range targets {
		for _, d := range t.Domains {
			jobs2 <- ValidateJob{IP: t.IP, SNI: d}
		}
	}
	close(jobs2)
	wg.Wait()
	close(results2)

	var finalResults []*ValidResult
	for r := range results2 {
		finalResults = append(finalResults, r)
	}

	sort.Slice(finalResults, func(i, j int) bool {
		return finalResults[i].RTT < finalResults[j].RTT
	})

	fmt.Printf("\n[+] Найдено валидных HTTP/2 целей (TLS 1.3): %d\n\n", len(finalResults))
	if len(finalResults) == 0 {
		fmt.Println("[-] Подходящих HTTP/2 целей не обнаружено.")
		return
	}

	fmt.Printf("%-36s | %-15s | %-13s | %-5s | %-9s | %-20s | %-7s\n", "Цель (SNI)", "IP адрес", "ALPN", "HTTP", "DATA", "Сервер", "RTT")
	fmt.Println(strings.Repeat("-", 115))
	for _, r := range finalResults {
		dataStr := fmt.Sprintf("%d B", r.DataBytes)
		fmt.Printf("%-36s | %-15s | %-13s | %-5s | %-9s | %-20s | %d ms\n",
			limitStr(r.SNI, 36), r.IP, limitStr(r.ALPN, 13), r.Status, dataStr, limitStr(r.Server, 20), r.RTT)
	}

	best := finalResults[0]
	fmt.Println("\n" + strings.Repeat("=", 115))
	fmt.Println("             РЕКОМЕНДУЕМАЯ КОНФИГУРАЦИЯ REALITY (STEALTH)")
	fmt.Println(strings.Repeat("=", 115))
	fmt.Printf("\"dest\": \"%s\",\n", best.Dest)
	fmt.Println("\"serverNames\": [")
	fmt.Printf("  \"%s\"\n", best.SNI)
	fmt.Println("]")
}

func limitStr(s string, limit int) string {
	if len(s) > limit {
		return s[:limit]
	}
	return s
}
