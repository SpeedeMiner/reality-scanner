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
	"net"
	"net/http"
	"os"
	"regexp"
	"sort"
	"strings"
	"sync"
	"time"

	utls "github.com/refraction-networking/utls"
	"golang.org/x/net/http2/hpack"
)

// ================= НАСТРОЙКИ =================
const ConnectTimeout = 1200 * time.Millisecond
const MaxHostsPer24 = 254
const MaxSampled24 = 4

var bannedTLDs = map[string]bool{
	"crl": true, "ocsp": true, "der": true, "crt": true, "cer": true, "pem": true,
	"arpa": true, "local": true, "internal": true, "invalid": true, "example": true, "test": true, "localhost": true,
}

var bannedServers = []string{"cloudflare", "fastly", "akamai", "ddos-guard", "qrator", "sucuri"}
var dnsCache sync.Map

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

// ================= BGP И GEOIP ХЕЛПЕРЫ =================
func getPublicIP() string {
	urls := []string{"https://api.ipify.org", "https://ifconfig.me/ip", "https://icanhazip.com"}
	client := &http.Client{Timeout: 4 * time.Second}
	for _, u := range urls {
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

func getASNAndPrefix(ip string) (string, string) {
	client := &http.Client{Timeout: 6 * time.Second}
	resp, err := client.Get(fmt.Sprintf("https://stat.ripe.net/data/network-info/data.json?resource=%s", ip))
	if err != nil {
		return "", ""
	}
	defer resp.Body.Close()
	var result struct {
		Data struct {
			ASNs   []interface{} `json:"asns"`
			Prefix string        `json:"prefix"`
		} `json:"data"`
	}
	json.NewDecoder(resp.Body).Decode(&result)
	if len(result.Data.ASNs) == 0 {
		return "", ""
	}
	asn := fmt.Sprintf("%v", result.Data.ASNs[0])
	if !strings.HasPrefix(strings.ToUpper(asn), "AS") {
		asn = "AS" + asn
	}
	return asn, result.Data.Prefix
}

func getPrefixes(asn string) []string {
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
		if !strings.Contains(p.Prefix, ":") { // Только IPv4
			prefixes = append(prefixes, p.Prefix)
		}
	}
	return prefixes
}

// ================= ГЕНЕРАТОР IP =================
func generateIPs(prefixes []string, maxIPs int) []string {
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
		if ones >= 24 {
			count := 0
			for ip := ip.Mask(ipnet.Mask); ipnet.Contains(ip); inc(ip) {
				ipStr := ip.String()
				if !seen[ipStr] && !strings.HasSuffix(ipStr, ".0") && !strings.HasSuffix(ipStr, ".255") {
					seen[ipStr] = true
					ips = append(ips, ipStr)
					count++
					if maxIPs > 0 && len(ips) >= maxIPs {
						return ips
					}
					if count >= MaxHostsPer24 {
						break
					}
				}
			}
		} else {
			// Упрощенная логика сэмплинга для огромных подсетей
			count := 0
			for ip := ip.Mask(ipnet.Mask); ipnet.Contains(ip); inc(ip) {
				ipStr := ip.String()
				if !seen[ipStr] && !strings.HasSuffix(ipStr, ".0") && !strings.HasSuffix(ipStr, ".255") {
					seen[ipStr] = true
					ips = append(ips, ipStr)
					count++
					if maxIPs > 0 && len(ips) >= maxIPs {
						return ips
					}
					if count >= (MaxHostsPer24 * MaxSampled24) {
						break
					}
				}
			}
		}
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

// ================= ВАЛИДАЦИЯ ДОМЕНОВ И OSINT =================
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

func getOSINTDomains(ip string) []string {
	var domains []string
	client := &http.Client{Timeout: 4 * time.Second}

	// 1. AlienVault
	req, _ := http.NewRequest("GET", fmt.Sprintf("https://otx.alienvault.com/api/v1/indicators/IPv4/%s/passive_dns", ip), nil)
	req.Header.Set("User-Agent", "Mozilla/5.0")
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

// ================= UTLS И ПРОБИНГ (ФАЗА 1) =================
func checkTLS(ip, sni string) (string, []string) {
	dialer := &net.Dialer{Timeout: ConnectTimeout}
	conn, err := dialer.Dial("tcp", net.JoinHostPort(ip, "443"))
	if err != nil {
		return "DEAD", nil
	}
	defer conn.Close()

	uConn := utls.UClient(conn, &utls.Config{
		ServerName:         sni,
		InsecureSkipVerify: true,
	}, utls.HelloChrome_Auto) // Маскируемся под Chrome!

	uConn.SetDeadline(time.Now().Add(ConnectTimeout))
	err = uConn.Handshake()

	if err != nil {
		// Порт открыт, но рукопожатие сброшено (ssl_reject_handshake)
		return "SSL_ERROR", nil
	}

	var doms []string
	certs := uConn.ConnectionState().PeerCertificates
	if len(certs) > 0 {
		for _, d := range certs[0].DNSNames {
			if cd := cleanDomain(d); cd != "" {
				doms = append(doms, cd)
			}
		}
		if cd := cleanDomain(certs[0].Subject.CommonName); cd != "" {
			doms = append(doms, cd)
		}
	}
	return "OK", doms
}

func probeIP(ip string) (string, []string) {
	status, doms := checkTLS(ip, ip)

	if status == "DEAD" {
		return ip, nil
	}

	domSet := make(map[string]bool)
	for _, d := range doms {
		domSet[d] = true
	}

	if len(domSet) > 15 {
		return ip, nil // CDN / Shared
	}

	if status == "SSL_ERROR" || len(domSet) == 0 {
		ptrs := getPTR(ip)
		for _, ptr := range ptrs {
			stat, cDoms := checkTLS(ip, ptr)
			if stat == "OK" {
				for _, d := range cDoms {
					domSet[d] = true
				}
			}
		}

		if len(domSet) == 0 {
			osints := getOSINTDomains(ip)
			for _, osint := range osints {
				stat, cDoms := checkTLS(ip, osint)
				if stat == "OK" {
					for _, d := range cDoms {
						domSet[d] = true
					}
					break // Нашли хотя бы один рабочий домен!
				}
			}
		}
	}

	var finalDoms []string
	for d := range domSet {
		finalDoms = append(finalDoms, d)
		if len(finalDoms) >= 5 {
			break
		}
	}
	return ip, finalDoms
}

// ================= HTTP/2 ВАЛИДАЦИЯ (ФАЗА 2) =================
func buildH2Headers(sni string) []byte {
	var payload []byte
	payload = append(payload, 0x82, 0x87, 0x84) // GET, https, /
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
	// DNS ПРОВЕРКА
	if val, ok := dnsCache.Load(sni); ok {
		if !strings.Contains(val.(string), ip) {
			return nil
		}
	} else {
		ips, err := net.LookupHost(sni)
		if err != nil {
			return nil
		}
		found := false
		var ipList []string
		for _, i := range ips {
			ipList = append(ipList, i)
			if i == ip {
				found = true
			}
		}
		dnsCache.Store(sni, strings.Join(ipList, ","))
		if !found {
			return nil
		}
	}

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
		NextProtos:         []string{"h2", "http/1.1"},
		MinVersion:         tls.VersionTLS13,
		MaxVersion:         tls.VersionTLS13,
	}, utls.HelloChrome_Auto)
	uConn.SetDeadline(time.Now().Add(ConnectTimeout))

	if err := uConn.Handshake(); err != nil {
		return nil
	}

	rtt := time.Since(t0).Milliseconds()
	alpn := uConn.ConnectionState().NegotiatedProtocol
	if alpn == "" {
		alpn = "h2 (no ALPN)"
	}

	// Отправляем H2 Preface + HEADERS
	uConn.Write([]byte("PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"))
	uConn.Write(buildH2Frame(0x04, 0, 0, []byte{})) // SETTINGS
	uConn.Write(buildH2Frame(0x01, 0x05, 1, buildH2Headers(sni)))

	// Читаем фреймы
	buf := make([]byte, 8192)
	recvBuf := bytes.Buffer{}
	decoder := hpack.NewDecoder(4096, nil)
	
	status := "200"
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
				break // Ждем еще данных
			}

			frameType := data[3]
			flags := data[4]
			streamId := binary.BigEndian.Uint32(data[5:9]) & 0x7FFFFFFF
			payload := data[9 : 9+length]
			recvBuf.Next(9 + length)

			if frameType == 0 || frameType == 1 || frameType == 4 || frameType == 7 || frameType == 8 {
				isH2 = true
			}

			if frameType == 0x04 && (flags&0x01) == 0 { // SETTINGS ACK
				uConn.Write(buildH2Frame(0x04, 0x01, 0, []byte{}))
			} else if frameType == 0x01 && streamId == 1 { // HEADERS
				headers, _ := decoder.DecodeFull(payload)
				for _, h := range headers {
					if h.Name == ":status" {
						status = h.Value
					}
					if h.Name == "server" {
						server = h.Value
					}
				}
			} else if frameType == 0x00 && streamId == 1 { // DATA
				dataBytes += len(payload)
			}
		}

		if isH2 && status != "" && (dataBytes > 0 || server != "-") {
			break
		}
	}

	if !isH2 {
		return nil
	}

	serverLower := strings.ToLower(server)
	for _, cdn := range bannedServers {
		if strings.Contains(serverLower, cdn) {
			return nil // Дропаем CDN
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
	workers := flag.Int("w", 500, "Количество горутин (concurrency)")
	maxIPs := flag.Int("max-ips", 0, "Лимит IP для скана")
	debugIP := flag.String("debug-ip", "", "Проверить один IP")
	flag.Parse()

	fmt.Println(strings.Repeat("=", 115))
	fmt.Println("      RIPE REALITY SCANNER (Golang + uTLS Chrome Fingerprint + H2 Engine)")
	fmt.Println(strings.Repeat("=", 115))

	if *debugIP != "" {
		fmt.Printf("\n[*] Отладка IP: %s\n", *debugIP)
		ip, doms := probeIP(*debugIP)
		fmt.Printf("[+] Домены (ASN.1 + OSINT): %v\n", doms)
		for _, d := range doms {
			res := verifyH2(ip, d)
			if res != nil {
				fmt.Printf("    - SNI '%s': УСПЕХ (Status: %s, RTT: %dms)\n", d, res.Status, res.RTT)
			} else {
				fmt.Printf("    - SNI '%s': ОТКЛОНЕН\n", d)
			}
		}
		return
	}

	myIP := getPublicIP()
	asn, prefix := getOriginAndNetworkInfo(myIP)
	fmt.Printf("[*] Внешний IP:        %s\n", myIP)
	fmt.Printf("[*] Announcing ASN:    %s (Локальный префикс: %s)\n", asn, prefix)
	fmt.Printf("[*] Параллелизм:       %d горутин\n", *workers)

	allPrefixes := getPrefixes(asn)
	if len(allPrefixes) == 0 && prefix != "" {
		allPrefixes = []string{prefix}
	}
	fmt.Printf("[*] Подсетей (BGP):    %d\n", len(allPrefixes))

	ips := generateIPs(allPrefixes, *maxIPs)
	totalIPs := len(ips)
	fmt.Printf("[*] Подготовлено %d IP адресов. Запуск...\n", totalIPs)

	// ФАЗА 1: ПРОБИНГ
	jobs := make(chan string, totalIPs)
	results1 := make(chan Target, totalIPs)
	var wg sync.WaitGroup

	for i := 0; i < *workers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for ip := range jobs {
				_, doms := probeIP(ip)
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
	fmt.Printf("\n[+] Этап 1 завершен. Найдено чистых IP с доменами: %d\n", len(targets))

	// ФАЗА 2: ВАЛИДАЦИЯ
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

	// СОРТИРОВКА И ВЫВОД
	var finalResults []*ValidResult
	for r := range results2 {
		finalResults = append(finalResults, r)
	}

	sort.Slice(finalResults, func(i, j int) bool {
		return finalResults[i].RTT < finalResults[j].RTT
	})

	fmt.Printf("\n[+] Найдено валидных HTTP/2 целей: %d\n\n", len(finalResults))
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
	fmt.Println("            РЕКОМЕНДУЕМАЯ КОНФИГУРАЦИЯ REALITY (HTTP/2)")
	fmt.Println(strings.Repeat("=", 115))
	fmt.Printf("\"dest\": \"%s\",\n", best.Dest)
	fmt.Println("\"serverNames\": [")
	fmt.Printf("  \"%s\"\n", best.SNI)
	fmt.Println("]")
	fmt.Printf("\nПараметры: ALPN: %s, HTTP Status: %s, Server: %s, Body: %d B, RTT: %d ms\n",
		best.ALPN, best.Status, best.Server, best.DataBytes, best.RTT)
}

func limitStr(s string, limit int) string {
	if len(s) > limit {
		return s[:limit]
	}
	return s
}
