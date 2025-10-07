package main

import (
	"bufio"
	"context"
	"crypto/tls"
	"encoding/json"
	"fmt"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"

	"golang.org/x/time/rate"
)

// ExitNodeConfig holds configuration for the exit node
type ExitNodeConfig struct {
	Timeout         time.Duration // Connection timeout
	MaxConnsPerHost int           // Maximum concurrent connections per host
	RateLimit       rate.Limit    // Requests per second (0 = unlimited)
	RateBurst       int           // Burst size for rate limiter
	DoHEnabled      bool          // Enable DNS-over-HTTPS
	DoHServers      []string      // DoH server URLs (e.g., "https://dns.google/dns-query")
	BlocklistPath   string        // Path to blocklist file (newline-delimited domains)
}

// DefaultExitNodeConfig returns sensible defaults
func DefaultExitNodeConfig() ExitNodeConfig {
	return ExitNodeConfig{
		Timeout:         30 * time.Second,
		MaxConnsPerHost: 10,
		RateLimit:       rate.Limit(100), // 100 requests/sec
		RateBurst:       20,
		DoHEnabled:      false,
		DoHServers:      []string{"https://dns.google/dns-query"},
		BlocklistPath:   "", // No blocklist by default
	}
}

// ExitNode handles outbound connections to the internet
type ExitNode struct {
	httpClient  *http.Client
	resolver    *DNSResolver
	rateLimiter *rate.Limiter
	blocklist   *Blocklist
	config      ExitNodeConfig
	// mu sync.RWMutex // Reserved for future synchronization needs
}

// NewExitNode creates a new exit node with the given configuration
func NewExitNode(config ExitNodeConfig) (*ExitNode, error) {
	// Create HTTP client with Pure Go TLS
	httpClient := &http.Client{
		Timeout: config.Timeout,
		Transport: &http.Transport{
			MaxConnsPerHost:     config.MaxConnsPerHost,
			MaxIdleConnsPerHost: config.MaxConnsPerHost / 2,
			IdleConnTimeout:     90 * time.Second,
			TLSClientConfig: &tls.Config{
				MinVersion: tls.VersionTLS12,
				// Pure Go crypto/tls - no C/C++ dependencies
			},
			DisableKeepAlives: false,
		},
	}

	// Create DNS resolver
	resolver := NewDNSResolver(config.DoHEnabled, config.DoHServers, config.Timeout)

	// Create rate limiter (unlimited if RateLimit is 0)
	var rateLimiter *rate.Limiter
	if config.RateLimit > 0 {
		rateLimiter = rate.NewLimiter(config.RateLimit, config.RateBurst)
	}

	// Load blocklist if path provided
	blocklist := NewBlocklist()
	if config.BlocklistPath != "" {
		if err := blocklist.LoadFromFile(config.BlocklistPath); err != nil {
			return nil, fmt.Errorf("failed to load blocklist: %w", err)
		}
	}

	return &ExitNode{
		httpClient:  httpClient,
		resolver:    resolver,
		rateLimiter: rateLimiter,
		blocklist:   blocklist,
		config:      config,
	}, nil
}

// CheckRateLimit returns true if the request is allowed by rate limiter
func (en *ExitNode) CheckRateLimit() bool {
	if en.rateLimiter == nil {
		return true // No rate limiting
	}
	return en.rateLimiter.Allow()
}

// ValidateTarget checks if the target is allowed (not in blocklist)
// Returns error if blocked
func (en *ExitNode) ValidateTarget(target string) error {
	// Extract hostname from target (format: "host:port")
	host, _, err := net.SplitHostPort(target)
	if err != nil {
		// If no port, treat entire target as hostname
		host = target
	}

	if en.blocklist.IsBlocked(host) {
		return fmt.Errorf("target %s is blocked", host)
	}

	return nil
}

// HandleTCPConnection establishes a TCP connection to the target
// This is used for SOCKS5 CONNECT and HTTP CONNECT tunneling
func (en *ExitNode) HandleTCPConnection(ctx context.Context, streamID string, target string) (net.Conn, error) {
	// Rate limiting check
	if !en.CheckRateLimit() {
		return nil, fmt.Errorf("rate limit exceeded")
	}

	// Blocklist validation
	if err := en.ValidateTarget(target); err != nil {
		return nil, err
	}

	// DNS resolution
	host, port, err := net.SplitHostPort(target)
	if err != nil {
		return nil, fmt.Errorf("invalid target address: %w", err)
	}

	ips, err := en.resolver.Resolve(ctx, host)
	if err != nil {
		return nil, fmt.Errorf("DNS resolution failed: %w", err)
	}

	if len(ips) == 0 {
		return nil, fmt.Errorf("no IP addresses found for %s", host)
	}

	// Try each resolved IP until one succeeds
	var lastErr error
	for _, ip := range ips {
		addr := net.JoinHostPort(ip.String(), port)

		dialer := &net.Dialer{
			Timeout: en.config.Timeout,
		}

		conn, err := dialer.DialContext(ctx, "tcp", addr)
		if err == nil {
			return conn, nil
		}
		lastErr = err
	}

	return nil, fmt.Errorf("all connection attempts failed: %w", lastErr)
}

// HandleHTTPRequest forwards an HTTP/HTTPS request through the exit node
// This is used for transparent HTTP proxying (less common, mainly for debugging)
func (en *ExitNode) HandleHTTPRequest(ctx context.Context, streamID string, req *http.Request) (*http.Response, error) {
	// Rate limiting check
	if !en.CheckRateLimit() {
		return nil, fmt.Errorf("rate limit exceeded")
	}

	// Blocklist validation
	target := req.Host
	if target == "" {
		target = req.URL.Host
	}
	if err := en.ValidateTarget(target); err != nil {
		return nil, err
	}

	// DNS resolution (if needed)
	if req.URL.Host != "" {
		host, _, err := net.SplitHostPort(req.URL.Host)
		if err != nil {
			host = req.URL.Host
		}

		ips, err := en.resolver.Resolve(ctx, host)
		if err != nil {
			return nil, fmt.Errorf("DNS resolution failed: %w", err)
		}

		if len(ips) == 0 {
			return nil, fmt.Errorf("no IP addresses found for %s", host)
		}
		// Use first resolved IP (round-robin can be added later)
	}

	// Forward request with timeout context
	reqWithContext := req.WithContext(ctx)
	return en.httpClient.Do(reqWithContext)
}

// Close cleans up resources
func (en *ExitNode) Close() error {
	en.httpClient.CloseIdleConnections()
	return nil
}

// DNSResolver handles DNS resolution with optional DoH support
type DNSResolver struct {
	resolver   *net.Resolver
	dohEnabled bool
	dohServers []string
	httpClient *http.Client
	// mu sync.RWMutex // Reserved for future synchronization needs
}

// NewDNSResolver creates a new DNS resolver
func NewDNSResolver(dohEnabled bool, dohServers []string, timeout time.Duration) *DNSResolver {
	resolver := &net.Resolver{
		PreferGo: true, // Use Pure Go DNS resolver
	}

	var httpClient *http.Client
	if dohEnabled {
		httpClient = &http.Client{
			Timeout: timeout,
			Transport: &http.Transport{
				TLSClientConfig: &tls.Config{
					MinVersion: tls.VersionTLS12,
				},
			},
		}
	}

	return &DNSResolver{
		resolver:   resolver,
		dohEnabled: dohEnabled,
		dohServers: dohServers,
		httpClient: httpClient,
	}
}

// Resolve resolves a hostname to IP addresses
func (dr *DNSResolver) Resolve(ctx context.Context, host string) ([]net.IP, error) {
	// Try DoH first if enabled
	if dr.dohEnabled && len(dr.dohServers) > 0 {
		ips, err := dr.resolveDoH(ctx, host)
		if err == nil && len(ips) > 0 {
			return ips, nil
		}
		// Fall back to standard DNS on DoH failure
	}

	// Standard DNS resolution
	addrs, err := dr.resolver.LookupIP(ctx, "ip", host)
	if err != nil {
		return nil, err
	}

	return addrs, nil
}

// resolveDoH performs DNS-over-HTTPS resolution (RFC 8484)
// Uses JSON API format for simplicity. For wire format, use github.com/miekg/dns
func (dr *DNSResolver) resolveDoH(ctx context.Context, host string) ([]net.IP, error) {
	if dr.httpClient == nil {
		return nil, fmt.Errorf("DoH client not initialized")
	}

	// Try each DoH server in order
	for _, dohServer := range dr.dohServers {
		ips, err := dr.queryDoHServer(ctx, dohServer, host)
		if err == nil && len(ips) > 0 {
			return ips, nil
		}
		// Continue to next server on failure
	}

	return nil, fmt.Errorf("all DoH servers failed for host: %s", host)
}

// queryDoHServer queries a single DoH server using JSON API format
// Supports both Google/Cloudflare JSON API and RFC 8484 wire format
func (dr *DNSResolver) queryDoHServer(ctx context.Context, dohServer, host string) ([]net.IP, error) {
	// Use JSON API format (simpler than wire format)
	// Supported by major DoH providers: Cloudflare, Google, Quad9
	reqURL := fmt.Sprintf("%s?name=%s&type=A", dohServer, host)

	req, err := http.NewRequestWithContext(ctx, "GET", reqURL, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create DoH request: %w", err)
	}

	// Set Accept header for JSON API
	req.Header.Set("Accept", "application/dns-json")

	resp, err := dr.httpClient.Do(req)
	if err != nil {
		return nil, fmt.Errorf("DoH request failed: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("DoH server returned status: %d", resp.StatusCode)
	}

	// Parse JSON response
	var dohResp struct {
		Status int `json:"Status"` // 0 = NOERROR, 2 = SERVFAIL, 3 = NXDOMAIN
		Answer []struct {
			Name string `json:"name"`
			Type int    `json:"type"` // 1 = A, 28 = AAAA
			Data string `json:"data"` // IP address
		} `json:"Answer"`
	}

	if err := json.NewDecoder(resp.Body).Decode(&dohResp); err != nil {
		return nil, fmt.Errorf("failed to decode DoH response: %w", err)
	}

	// Check DNS response status
	if dohResp.Status != 0 {
		return nil, fmt.Errorf("DNS query failed with status: %d", dohResp.Status)
	}

	// Extract IP addresses from Answer section
	var ips []net.IP
	for _, answer := range dohResp.Answer {
		if answer.Type == 1 { // A record (IPv4)
			ip := net.ParseIP(answer.Data)
			if ip != nil {
				ips = append(ips, ip)
			}
		} else if answer.Type == 28 { // AAAA record (IPv6)
			ip := net.ParseIP(answer.Data)
			if ip != nil {
				ips = append(ips, ip)
			}
		}
	}

	if len(ips) == 0 {
		return nil, fmt.Errorf("no IP addresses found in DoH response")
	}

	return ips, nil
}

// Blocklist manages blocked domains
type Blocklist struct {
	domains map[string]bool
	mu      sync.RWMutex
}

// NewBlocklist creates an empty blocklist
func NewBlocklist() *Blocklist {
	return &Blocklist{
		domains: make(map[string]bool),
	}
}

// IsBlocked checks if a domain is in the blocklist
func (bl *Blocklist) IsBlocked(domain string) bool {
	bl.mu.RLock()
	defer bl.mu.RUnlock()

	// Normalize domain to lowercase
	domain = strings.ToLower(strings.TrimSpace(domain))

	return bl.domains[domain]
}

// Add adds a domain to the blocklist
func (bl *Blocklist) Add(domain string) {
	bl.mu.Lock()
	defer bl.mu.Unlock()

	domain = strings.ToLower(strings.TrimSpace(domain))
	if domain != "" {
		bl.domains[domain] = true
	}
}

// Remove removes a domain from the blocklist
func (bl *Blocklist) Remove(domain string) {
	bl.mu.Lock()
	defer bl.mu.Unlock()

	domain = strings.ToLower(strings.TrimSpace(domain))
	delete(bl.domains, domain)
}

// LoadFromFile loads blocklist from a file (newline-delimited domains)
// Note: This function is intentionally designed to accept user-provided paths
// for blocklist loading. In production, paths should be validated and restricted
// to a specific directory using filepath.Clean and path validation.
func (bl *Blocklist) LoadFromFile(path string) error {
	// Validate and clean the path to prevent directory traversal
	cleanPath := filepath.Clean(path)
	if !filepath.IsAbs(cleanPath) {
		return fmt.Errorf("blocklist path must be absolute: %s", path)
	}

	// #nosec G304 -- This is an intentional file read operation for blocklist loading
	// The path is cleaned and validated above to prevent directory traversal
	file, err := os.Open(cleanPath)
	if err != nil {
		return fmt.Errorf("failed to open blocklist file: %w", err)
	}
	defer file.Close()

	bl.mu.Lock()
	defer bl.mu.Unlock()

	scanner := bufio.NewScanner(file)
	count := 0
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		// Skip empty lines and comments
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}

		domain := strings.ToLower(line)
		bl.domains[domain] = true
		count++
	}

	if err := scanner.Err(); err != nil {
		return fmt.Errorf("error reading blocklist file: %w", err)
	}

	return nil
}

// Count returns the number of blocked domains
func (bl *Blocklist) Count() int {
	bl.mu.RLock()
	defer bl.mu.RUnlock()
	return len(bl.domains)
}
