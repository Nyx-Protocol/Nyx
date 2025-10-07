package main

import (
	"context"
	"net"
	"net/http"
	"net/http/httptest"
	"os"
	"testing"
	"time"

	"golang.org/x/time/rate"
)

func TestDefaultExitNodeConfig(t *testing.T) {
	config := DefaultExitNodeConfig()

	if config.Timeout != 30*time.Second {
		t.Errorf("Expected timeout 30s, got %v", config.Timeout)
	}

	if config.MaxConnsPerHost != 10 {
		t.Errorf("Expected max conns 10, got %d", config.MaxConnsPerHost)
	}

	if config.RateLimit != rate.Limit(100) {
		t.Errorf("Expected rate limit 100, got %v", config.RateLimit)
	}
}

func TestNewExitNode(t *testing.T) {
	config := DefaultExitNodeConfig()
	exitNode, err := NewExitNode(config)

	if err != nil {
		t.Fatalf("Failed to create exit node: %v", err)
	}

	if exitNode.httpClient == nil {
		t.Error("HTTP client should not be nil")
	}

	if exitNode.resolver == nil {
		t.Error("DNS resolver should not be nil")
	}

	if exitNode.rateLimiter == nil {
		t.Error("Rate limiter should not be nil when RateLimit > 0")
	}

	defer exitNode.Close()
}

func TestExitNodeRateLimiting(t *testing.T) {
	config := DefaultExitNodeConfig()
	config.RateLimit = rate.Limit(2) // 2 requests per second
	config.RateBurst = 2             // Allow 2 tokens in burst

	exitNode, err := NewExitNode(config)
	if err != nil {
		t.Fatalf("Failed to create exit node: %v", err)
	}
	defer exitNode.Close()

	// First request should succeed
	if !exitNode.CheckRateLimit() {
		t.Error("First request should be allowed")
	}

	// Second immediate request should succeed (burst)
	if !exitNode.CheckRateLimit() {
		t.Error("Burst request should be allowed")
	}

	// Third immediate request should fail (rate limit exceeded)
	if exitNode.CheckRateLimit() {
		t.Error("Third request should be rate limited")
	}

	// Wait for rate limiter to refill (500ms = 1 token at 2 req/sec)
	time.Sleep(600 * time.Millisecond)

	// Should succeed after waiting
	if !exitNode.CheckRateLimit() {
		t.Error("Request should be allowed after waiting")
	}
}

func TestExitNodeNoRateLimiting(t *testing.T) {
	config := DefaultExitNodeConfig()
	config.RateLimit = 0 // Unlimited

	exitNode, err := NewExitNode(config)
	if err != nil {
		t.Fatalf("Failed to create exit node: %v", err)
	}
	defer exitNode.Close()

	if exitNode.rateLimiter != nil {
		t.Error("Rate limiter should be nil when RateLimit is 0")
	}

	// All requests should succeed
	for i := 0; i < 100; i++ {
		if !exitNode.CheckRateLimit() {
			t.Errorf("Request %d should be allowed (unlimited)", i)
		}
	}
}

func TestBlocklistBasic(t *testing.T) {
	bl := NewBlocklist()

	if bl.Count() != 0 {
		t.Errorf("New blocklist should be empty, got %d domains", bl.Count())
	}

	bl.Add("example.com")
	bl.Add("evil.org")

	if bl.Count() != 2 {
		t.Errorf("Expected 2 domains, got %d", bl.Count())
	}

	if !bl.IsBlocked("example.com") {
		t.Error("example.com should be blocked")
	}

	if !bl.IsBlocked("EXAMPLE.COM") {
		t.Error("EXAMPLE.COM should be blocked (case insensitive)")
	}

	if bl.IsBlocked("google.com") {
		t.Error("google.com should not be blocked")
	}

	bl.Remove("example.com")

	if bl.IsBlocked("example.com") {
		t.Error("example.com should no longer be blocked")
	}

	if bl.Count() != 1 {
		t.Errorf("Expected 1 domain after removal, got %d", bl.Count())
	}
}

func TestBlocklistLoadFromFile(t *testing.T) {
	// Create temporary blocklist file
	tmpfile, err := os.CreateTemp("", "blocklist-*.txt")
	if err != nil {
		t.Fatal(err)
	}
	defer os.Remove(tmpfile.Name())

	content := `# This is a comment
example.com
evil.org

# Another comment
malware.net
`

	if _, err := tmpfile.Write([]byte(content)); err != nil {
		t.Fatal(err)
	}
	if err := tmpfile.Close(); err != nil {
		t.Fatal(err)
	}

	bl := NewBlocklist()
	if err := bl.LoadFromFile(tmpfile.Name()); err != nil {
		t.Fatalf("Failed to load blocklist: %v", err)
	}

	if bl.Count() != 3 {
		t.Errorf("Expected 3 domains, got %d", bl.Count())
	}

	if !bl.IsBlocked("example.com") {
		t.Error("example.com should be blocked")
	}

	if !bl.IsBlocked("evil.org") {
		t.Error("evil.org should be blocked")
	}

	if !bl.IsBlocked("malware.net") {
		t.Error("malware.net should be blocked")
	}
}

func TestExitNodeValidateTarget(t *testing.T) {
	config := DefaultExitNodeConfig()
	exitNode, err := NewExitNode(config)
	if err != nil {
		t.Fatalf("Failed to create exit node: %v", err)
	}
	defer exitNode.Close()

	// Add some blocked domains
	exitNode.blocklist.Add("blocked.com")
	exitNode.blocklist.Add("evil.org")

	tests := []struct {
		target      string
		shouldBlock bool
	}{
		{"example.com:443", false},
		{"blocked.com:443", true},
		{"BLOCKED.COM:80", true}, // Case insensitive
		{"evil.org:8080", true},
		{"google.com", false},
		{"192.168.1.1:8080", false}, // IP addresses not in blocklist
	}

	for _, tt := range tests {
		err := exitNode.ValidateTarget(tt.target)
		blocked := (err != nil)

		if blocked != tt.shouldBlock {
			t.Errorf("Target %s: expected blocked=%v, got blocked=%v",
				tt.target, tt.shouldBlock, blocked)
		}
	}
}

func TestDNSResolverStandard(t *testing.T) {
	resolver := NewDNSResolver(false, nil, 5*time.Second)

	ctx := context.Background()
	ips, err := resolver.Resolve(ctx, "localhost")
	if err != nil {
		t.Fatalf("Failed to resolve localhost: %v", err)
	}

	if len(ips) == 0 {
		t.Error("Expected at least one IP for localhost")
	}

	// Check for loopback address
	hasLoopback := false
	for _, ip := range ips {
		if ip.IsLoopback() {
			hasLoopback = true
			break
		}
	}

	if !hasLoopback {
		t.Error("Expected at least one loopback IP for localhost")
	}
}

func TestDNSResolverInvalidHost(t *testing.T) {
	resolver := NewDNSResolver(false, nil, 5*time.Second)

	ctx := context.Background()
	_, err := resolver.Resolve(ctx, "this-domain-does-not-exist-12345.invalid")
	if err == nil {
		t.Error("Expected error for invalid domain")
	}
}

func TestDNSResolverDoHFallback(t *testing.T) {
	// Enable DoH but it should fall back to standard DNS
	resolver := NewDNSResolver(true, []string{"https://dns.google/dns-query"}, 5*time.Second)

	ctx := context.Background()
	ips, err := resolver.Resolve(ctx, "localhost")
	if err != nil {
		t.Fatalf("Failed to resolve localhost with DoH fallback: %v", err)
	}

	if len(ips) == 0 {
		t.Error("Expected at least one IP for localhost")
	}
}

func TestExitNodeHandleHTTPRequest(t *testing.T) {
	// Create a test HTTP server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
		if _, err := w.Write([]byte("Hello from test server")); err != nil {
			t.Logf("Write error: %v", err)
		}
	}))
	defer server.Close()

	config := DefaultExitNodeConfig()
	config.RateLimit = 0 // Disable rate limiting for test
	exitNode, err := NewExitNode(config)
	if err != nil {
		t.Fatalf("Failed to create exit node: %v", err)
	}
	defer exitNode.Close()

	// Create HTTP request
	req, err := http.NewRequest("GET", server.URL, nil)
	if err != nil {
		t.Fatalf("Failed to create request: %v", err)
	}

	ctx := context.Background()
	resp, err := exitNode.HandleHTTPRequest(ctx, "test-stream-1", req)
	if err != nil {
		t.Fatalf("Failed to handle HTTP request: %v", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		t.Errorf("Expected status 200, got %d", resp.StatusCode)
	}
}

func TestExitNodeHandleTCPConnection(t *testing.T) {
	// Create a test TCP server
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("Failed to create listener: %v", err)
	}
	defer listener.Close()

	// Accept connections in background
	go func() {
		conn, err := listener.Accept()
		if err != nil {
			return
		}
		defer conn.Close()

		// Echo server
		buf := make([]byte, 1024)
		n, err := conn.Read(buf)
		if err != nil {
			return
		}
		if _, err := conn.Write(buf[:n]); err != nil {
			t.Logf("Write error: %v", err)
		}
	}()

	config := DefaultExitNodeConfig()
	config.RateLimit = 0 // Disable rate limiting for test
	exitNode, err := NewExitNode(config)
	if err != nil {
		t.Fatalf("Failed to create exit node: %v", err)
	}
	defer exitNode.Close()

	ctx := context.Background()
	target := listener.Addr().String()
	conn, err := exitNode.HandleTCPConnection(ctx, "test-stream-1", target)
	if err != nil {
		t.Fatalf("Failed to handle TCP connection: %v", err)
	}
	defer conn.Close()

	// Send test data
	testData := []byte("Hello, TCP!")
	_, err = conn.Write(testData)
	if err != nil {
		t.Fatalf("Failed to write to connection: %v", err)
	}

	// Read response
	buf := make([]byte, 1024)
	n, err := conn.Read(buf)
	if err != nil {
		t.Fatalf("Failed to read from connection: %v", err)
	}

	if string(buf[:n]) != string(testData) {
		t.Errorf("Expected echo response %q, got %q", testData, buf[:n])
	}
}

func TestExitNodeHandleTCPConnectionBlocked(t *testing.T) {
	config := DefaultExitNodeConfig()
	config.RateLimit = 0
	exitNode, err := NewExitNode(config)
	if err != nil {
		t.Fatalf("Failed to create exit node: %v", err)
	}
	defer exitNode.Close()

	// Block the target
	exitNode.blocklist.Add("blocked.com")

	ctx := context.Background()
	_, err = exitNode.HandleTCPConnection(ctx, "test-stream-1", "blocked.com:443")
	if err == nil {
		t.Error("Expected error for blocked target")
	}

	if err != nil && !contains(err.Error(), "blocked") {
		t.Errorf("Expected 'blocked' in error message, got: %v", err)
	}
}

func TestExitNodeHandleTCPConnectionRateLimited(t *testing.T) {
	config := DefaultExitNodeConfig()
	config.RateLimit = rate.Limit(1) // 1 request per second
	config.RateBurst = 0
	exitNode, err := NewExitNode(config)
	if err != nil {
		t.Fatalf("Failed to create exit node: %v", err)
	}
	defer exitNode.Close()

	ctx := context.Background()

	// First request should succeed (or fail with connection error, not rate limit)
	_, err1 := exitNode.HandleTCPConnection(ctx, "test-stream-1", "example.com:443")

	// Second immediate request should fail with rate limit
	_, err2 := exitNode.HandleTCPConnection(ctx, "test-stream-2", "example.com:443")

	if err2 == nil {
		t.Error("Expected rate limit error for second request")
	}

	if err2 != nil && !contains(err2.Error(), "rate limit") {
		t.Errorf("Expected 'rate limit' in error message, got: %v", err2)
	}

	// First request may fail with DNS/connection error, that's OK for this test
	_ = err1
}

func TestExitNodeClose(t *testing.T) {
	config := DefaultExitNodeConfig()
	exitNode, err := NewExitNode(config)
	if err != nil {
		t.Fatalf("Failed to create exit node: %v", err)
	}

	err = exitNode.Close()
	if err != nil {
		t.Errorf("Close should not return error: %v", err)
	}
}

// Helper function
func contains(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || len(s) > len(substr) &&
		(s[:len(substr)] == substr || s[len(s)-len(substr):] == substr ||
			len(s) > len(substr)*2 && s[len(s)/2-len(substr)/2:len(s)/2+len(substr)/2+len(substr)%2] == substr))
}
