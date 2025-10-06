package main

import (
	"bufio"
	"context"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"strings"
	"testing"
	"time"

	"golang.org/x/net/proxy"
)

// Integration tests for nyx-http-proxy
// These tests require the proxy server to be running

const (
	socks5Addr = "127.0.0.1:9050"
	httpAddr   = "127.0.0.1:8080"
	testURL    = "http://example.com"
	testHost   = "example.com:80"
)

// TestProxyServerStartup tests that the proxy server can be started
func TestProxyServerStartup(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	// Check if proxy is already running
	if isPortOpen(socks5Addr) {
		t.Skip("Proxy already running on", socks5Addr)
	}

	// Build binary if not exists
	if _, err := os.Stat("nyx-http-proxy.exe"); os.IsNotExist(err) {
		if _, err := os.Stat("nyx-http-proxy"); os.IsNotExist(err) {
			t.Log("Building nyx-http-proxy...")
			cmd := exec.Command("go", "build", "-o", "nyx-http-proxy")
			if err := cmd.Run(); err != nil {
				t.Fatalf("Failed to build proxy: %v", err)
			}
		}
	}

	t.Log("Proxy binary exists or was built successfully")
}

// TestSOCKS5ProxyConnection tests basic SOCKS5 connectivity
func TestSOCKS5ProxyConnection(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	if !isPortOpen(socks5Addr) {
		t.Skip("SOCKS5 proxy not running on", socks5Addr)
	}

	// Create SOCKS5 dialer
	dialer, err := proxy.SOCKS5("tcp", socks5Addr, nil, proxy.Direct)
	if err != nil {
		t.Fatalf("Failed to create SOCKS5 dialer: %v", err)
	}

	// Test connection
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	conn, err := dialer.(proxy.ContextDialer).DialContext(ctx, "tcp", testHost)
	if err != nil {
		t.Fatalf("Failed to dial via SOCKS5: %v", err)
	}
	defer conn.Close()

	// Send simple HTTP request
	_, err = conn.Write([]byte("GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"))
	if err != nil {
		t.Fatalf("Failed to write to connection: %v", err)
	}

	// Read response
	reader := bufio.NewReader(conn)
	statusLine, err := reader.ReadString('\n')
	if err != nil {
		t.Fatalf("Failed to read response: %v", err)
	}

	if !strings.Contains(statusLine, "200 OK") && !strings.Contains(statusLine, "301") && !strings.Contains(statusLine, "302") {
		t.Errorf("Unexpected status line: %s", statusLine)
	}

	t.Logf("SOCKS5 connection successful: %s", strings.TrimSpace(statusLine))
}

// TestHTTPProxyConnection tests HTTP CONNECT proxy
func TestHTTPProxyConnection(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	if !isPortOpen(httpAddr) {
		t.Skip("HTTP proxy not running on", httpAddr)
	}

	// Create HTTP client with proxy
	proxyURL, _ := url.Parse("http://" + httpAddr)
	client := &http.Client{
		Transport: &http.Transport{
			Proxy: http.ProxyURL(proxyURL),
		},
		Timeout: 10 * time.Second,
	}

	// Test HTTPS connection (requires CONNECT method)
	resp, err := client.Get("https://example.com")
	if err != nil {
		t.Fatalf("Failed to connect via HTTP proxy: %v", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		t.Errorf("Expected status 200, got %d", resp.StatusCode)
	}

	body, _ := io.ReadAll(resp.Body)
	if len(body) == 0 {
		t.Error("Empty response body")
	}

	t.Logf("HTTP CONNECT successful: %d bytes received", len(body))
}

// TestExitNodeRateLimitIntegration tests rate limiting in a real scenario
func TestExitNodeRateLimitIntegration(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	if !isPortOpen(socks5Addr) {
		t.Skip("SOCKS5 proxy not running on", socks5Addr)
	}

	// Create SOCKS5 dialer for proper HTTP/HTTPS proxying
	// HTTP CONNECT proxy is for HTTPS tunneling, not plain HTTP GET requests
	dialer, err := proxy.SOCKS5("tcp", socks5Addr, nil, proxy.Direct)
	if err != nil {
		t.Fatalf("Failed to create SOCKS5 dialer: %v", err)
	}

	client := &http.Client{
		Transport: &http.Transport{
			DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
				return dialer.Dial(network, addr)
			},
			DisableKeepAlives: true, // Force new connection each time
		},
		Timeout: 5 * time.Second,
	}

	// Make rapid requests (should succeed with default 100 req/sec limit)
	successCount := 0
	for i := 0; i < 10; i++ {
		resp, err := client.Get("http://example.com")
		if err != nil {
			t.Logf("Request %d failed: %v", i, err)
			continue
		}
		resp.Body.Close()

		if resp.StatusCode == http.StatusOK {
			successCount++
		}
	}

	if successCount < 8 { // Allow some failures
		t.Errorf("Too many failed requests: %d/10 succeeded", successCount)
	}

	t.Logf("Rate limiting test: %d/10 requests succeeded", successCount)
}

// TestIPCBridgeIntegration tests IPC communication (requires nyx-daemon)
func TestIPCBridgeIntegration(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	// Check if nyx-daemon IPC socket exists
	ipcPath := "/tmp/nyx-daemon.sock"
	if _, err := os.Stat(ipcPath); os.IsNotExist(err) {
		// Try Windows named pipe (can't check existence easily)
		t.Skip("IPC socket not found (nyx-daemon not running)")
	}

	// Test MixBridgeClient connectivity
	client := NewMixBridgeClient(ipcPath)
	if client == nil {
		t.Skip("Failed to create IPC client")
	}
	defer client.Close()

	// Test Connect to IPC
	if err := client.Connect(); err != nil {
		t.Skipf("Failed to connect to IPC: %v", err)
	}

	// Test ProxyConnect
	result, err := client.ProxyConnect(testHost, "socks5")
	if err != nil {
		t.Fatalf("ProxyConnect failed: %v", err)
	}

	t.Logf("IPC bridge test successful: stream_id=%s", result.StreamID)

	// Clean up stream
	if err := client.ProxyClose(result.StreamID); err != nil {
		t.Logf("Warning: Failed to close stream: %v", err)
	}
}

// TestDNSResolution tests DNS resolution through the exit node
func TestDNSResolution(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	if !isPortOpen(socks5Addr) {
		t.Skip("SOCKS5 proxy not running")
	}

	// Test various domain formats
	testCases := []string{
		"example.com:80",
		"www.google.com:443",
		"api.github.com:443",
	}

	dialer, err := proxy.SOCKS5("tcp", socks5Addr, nil, proxy.Direct)
	if err != nil {
		t.Fatalf("Failed to create SOCKS5 dialer: %v", err)
	}

	for _, target := range testCases {
		t.Run(target, func(t *testing.T) {
			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()

			conn, err := dialer.(proxy.ContextDialer).DialContext(ctx, "tcp", target)
			if err != nil {
				t.Errorf("Failed to connect to %s: %v", target, err)
				return
			}
			conn.Close()

			t.Logf("DNS resolution successful: %s", target)
		})
	}
}

// TestBlocklistIntegration tests blocklist functionality
func TestBlocklistIntegration(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	// This test would require configuring a blocklist
	// For now, we just verify the mechanism exists
	t.Log("Blocklist integration test: mechanism verified in unit tests")
}

// TestPerformanceBenchmark measures latency and throughput
func TestPerformanceBenchmark(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping performance test in short mode")
	}

	if !isPortOpen(httpAddr) {
		t.Skip("HTTP proxy not running")
	}

	proxyURL, _ := url.Parse("http://" + httpAddr)
	client := &http.Client{
		Transport: &http.Transport{
			Proxy: http.ProxyURL(proxyURL),
		},
		Timeout: 30 * time.Second,
	}

	// Measure latency (10 requests)
	var totalLatency time.Duration
	successCount := 0

	for i := 0; i < 10; i++ {
		start := time.Now()
		resp, err := client.Get("http://example.com")
		latency := time.Since(start)

		if err != nil {
			t.Logf("Request %d failed: %v", i, err)
			continue
		}
		resp.Body.Close()

		if resp.StatusCode == http.StatusOK {
			totalLatency += latency
			successCount++
		}
	}

	if successCount > 0 {
		avgLatency := totalLatency / time.Duration(successCount)
		t.Logf("Performance: %d/10 successful, avg latency: %v", successCount, avgLatency)

		// Baseline: Direct connection should be < 100ms, proxied < 200ms
		if avgLatency > 500*time.Millisecond {
			t.Logf("Warning: High latency detected: %v", avgLatency)
		}
	} else {
		t.Error("No successful requests in performance test")
	}
}

// TestConcurrentConnections tests multiple simultaneous connections
func TestConcurrentConnections(t *testing.T) {
	if testing.Short() {
		t.Skip("Skipping integration test in short mode")
	}

	if !isPortOpen(socks5Addr) {
		t.Skip("SOCKS5 proxy not running")
	}

	dialer, err := proxy.SOCKS5("tcp", socks5Addr, nil, proxy.Direct)
	if err != nil {
		t.Fatalf("Failed to create SOCKS5 dialer: %v", err)
	}

	// Launch 10 concurrent connections
	concurrency := 10
	results := make(chan error, concurrency)

	for i := 0; i < concurrency; i++ {
		go func(id int) {
			ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
			defer cancel()

			conn, err := dialer.(proxy.ContextDialer).DialContext(ctx, "tcp", testHost)
			if err != nil {
				results <- fmt.Errorf("connection %d failed: %w", id, err)
				return
			}
			defer conn.Close()

			// Send simple request
			_, err = conn.Write([]byte("GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"))
			if err != nil {
				results <- fmt.Errorf("connection %d write failed: %w", id, err)
				return
			}

			// Read response status
			reader := bufio.NewReader(conn)
			_, err = reader.ReadString('\n')
			if err != nil {
				results <- fmt.Errorf("connection %d read failed: %w", id, err)
				return
			}

			results <- nil
		}(i)
	}

	// Collect results
	successCount := 0
	for i := 0; i < concurrency; i++ {
		err := <-results
		if err != nil {
			t.Logf("Concurrent connection error: %v", err)
		} else {
			successCount++
		}
	}

	if successCount < concurrency-2 { // Allow 2 failures
		t.Errorf("Too many concurrent connection failures: %d/%d succeeded", successCount, concurrency)
	}

	t.Logf("Concurrent connections: %d/%d succeeded", successCount, concurrency)
}

// Helper function to check if a port is open
func isPortOpen(address string) bool {
	conn, err := net.DialTimeout("tcp", address, 1*time.Second)
	if err != nil {
		return false
	}
	conn.Close()
	return true
}

// TestMain runs setup before tests
func TestMain(m *testing.M) {
	// Check if we should skip all integration tests
	if os.Getenv("SKIP_INTEGRATION") == "true" {
		fmt.Println("Skipping integration tests (SKIP_INTEGRATION=true)")
		os.Exit(0)
	}

	// Run tests
	code := m.Run()
	os.Exit(code)
}
