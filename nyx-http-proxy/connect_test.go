package main

import (
	"bufio"
	"fmt"
	"net"
	"strings"
	"testing"
	"time"
)

// Test HTTP CONNECT request parsing (valid request)
func TestHTTPConnectParse_Valid(t *testing.T) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}

	request := "CONNECT example.com:443 HTTP/1.1\r\n" +
		"Host: example.com:443\r\n" +
		"User-Agent: test/1.0\r\n" +
		"\r\n"

	conn := newMockConn([]byte(request))

	targetAddr, authHeader, err := server.parseConnectRequest(conn)
	if err != nil {
		t.Fatalf("parseConnectRequest failed: %v", err)
	}

	expectedAddr := "example.com:443"
	if targetAddr != expectedAddr {
		t.Errorf("expected target %s, got %s", expectedAddr, targetAddr)
	}

	if authHeader != "" {
		t.Errorf("expected no auth header, got %s", authHeader)
	}
}

// Test HTTP CONNECT with Proxy-Authorization header
func TestHTTPConnectParse_WithAuth(t *testing.T) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}

	request := "CONNECT example.com:443 HTTP/1.1\r\n" +
		"Host: example.com:443\r\n" +
		"Proxy-Authorization: Basic dXNlcjpwYXNz\r\n" +
		"\r\n"

	conn := newMockConn([]byte(request))

	targetAddr, authHeader, err := server.parseConnectRequest(conn)
	if err != nil {
		t.Fatalf("parseConnectRequest failed: %v", err)
	}

	if targetAddr != "example.com:443" {
		t.Errorf("unexpected target: %s", targetAddr)
	}

	expectedAuth := "Basic dXNlcjpwYXNz"
	if authHeader != expectedAuth {
		t.Errorf("expected auth %s, got %s", expectedAuth, authHeader)
	}
}

// Test invalid HTTP method (not CONNECT)
func TestHTTPConnectParse_InvalidMethod(t *testing.T) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}

	request := "GET / HTTP/1.1\r\n\r\n"
	conn := newMockConn([]byte(request))

	_, _, err := server.parseConnectRequest(conn)
	if err == nil {
		t.Fatal("expected error for non-CONNECT method")
	}

	if !strings.Contains(err.Error(), "unsupported method") {
		t.Errorf("unexpected error: %v", err)
	}
}

// Test invalid HTTP version
func TestHTTPConnectParse_InvalidVersion(t *testing.T) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}

	request := "CONNECT example.com:443 HTTP/2.0\r\n\r\n"
	conn := newMockConn([]byte(request))

	_, _, err := server.parseConnectRequest(conn)
	if err != errHTTPUnsupportedVersion {
		t.Errorf("expected errHTTPUnsupportedVersion, got %v", err)
	}
}

// Test malformed request line
func TestHTTPConnectParse_MalformedRequest(t *testing.T) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}

	request := "CONNECT\r\n\r\n" // Missing target and version
	conn := newMockConn([]byte(request))

	_, _, err := server.parseConnectRequest(conn)
	if err != errHTTPInvalidRequest {
		t.Errorf("expected errHTTPInvalidRequest, got %v", err)
	}
}

// Test request header too large
func TestHTTPConnectParse_HeaderTooLarge(t *testing.T) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}

	// Generate oversized header
	largeHeader := strings.Repeat("X-Custom-Header: value\r\n", 500) // ~12KB
	request := "CONNECT example.com:443 HTTP/1.1\r\n" + largeHeader + "\r\n"

	conn := newMockConn([]byte(request))

	_, _, err := server.parseConnectRequest(conn)
	if err != errHTTPHeaderTooLarge {
		t.Errorf("expected errHTTPHeaderTooLarge, got %v", err)
	}
}

// Test Basic authentication (valid credentials)
func TestHTTPConnectAuth_Valid(t *testing.T) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}
	server.SetAuth("user", "pass")

	// "user:pass" -> base64 = "dXNlcjpwYXNz"
	authHeader := "Basic dXNlcjpwYXNz"

	err := server.authenticate(authHeader)
	if err != nil {
		t.Fatalf("authenticate failed: %v", err)
	}
}

// Test Basic authentication (invalid credentials)
func TestHTTPConnectAuth_InvalidCredentials(t *testing.T) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}
	server.SetAuth("user", "pass")

	// "wrong:creds" -> base64 = "d3Jvbmc6Y3JlZHM="
	authHeader := "Basic d3Jvbmc6Y3JlZHM="

	err := server.authenticate(authHeader)
	if err != errHTTPAuthFailed {
		t.Errorf("expected errHTTPAuthFailed, got %v", err)
	}
}

// Test authentication missing header
func TestHTTPConnectAuth_Missing(t *testing.T) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}
	server.SetAuth("user", "pass")

	err := server.authenticate("")
	if err != errHTTPAuthRequired {
		t.Errorf("expected errHTTPAuthRequired, got %v", err)
	}
}

// Test authentication with invalid base64
func TestHTTPConnectAuth_InvalidBase64(t *testing.T) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}
	server.SetAuth("user", "pass")

	authHeader := "Basic !!!invalid-base64!!!"

	err := server.authenticate(authHeader)
	if err == nil || !strings.Contains(err.Error(), "invalid base64") {
		t.Errorf("expected base64 error, got %v", err)
	}
}

// Test authentication with unsupported scheme
func TestHTTPConnectAuth_UnsupportedScheme(t *testing.T) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}
	server.SetAuth("user", "pass")

	authHeader := "Digest realm=example"

	err := server.authenticate(authHeader)
	if err == nil || !strings.Contains(err.Error(), "unsupported auth scheme") {
		t.Errorf("expected unsupported scheme error, got %v", err)
	}
}

// Test host validation (valid)
func TestValidateHost_Valid(t *testing.T) {
	testCases := []string{
		"example.com:443",
		"192.168.1.1:8080",
		"[::1]:80",
		"localhost:9050",
	}

	for _, hostPort := range testCases {
		err := validateHost(hostPort)
		if err != nil {
			t.Errorf("validateHost(%s) failed: %v", hostPort, err)
		}
	}
}

// Test host validation (invalid)
func TestValidateHost_Invalid(t *testing.T) {
	testCases := []struct {
		hostPort string
		errMsg   string
	}{
		{"example.com", "invalid host:port format"},         // Missing port
		{"example.com:0", "invalid port"},                   // Port out of range
		{"example.com:65536", "invalid port"},               // Port too large
		{"example.com:abc", "invalid port"},                 // Non-numeric port
		{":443", "invalid host"},                            // Empty hostname
		{strings.Repeat("a", 256) + ":443", "invalid host"}, // Hostname too long
	}

	for _, tc := range testCases {
		err := validateHost(tc.hostPort)
		if err == nil {
			t.Errorf("validateHost(%s) should fail", tc.hostPort)
		} else if !strings.Contains(err.Error(), tc.errMsg) {
			t.Errorf("validateHost(%s) error mismatch: got %v, want substring %s", tc.hostPort, err, tc.errMsg)
		}
	}
}

// Test success response format
func TestHTTPConnectSuccessResponse(t *testing.T) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}

	conn := newMockConn(nil)

	err := server.sendSuccessResponse(conn)
	if err != nil {
		t.Fatalf("sendSuccessResponse failed: %v", err)
	}

	response := string(conn.(*mockNetConn).writeBuf)
	expectedPrefix := "HTTP/1.1 200 Connection established\r\n\r\n"

	if response != expectedPrefix {
		t.Errorf("expected response %q, got %q", expectedPrefix, response)
	}
}

// Test error response format
func TestHTTPConnectErrorResponse(t *testing.T) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}

	conn := newMockConn(nil)

	err := server.sendErrorResponse(conn, httpStatusBadGateway, "Target unreachable")
	if err != nil {
		t.Fatalf("sendErrorResponse failed: %v", err)
	}

	response := string(conn.(*mockNetConn).writeBuf)

	// Verify status line
	if !strings.HasPrefix(response, "HTTP/1.1 502 Bad Gateway") {
		t.Errorf("unexpected status line: %s", response)
	}

	// Verify body
	if !strings.Contains(response, "Target unreachable") {
		t.Errorf("response missing error message: %s", response)
	}
}

// Test HTTP status text mapping
func TestHTTPStatusText(t *testing.T) {
	testCases := []struct {
		code int
		text string
	}{
		{httpStatusOK, "Connection established"},
		{httpStatusBadRequest, "Bad Request"},
		{httpStatusProxyAuthRequired, "Proxy Authentication Required"},
		{httpStatusBadGateway, "Bad Gateway"},
		{httpStatusGatewayTimeout, "Gateway Timeout"},
		{999, "Unknown"},
	}

	for _, tc := range testCases {
		text := getHTTPStatusText(tc.code)
		if text != tc.text {
			t.Errorf("getHTTPStatusText(%d) = %s, want %s", tc.code, text, tc.text)
		}
	}
}

// mockNetConn is a mock net.Conn for testing
type mockNetConn struct {
	readBuf  []byte
	writeBuf []byte
	readPos  int
}

func newMockConn(data []byte) net.Conn {
	return &mockNetConn{readBuf: data}
}

func (m *mockNetConn) Read(b []byte) (n int, err error) {
	if m.readPos >= len(m.readBuf) {
		return 0, fmt.Errorf("EOF")
	}
	n = copy(b, m.readBuf[m.readPos:])
	m.readPos += n
	return n, nil
}

func (m *mockNetConn) Write(b []byte) (n int, err error) {
	m.writeBuf = append(m.writeBuf, b...)
	return len(b), nil
}

func (m *mockNetConn) Close() error { return nil }
func (m *mockNetConn) LocalAddr() net.Addr {
	return &net.TCPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 8080}
}
func (m *mockNetConn) RemoteAddr() net.Addr {
	return &net.TCPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 5678}
}
func (m *mockNetConn) SetDeadline(t time.Time) error      { return nil }
func (m *mockNetConn) SetReadDeadline(t time.Time) error  { return nil }
func (m *mockNetConn) SetWriteDeadline(t time.Time) error { return nil }

// Integration test: HTTP CONNECT server lifecycle
func TestHTTPConnectServerLifecycle(t *testing.T) {
	stats := &Stats{}
	mixBridge := NewMixBridgeClient("/tmp/nyx-mix.sock") // Dummy IPC path for testing

	server, err := NewHTTPConnectServer(":0", stats, mixBridge) // Random port
	if err != nil {
		t.Fatalf("NewHTTPConnectServer failed: %v", err)
	}

	// Start server in background
	go func() {
		server.Serve()
	}()

	// Give server time to start
	time.Sleep(100 * time.Millisecond)

	// Get actual listening address
	addr := server.listener.Addr().String()
	t.Logf("HTTP CONNECT server listening on %s", addr)

	// Test connection
	conn, err := net.DialTimeout("tcp", addr, time.Second)
	if err != nil {
		t.Fatalf("failed to connect to server: %v", err)
	}

	// Send CONNECT request
	request := "CONNECT example.com:443 HTTP/1.1\r\n\r\n"
	_, err = conn.Write([]byte(request))
	if err != nil {
		t.Fatalf("failed to write request: %v", err)
	}

	// Read response (should fail due to no target, but server should respond)
	reader := bufio.NewReader(conn)
	responseLine, err := reader.ReadString('\n')
	if err != nil {
		t.Fatalf("failed to read response: %v", err)
	}

	// Expect HTTP response (success or error)
	if !strings.HasPrefix(responseLine, "HTTP/1.1") {
		t.Errorf("unexpected response: %s", responseLine)
	}

	conn.Close()

	// Shutdown server
	err = server.Close()
	if err != nil {
		t.Fatalf("server close failed: %v", err)
	}

	// Verify statistics
	if stats.TotalConnections.Load() == 0 {
		t.Error("expected non-zero total connections")
	}
	if stats.HTTPConnections.Load() == 0 {
		t.Error("expected non-zero HTTP connections")
	}
}

// Benchmark HTTP CONNECT request parsing
func BenchmarkHTTPConnectParse(b *testing.B) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}

	request := "CONNECT example.com:443 HTTP/1.1\r\n" +
		"Host: example.com:443\r\n" +
		"User-Agent: bench/1.0\r\n" +
		"\r\n"

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		conn := newMockConn([]byte(request))
		server.parseConnectRequest(conn)
	}
}

// Benchmark Basic authentication
func BenchmarkHTTPConnectAuth(b *testing.B) {
	stats := &Stats{}
	server := &HTTPConnectServer{stats: stats}
	server.SetAuth("user", "pass")

	authHeader := "Basic dXNlcjpwYXNz"

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		server.authenticate(authHeader)
	}
}
