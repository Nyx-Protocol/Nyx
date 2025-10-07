package main

import (
	"encoding/binary"
	"io"
	"net"
	"testing"
	"time"
)

// mockConn is a mock net.Conn for testing
type mockConn struct {
	readBuf  []byte
	writeBuf []byte
	readPos  int
}

func (m *mockConn) Read(b []byte) (n int, err error) {
	if m.readPos >= len(m.readBuf) {
		return 0, io.EOF
	}
	n = copy(b, m.readBuf[m.readPos:])
	m.readPos += n
	return n, nil
}

func (m *mockConn) Write(b []byte) (n int, err error) {
	m.writeBuf = append(m.writeBuf, b...)
	return len(b), nil
}

func (m *mockConn) Close() error                       { return nil }
func (m *mockConn) LocalAddr() net.Addr                { return &net.TCPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 1234} }
func (m *mockConn) RemoteAddr() net.Addr               { return &net.TCPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 5678} }
func (m *mockConn) SetDeadline(t time.Time) error      { return nil }
func (m *mockConn) SetReadDeadline(t time.Time) error  { return nil }
func (m *mockConn) SetWriteDeadline(t time.Time) error { return nil }

// Test SOCKS5 authentication handshake (no-auth)
func TestSOCKS5Auth_NoAuth(t *testing.T) {
	stats := &Stats{}
	server := &SOCKS5Server{stats: stats}

	// Client greeting: [VER=0x05, NMETHODS=1, METHOD=0x00 (no-auth)]
	conn := &mockConn{
		readBuf: []byte{0x05, 0x01, 0x00},
	}

	err := server.handleAuth(conn)
	if err != nil {
		t.Fatalf("handleAuth failed: %v", err)
	}

	// Verify reply: [VER=0x05, METHOD=0x00]
	expectedReply := []byte{0x05, 0x00}
	if len(conn.writeBuf) != 2 {
		t.Fatalf("expected reply length 2, got %d", len(conn.writeBuf))
	}
	if conn.writeBuf[0] != expectedReply[0] || conn.writeBuf[1] != expectedReply[1] {
		t.Errorf("expected reply %v, got %v", expectedReply, conn.writeBuf)
	}
}

// Test SOCKS5 authentication with invalid version
func TestSOCKS5Auth_InvalidVersion(t *testing.T) {
	stats := &Stats{}
	server := &SOCKS5Server{stats: stats}

	// Client greeting with invalid version
	conn := &mockConn{
		readBuf: []byte{0x04, 0x01, 0x00}, // SOCKS4, not SOCKS5
	}

	err := server.handleAuth(conn)
	if err != errSOCKS5InvalidVersion {
		t.Errorf("expected errSOCKS5InvalidVersion, got %v", err)
	}
}

// Test SOCKS5 authentication with no acceptable method
func TestSOCKS5Auth_NoAcceptableMethod(t *testing.T) {
	stats := &Stats{}
	server := &SOCKS5Server{stats: stats}

	// Client greeting: [VER=0x05, NMETHODS=1, METHOD=0x02 (password auth)]
	// Server only supports no-auth (0x00)
	conn := &mockConn{
		readBuf: []byte{0x05, 0x01, 0x02},
	}

	err := server.handleAuth(conn)
	if err != errSOCKS5NoAcceptableAuth {
		t.Errorf("expected errSOCKS5NoAcceptableAuth, got %v", err)
	}

	// Verify reply: [VER=0x05, METHOD=0xFF (no acceptable)]
	expectedReply := []byte{0x05, 0xFF}
	if len(conn.writeBuf) != 2 {
		t.Fatalf("expected reply length 2, got %d", len(conn.writeBuf))
	}
	if conn.writeBuf[0] != expectedReply[0] || conn.writeBuf[1] != expectedReply[1] {
		t.Errorf("expected reply %v, got %v", expectedReply, conn.writeBuf)
	}
}

// Test SOCKS5 CONNECT request with IPv4 address
func TestSOCKS5Request_IPv4(t *testing.T) {
	stats := &Stats{}
	server := &SOCKS5Server{stats: stats}

	// CONNECT request: [VER, CMD=CONNECT, RSV, ATYP=IPv4, ADDR=93.184.216.34 (example.com), PORT=80]
	requestBuf := []byte{
		0x05,             // VER
		0x01,             // CMD: CONNECT
		0x00,             // RSV
		0x01,             // ATYP: IPv4
		93, 184, 216, 34, // ADDR: 93.184.216.34
		0x00, 0x50, // PORT: 80 (big-endian)
	}

	conn := &mockConn{
		readBuf: requestBuf,
	}

	targetAddr, err := server.handleRequest(conn)
	if err != nil {
		t.Fatalf("handleRequest failed: %v", err)
	}

	expectedAddr := "93.184.216.34:80"
	if targetAddr != expectedAddr {
		t.Errorf("expected target address %s, got %s", expectedAddr, targetAddr)
	}
}

// Test SOCKS5 CONNECT request with domain name
func TestSOCKS5Request_Domain(t *testing.T) {
	stats := &Stats{}
	server := &SOCKS5Server{stats: stats}

	// CONNECT request: [VER, CMD=CONNECT, RSV, ATYP=Domain, LEN=11, DOMAIN=example.com, PORT=443]
	domain := "example.com"
	requestBuf := []byte{
		0x05,              // VER
		0x01,              // CMD: CONNECT
		0x00,              // RSV
		0x03,              // ATYP: Domain
		byte(len(domain)), // Domain length
	}
	requestBuf = append(requestBuf, []byte(domain)...) // Domain name
	requestBuf = append(requestBuf, 0x01, 0xBB)        // PORT: 443 (big-endian)

	conn := &mockConn{
		readBuf: requestBuf,
	}

	targetAddr, err := server.handleRequest(conn)
	if err != nil {
		t.Fatalf("handleRequest failed: %v", err)
	}

	expectedAddr := "example.com:443"
	if targetAddr != expectedAddr {
		t.Errorf("expected target address %s, got %s", expectedAddr, targetAddr)
	}
}

// Test SOCKS5 CONNECT request with IPv6 address
func TestSOCKS5Request_IPv6(t *testing.T) {
	stats := &Stats{}
	server := &SOCKS5Server{stats: stats}

	// CONNECT request: [VER, CMD=CONNECT, RSV, ATYP=IPv6, ADDR=::1, PORT=8080]
	requestBuf := []byte{
		0x05, // VER
		0x01, // CMD: CONNECT
		0x00, // RSV
		0x04, // ATYP: IPv6
		// IPv6 address: ::1 (16 bytes)
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
		0x1F, 0x90, // PORT: 8080 (big-endian)
	}

	conn := &mockConn{
		readBuf: requestBuf,
	}

	targetAddr, err := server.handleRequest(conn)
	if err != nil {
		t.Fatalf("handleRequest failed: %v", err)
	}

	expectedAddr := "[::1]:8080"
	if targetAddr != expectedAddr {
		t.Errorf("expected target address %s, got %s", expectedAddr, targetAddr)
	}
}

// Test SOCKS5 CONNECT request with unsupported command
func TestSOCKS5Request_UnsupportedCommand(t *testing.T) {
	stats := &Stats{}
	server := &SOCKS5Server{stats: stats}

	// BIND request (not supported): [VER, CMD=BIND, RSV, ATYP=IPv4, ...]
	requestBuf := []byte{
		0x05,         // VER
		0x02,         // CMD: BIND (unsupported)
		0x00,         // RSV
		0x01,         // ATYP: IPv4
		127, 0, 0, 1, // ADDR: 127.0.0.1
		0x00, 0x50, // PORT: 80
	}

	conn := &mockConn{
		readBuf: requestBuf,
	}

	_, err := server.handleRequest(conn)
	if err != errSOCKS5CommandNotSupported {
		t.Errorf("expected errSOCKS5CommandNotSupported, got %v", err)
	}

	// Verify error reply was sent: REP=0x07 (command not supported)
	if len(conn.writeBuf) < 4 || conn.writeBuf[1] != socks5RepCommandNotSupported {
		t.Errorf("expected REP=0x07 in reply, got %v", conn.writeBuf)
	}
}

// Test SOCKS5 reply generation
func TestSOCKS5SendReply_Success(t *testing.T) {
	stats := &Stats{}
	server := &SOCKS5Server{stats: stats}

	conn := &mockConn{}
	bindAddr := &net.TCPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 1234}

	err := server.sendReply(conn, socks5RepSuccess, bindAddr)
	if err != nil {
		t.Fatalf("sendReply failed: %v", err)
	}

	// Verify reply format: [VER=0x05, REP=0x00, RSV=0x00, ATYP=0x01, ADDR=127.0.0.1, PORT=1234]
	if len(conn.writeBuf) != 10 { // 4 (header) + 4 (IPv4) + 2 (port)
		t.Fatalf("expected reply length 10, got %d", len(conn.writeBuf))
	}

	// Check header
	if conn.writeBuf[0] != 0x05 || conn.writeBuf[1] != 0x00 || conn.writeBuf[2] != 0x00 || conn.writeBuf[3] != 0x01 {
		t.Errorf("invalid reply header: %v", conn.writeBuf[:4])
	}

	// Check IPv4 address
	expectedIP := []byte{127, 0, 0, 1}
	if !bytesEqual(conn.writeBuf[4:8], expectedIP) {
		t.Errorf("expected IP %v, got %v", expectedIP, conn.writeBuf[4:8])
	}

	// Check port
	port := binary.BigEndian.Uint16(conn.writeBuf[8:10])
	if port != 1234 {
		t.Errorf("expected port 1234, got %d", port)
	}
}

// Test SOCKS5 reply on error
func TestSOCKS5SendReply_Error(t *testing.T) {
	stats := &Stats{}
	server := &SOCKS5Server{stats: stats}

	conn := &mockConn{}

	err := server.sendReply(conn, socks5RepHostUnreachable, nil)
	if err != nil {
		t.Fatalf("sendReply failed: %v", err)
	}

	// Verify error reply: [VER=0x05, REP=0x04, RSV=0x00, ATYP=0x01, ADDR=0.0.0.0, PORT=0]
	if len(conn.writeBuf) != 10 {
		t.Fatalf("expected reply length 10, got %d", len(conn.writeBuf))
	}

	if conn.writeBuf[1] != socks5RepHostUnreachable {
		t.Errorf("expected REP=0x04, got 0x%02x", conn.writeBuf[1])
	}

	// Check zero address
	expectedZero := []byte{0, 0, 0, 0, 0, 0}
	if !bytesEqual(conn.writeBuf[4:10], expectedZero) {
		t.Errorf("expected zero address/port, got %v", conn.writeBuf[4:10])
	}
}

// bytesEqual compares two byte slices
func bytesEqual(a, b []byte) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

// Benchmark SOCKS5 authentication
func BenchmarkSOCKS5Auth(b *testing.B) {
	stats := &Stats{}
	server := &SOCKS5Server{stats: stats}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		conn := &mockConn{
			readBuf: []byte{0x05, 0x01, 0x00},
		}
		_ = server.handleAuth(conn)
	}
}

// Benchmark SOCKS5 request parsing (IPv4)
func BenchmarkSOCKS5Request_IPv4(b *testing.B) {
	stats := &Stats{}
	server := &SOCKS5Server{stats: stats}

	requestBuf := []byte{
		0x05, 0x01, 0x00, 0x01,
		93, 184, 216, 34,
		0x00, 0x50,
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		conn := &mockConn{
			readBuf: requestBuf,
		}
		_, _ = server.handleRequest(conn)
	}
}
