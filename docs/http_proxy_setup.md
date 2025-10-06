# HTTP Proxy Setup Guide

## Overview

`nyx-http-proxy` is a Tor-compatible HTTP/SOCKS5 proxy with Mix Network integration for enhanced anonymity. It provides:

- **SOCKS5 Proxy** (RFC 1928): Port 9050 (default)
- **HTTP CONNECT Proxy**: Port 8080 (default)
- **Exit Node**: HTTP/HTTPS client with rate limiting and blocklist
- **Mix Network Integration**: IPC bridge to nyx-daemon for anonymous routing

## Architecture

```
Browser/App → SOCKS5 (9050) or HTTP CONNECT (8080)
              ↓
           nyx-http-proxy (Go)
              ├─ SOCKS5Server
              ├─ HTTPConnectServer
              ├─ ExitNode (HTTP/HTTPS client)
              └─ MixBridgeClient (IPC)
              ↓
           JSON-RPC 2.0 over Unix socket/Named Pipe
              ↓
           nyx-daemon (Rust)
              └─ HttpProxyHandler
              ↓
           [Phase 1: Direct TCP]  ← Current
           [Phase 2: Mix Network] ← Future
              ↓
           Internet
```

## Quick Start

### 1. Build and Run

**Windows (PowerShell)**:
```powershell
cd nyx-http-proxy
go build -o nyx-http-proxy.exe
.\nyx-http-proxy.exe
```

**Linux/macOS (bash)**:
```bash
cd nyx-http-proxy
go build -o nyx-http-proxy
./nyx-http-proxy
```

### 2. Verify Services

Check SOCKS5 (port 9050):
```powershell
Test-NetConnection -ComputerName localhost -Port 9050
```

Check HTTP CONNECT (port 8080):
```powershell
Test-NetConnection -ComputerName localhost -Port 8080
```

### 3. Test with curl

**Via SOCKS5**:
```bash
curl --socks5 127.0.0.1:9050 https://example.com
```

**Via HTTP CONNECT**:
```bash
curl --proxy http://127.0.0.1:8080 https://example.com
```

## Browser Configuration

### Firefox

1. Open **Settings** → **Network Settings**
2. Select **Manual proxy configuration**
3. Set **SOCKS Host**: `127.0.0.1`, **Port**: `9050`
4. Select **SOCKS v5**
5. Check **Proxy DNS when using SOCKS v5**
6. Click **OK**

**Verify**: Visit https://check.torproject.org (should show your exit IP)

### Chrome/Edge

Chrome/Edge use system proxy settings. Configure via:

**Windows**:
1. Settings → Network & Internet → Proxy
2. Enable **Manual proxy setup**
3. Set **Address**: `127.0.0.1`, **Port**: `8080`
4. Save

**Linux (via environment)**:
```bash
export http_proxy=http://127.0.0.1:8080
export https_proxy=http://127.0.0.1:8080
google-chrome
```

## Exit Node Configuration

### Default Configuration

```go
ExitNodeConfig{
    Timeout:         30 * time.Second,
    MaxConnsPerHost: 10,
    RateLimit:       rate.Limit(100), // 100 req/sec
    RateBurst:       20,
    DoHEnabled:      false,
    DoHServers:      []string{"https://dns.google/dns-query"},
    BlocklistPath:   "", // No blocklist
}
```

### Rate Limiting

Token bucket algorithm:
- **RateLimit**: Requests per second (0 = unlimited)
- **RateBurst**: Burst capacity for short spikes

Example: `RateLimit=100, RateBurst=20` allows:
- Steady state: 100 req/sec
- Burst: Up to 20 requests instantly, then 100 req/sec

### Blocklist

Create a text file with blocked domains (one per line):

**blocklist.txt**:
```
# Blocked domains (comments start with #)
malicious-site.com
tracking-domain.net
ad-server.example
```

Load in code:
```go
config := DefaultExitNodeConfig()
config.BlocklistPath = "blocklist.txt"
exitNode, _ := NewExitNode(config)
```

Blocklist features:
- Case-insensitive matching
- Newline-delimited format
- Comment support (`#` prefix)
- File-based loading

### DNS-over-HTTPS (DoH)

**Status**: Stub implementation (falls back to standard DNS)

Future enhancement:
```go
config.DoHEnabled = true
config.DoHServers = []string{
    "https://dns.google/dns-query",
    "https://cloudflare-dns.com/dns-query",
}
```

## IPC Protocol

### JSON-RPC 2.0 Format

**Request** (newline-delimited):
```json
{"jsonrpc":"2.0","method":"proxy.connect","params":{"target":"example.com:443"},"id":1}
```

**Response**:
```json
{"jsonrpc":"2.0","result":{"stream_id":12345},"id":1}
```

**Error**:
```json
{"jsonrpc":"2.0","error":{"code":-32001,"message":"Connection failed"},"id":1}
```

### Error Codes

| Code | Meaning |
|------|---------|
| -32700 | Parse error (invalid JSON) |
| -32600 | Invalid request |
| -32601 | Method not found |
| -32602 | Invalid params |
| -32603 | Internal error |
| -32001 | Connection failed |
| -32002 | Stream not found |
| -32003 | Stream closed |

### IPC Endpoints

**Unix Socket** (Linux/macOS):
- `/tmp/nyx-daemon.sock`

**Named Pipe** (Windows):
- `\\.\pipe\nyx-daemon`

## Troubleshooting

### Connection Refused (SOCKS5/HTTP CONNECT)

**Symptom**: `curl: (7) Failed to connect to 127.0.0.1 port 9050`

**Solutions**:
1. Verify proxy is running: `ps aux | grep nyx-http-proxy` (Linux) or `Get-Process nyx-http-proxy` (Windows)
2. Check port binding:
   - SOCKS5: `netstat -an | grep 9050` (Linux) or `netstat -an | findstr 9050` (Windows)
   - HTTP CONNECT: `netstat -an | grep 8080` or `netstat -an | findstr 8080`
3. Check logs in console output

### IPC Connection Failed

**Symptom**: `Failed to connect to IPC socket: No such file or directory`

**Solutions**:
1. Verify nyx-daemon is running
2. Check IPC socket exists:
   - Linux/macOS: `ls -l /tmp/nyx-daemon.sock`
   - Windows: Named pipes don't show in filesystem
3. Check permissions (Unix socket): `chmod 666 /tmp/nyx-daemon.sock`

### Rate Limit Exceeded

**Symptom**: HTTP 429 or SOCKS5 connection denied

**Solution**:
- Increase `RateLimit` or `RateBurst` in ExitNodeConfig
- Or set `RateLimit = 0` for unlimited (not recommended in production)

### Target Blocked

**Symptom**: Connection denied immediately

**Solutions**:
1. Check blocklist file for the target domain
2. Remove domain from blocklist: `grep -v "example.com" blocklist.txt > blocklist.txt.new && mv blocklist.txt.new blocklist.txt`
3. Or disable blocklist: `config.BlocklistPath = ""`

### DNS Resolution Failed

**Symptom**: `DNS resolution failed: no such host`

**Solutions**:
1. Verify DNS connectivity: `nslookup example.com` or `dig example.com`
2. Try alternative DNS: Configure system DNS to 8.8.8.8 (Google) or 1.1.1.1 (Cloudflare)
3. Enable DoH (future): `config.DoHEnabled = true`

### TLS Certificate Errors

**Symptom**: `x509: certificate verify failed`

**Solutions**:
1. System time incorrect: Check and sync system clock
2. Missing CA certificates:
   - Linux: `sudo update-ca-certificates`
   - macOS: System should auto-update
   - Windows: Usually automatic
3. Self-signed certificate: Not supported (security risk)

## Performance Tuning

### Latency Optimization

**Current bottlenecks**:
1. IPC overhead: ~1-5ms per request
2. DNS resolution: ~10-50ms (first request per domain)
3. TLS handshake: ~20-100ms (first request per domain)

**Optimizations**:
- HTTP client reuses connections (`MaxConnsPerHost: 10`)
- DNS caching (via `net.Resolver`)
- TLS session resumption (via `crypto/tls`)

### Throughput Optimization

**Default limits**:
- Rate limit: 100 req/sec (configurable)
- Max connections per host: 10 (configurable)
- HTTP client timeout: 30s (configurable)

**For high-throughput scenarios**:
```go
config := ExitNodeConfig{
    Timeout:         60 * time.Second,     // Longer timeout
    MaxConnsPerHost: 50,                    // More connections
    RateLimit:       rate.Limit(1000),     // Higher rate
    RateBurst:       100,                   // Larger burst
}
```

### Memory Usage

**Typical usage**:
- Base: ~50 MB (Go runtime)
- Per connection: ~100 KB (buffers + state)
- With 100 concurrent connections: ~60 MB

**Memory leak detection**:
```bash
# Enable pprof in main.go (development only)
import _ "net/http/pprof"
go tool pprof http://localhost:6060/debug/pprof/heap
```

## Security Considerations

### No C/C++ Dependencies

**Constraint**: ZERO C/C++ dependencies for security and portability.

**Implementation**:
- TLS: Pure Go `crypto/tls` (no OpenSSL)
- HTTP: Pure Go `net/http`
- Rate limiting: Pure Go `golang.org/x/time/rate`

**Verification**:
```bash
go list -m all | grep -i "cgo"  # Should be empty
ldd nyx-http-proxy              # Should show no C libraries (Linux)
```

### Credential Handling

**Username/Password (HTTP CONNECT)**:
- Timing-safe comparison via `crypto/subtle`
- No plaintext logging
- Basic Auth only (HTTPS required for security)

**Best practices**:
- Use over localhost only
- Or use HTTPS for remote access
- Rotate credentials regularly

### Blocklist Security

**Considerations**:
- Blocklist is not a firewall (DNS/IP can be bypassed)
- Case-insensitive matching prevents evasion
- File-based loading allows updates without restart

**Recommendations**:
- Combine with network-level filtering
- Use reputable blocklist sources
- Audit blocklist regularly

### DoS Protection

**Current mitigations**:
1. Rate limiting (token bucket)
2. Connection limits per host
3. Request timeout (30s default)
4. Header size limit (8KB for HTTP CONNECT)

**Future enhancements**:
- Per-IP rate limiting
- Connection pooling limits
- Circuit breaker for failing targets

## Testing

### Unit Tests

Run all tests:
```bash
cd nyx-http-proxy
go test -v ./...
```

Run specific test:
```bash
go test -v -run TestExitNodeRateLimiting
```

Check coverage:
```bash
go test -cover ./...
```

**Current coverage**: 54.1% (48/48 tests passing)

### Integration Tests

**SOCKS5 Integration**:
```bash
# Start proxy
./nyx-http-proxy &

# Test with curl
curl --socks5 127.0.0.1:9050 https://example.com

# Verify response
curl --socks5 127.0.0.1:9050 https://httpbin.org/ip
```

**HTTP CONNECT Integration**:
```bash
# Test with curl
curl --proxy http://127.0.0.1:8080 https://example.com

# Test with authentication
curl --proxy-user testuser:testpass --proxy http://127.0.0.1:8080 https://example.com
```

**IPC Integration** (requires nyx-daemon):
```bash
# Start nyx-daemon (in separate terminal)
cd nyx-daemon
cargo run

# Start nyx-http-proxy
cd nyx-http-proxy
./nyx-http-proxy

# Test connection
curl --socks5 127.0.0.1:9050 https://example.com
```

### Benchmarks

**Latency test**:
```bash
# Measure request latency
time curl --socks5 127.0.0.1:9050 https://example.com > /dev/null
```

**Throughput test**:
```bash
# Download 100MB file
time curl --socks5 127.0.0.1:9050 https://speed.cloudflare.com/__down?bytes=104857600 > /dev/null
```

**Load test** (requires `ab` or `wrk`):
```bash
# 1000 requests, 10 concurrent
ab -n 1000 -c 10 -X 127.0.0.1:8080 https://example.com/
```

## Development

### Project Structure

```
nyx-http-proxy/
├── main.go              # ProxyServer orchestration
├── socks5.go            # SOCKS5 protocol (RFC 1928)
├── socks5_test.go       # SOCKS5 unit tests (9 tests)
├── connect.go           # HTTP CONNECT proxy
├── connect_test.go      # HTTP CONNECT tests (17 tests)
├── exitnode.go          # Exit node implementation
├── exitnode_test.go     # Exit node tests (14 tests)
├── mixbridge.go         # IPC bridge to nyx-daemon
├── mixbridge_test.go    # IPC tests (8 tests)
├── go.mod               # Dependencies
├── go.sum               # Dependency checksums
├── Dockerfile           # Container image
└── README.md            # Project overview
```

### Adding Features

**Example: Add custom DNS resolver**

1. **Modify ExitNodeConfig**:
```go
type ExitNodeConfig struct {
    // ... existing fields ...
    CustomDNS string // e.g., "8.8.8.8:53"
}
```

2. **Update NewExitNode**:
```go
func NewExitNode(config ExitNodeConfig) (*ExitNode, error) {
    resolver := &net.Resolver{}
    if config.CustomDNS != "" {
        resolver = &net.Resolver{
            PreferGo: true,
            Dial: func(ctx context.Context, network, address string) (net.Conn, error) {
                d := net.Dialer{Timeout: 5 * time.Second}
                return d.DialContext(ctx, "udp", config.CustomDNS)
            },
        }
    }
    // ... rest of the function ...
}
```

3. **Add tests**:
```go
func TestCustomDNSResolver(t *testing.T) {
    config := DefaultExitNodeConfig()
    config.CustomDNS = "8.8.8.8:53"
    
    exitNode, err := NewExitNode(config)
    if err != nil {
        t.Fatalf("Failed to create exit node: %v", err)
    }
    
    // Test DNS resolution
    // ...
}
```

4. **Run tests**:
```bash
go test -v -run TestCustomDNSResolver
```

### Code Style

**Follow Go conventions**:
- `gofmt` for formatting
- `go vet` for static analysis
- Exported functions/types: Capitalized
- Unexported: lowercase
- Comments: English, complete sentences

**Example**:
```go
// HandleTCPConnection establishes a TCP connection to the target
// via the exit node. It performs rate limiting, blocklist validation,
// DNS resolution, and bidirectional data copying.
//
// Context cancellation will terminate the connection gracefully.
func (en *ExitNode) HandleTCPConnection(ctx context.Context, streamID uint32, target string) error {
    // Implementation...
}
```

## Roadmap

### Phase 2b (Next)

**SOCKS5/HTTP CONNECT Integration**:
- Update `socks5.go`: Use `MixBridgeClient.ProxyConnect` instead of `net.Dial`
- Update `connect.go`: Use `MixBridgeClient.ProxyConnect` instead of `net.Dial`
- End-to-end testing with nyx-daemon

**Real Mix Routing**:
- Implement `route_through_mix()` in `http_proxy.rs`
- Integrate with nyx-mix layer (cMix, VDF, RSA accumulator)
- Remove fallback to direct connection

### Phase 3 (Future)

**Advanced Features**:
- Per-IP rate limiting
- Dynamic blocklist updates (HTTP API)
- Full DNS-over-HTTPS (RFC 8484)
- IPv6 support (Teredo tunneling)
- SOCKS5 BIND/UDP ASSOCIATE commands
- HTTP/2 and HTTP/3 support

**Observability**:
- Prometheus metrics export
- OpenTelemetry tracing integration
- Grafana dashboards

**Security**:
- mTLS for IPC (mutual authentication)
- SOCKS5 GSSAPI authentication
- Certificate pinning for DoH
- Circuit breaker for failing targets

## References

### RFCs
- [RFC 1928](https://datatracker.ietf.org/doc/html/rfc1928): SOCKS Protocol Version 5
- [RFC 7231](https://datatracker.ietf.org/doc/html/rfc7231): HTTP/1.1 Semantics (CONNECT method)
- [RFC 8484](https://datatracker.ietf.org/doc/html/rfc8484): DNS Queries over HTTPS (DoH)
- [RFC 7617](https://datatracker.ietf.org/doc/html/rfc7617): HTTP Basic Authentication

### Specifications
- [JSON-RPC 2.0](https://www.jsonrpc.org/specification): IPC protocol
- [Nyx Protocol Spec](../spec/Nyx_Protocol_v1.0_Spec_EN.md): Mix Network integration

### Go Packages
- [net/http](https://pkg.go.dev/net/http): HTTP client
- [crypto/tls](https://pkg.go.dev/crypto/tls): TLS implementation
- [golang.org/x/time/rate](https://pkg.go.dev/golang.org/x/time/rate): Rate limiting

## License

See [LICENSE-APACHE](../LICENSE-APACHE) and [LICENSE-MIT](../LICENSE-MIT) for details.

## Support

- **Issues**: https://github.com/SeleniaProject/NyxNet/issues
- **Discussions**: https://github.com/SeleniaProject/NyxNet/discussions
- **Security**: See [SECURITY.md](../SECURITY.md) for responsible disclosure
