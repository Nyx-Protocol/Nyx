# Nyx HTTP Proxy

Pure Go HTTP/HTTPS proxy with SOCKS5 and HTTP CONNECT support for routing traffic through the Nyx Mix Network.

**⚠️ IMPORTANT**: This proxy **ALWAYS** routes traffic through the Nyx Mix Network (3-hop anonymity). All HTTP/HTTPS traffic is encrypted using Sphinx onion routing for maximum privacy, just like Tor.

## Features

- **SOCKS5 Proxy** (RFC 1928): Compatible with browsers, curl, and other SOCKS5 clients
- **HTTP CONNECT Proxy**: Standard HTTP/1.1 CONNECT method for HTTPS tunneling  
- **Pure Go TLS**: 100% Pure Go implementation using `crypto/tls` (ZERO C/C++ dependencies)
- **Nyx Mix Network Routing**: ALL traffic goes through 3-hop Mix Network with post-quantum encryption
- **Automatic Reconnection**: Automatic retry with exponential backoff for Mix Layer connection
- **Statistics & Monitoring**: Real-time connection stats and health checks
- **Cross-Platform**: Linux, macOS, Windows support

## Architecture

**Complete Tor-like Privacy Architecture:**

```
Browser/App
    ↓ HTTP/HTTPS Request
SOCKS5 (localhost:9050) or HTTP CONNECT (localhost:8080)
    ↓ Plaintext (localhost only)
Go Proxy (nyx-http-proxy) - Handles TLS/HTTP in Pure Go
    ↓ JSON-RPC over IPC (/tmp/nyx-mix.sock)
Rust Mix Layer (nyx-daemon)
    ↓ Sphinx Onion Encryption (3 layers)
Mix Node 1 → Mix Node 2 → Mix Node 3 (Entry/Middle/Exit)
    ↓ Decrypted at Exit Node
Target Server (example.com, etc.)
    ↓ HTTP Response
← Same path in reverse (3-hop Mix Network) ←
Browser/App receives response
```

**Key Points:**
- ✅ ALL traffic goes through 3-hop Nyx Mix Network
- ✅ Post-quantum encryption (ML-KEM-768 + X25519)
- ✅ Tor-compatible SOCKS5 proxy on port 9050
- ✅ No direct connections - everything through Mix Network
- ✅ TLS/HTTP handled by Go (no C/C++ dependencies)

## Prerequisites

**CRITICAL**: `nyx-daemon` MUST be running for the proxy to work!

1. Start Nyx daemon with Mix Layer enabled:
```bash
# Terminal 1: Start Nyx daemon
cd ../nyx-daemon
cargo run --release

# Wait for "Mix Layer IPC listening on /tmp/nyx-mix.sock"
```

2. Verify daemon is running:
```bash
# Check if IPC socket exists
ls -l /tmp/nyx-mix.sock  # Unix/Linux/macOS
# or
dir \\.\pipe\nyx-mix     # Windows
```

## Usage

### Basic

```bash
# Terminal 2: Start the HTTP proxy
./nyx-http-proxy

# You should see:
# "Successfully connected to Mix Layer at /tmp/nyx-mix.sock"
# "SOCKS5 server listening on :9050"
# "HTTP CONNECT server listening on :8080"

# Custom ports
./nyx-http-proxy -socks5 :9050 -http :8080 -health :8081

# Custom IPC path
./nyx-http-proxy -ipc /var/run/nyx-mix.sock
```

### Browser Configuration

#### Firefox
1. Open Settings → Network Settings
2. Select "Manual proxy configuration"
3. SOCKS Host: `localhost`, Port: `9050`
4. Select "SOCKS v5"
5. Check "Proxy DNS when using SOCKS v5"

#### Chrome/Chromium
```bash
# Linux/macOS
chromium --proxy-server="socks5://localhost:9050"

# Windows
chrome.exe --proxy-server="socks5://localhost:9050"
```

### Command-Line Tools

**All traffic goes through Nyx Mix Network (3-hop anonymity):**

```bash
# curl with SOCKS5 (Tor-compatible)
curl --socks5 localhost:9050 https://example.com
# → Goes through: curl → nyx-http-proxy → Mix Node 1 → Mix Node 2 → Mix Node 3 → example.com

# curl with HTTP proxy
curl --proxy http://localhost:8080 https://example.com

# wget with proxy
wget -e use_proxy=yes -e http_proxy=localhost:8080 https://example.com

# Check your anonymized IP
curl --socks5 localhost:9050 https://api.ipify.org?format=json
# {"ip":"<exit-node-ip>"}  <- Not your real IP!
```

### Testing Mix Network Routing

```bash
# Terminal 3: Monitor Mix Layer logs
tail -f /var/log/nyx-daemon.log

# You should see:
# - "ProxyConnect: target=example.com:443"
# - "Creating 3-hop circuit: Entry → Middle → Exit"
# - "ProxySend: stream_id=abc123, bytes=1234"
# - "ProxyReceive: stream_id=abc123, bytes=5678"
```

## Configuration

Environment variables:

- `NYX_SOCKS5_ADDR`: SOCKS5 listen address (default: `:9050`)
- `NYX_HTTP_ADDR`: HTTP proxy listen address (default: `:8080`)
- `NYX_HEALTH_ADDR`: Health check listen address (default: `:8081`)
- `NYX_IPC_PATH`: Mix Layer IPC socket path (default: `/tmp/nyx-mix.sock`)

## Health Check

```bash
curl http://localhost:8081/health
```

Response:
```json
{
  "status": "healthy",
  "total_connections": 1234,
  "socks5_connections": 800,
  "http_connections": 434,
  "active_connections": 5,
  "bytes_transferred": 123456789,
  "errors": 0
}
```

## Building

```bash
# Build for current platform
go build -o nyx-http-proxy

# Build for Linux
GOOS=linux GOARCH=amd64 go build -o nyx-http-proxy-linux

# Build for Windows
GOOS=windows GOARCH=amd64 go build -o nyx-http-proxy.exe

# Build for macOS
GOOS=darwin GOARCH=amd64 go build -o nyx-http-proxy-macos
```

## Testing

```bash
# Run unit tests
go test ./...

# Run with race detector
go test -race ./...

# Integration test (requires running nyx-daemon)
go test -tags=integration ./...
```

## Development Status

- [x] Project structure and build system
- [ ] SOCKS5 protocol implementation
- [ ] HTTP CONNECT proxy implementation
- [ ] IPC bridge to Rust Mix Layer
- [ ] Exit node HTTP/HTTPS client
- [ ] Statistics and monitoring
- [ ] Integration tests
- [ ] Performance benchmarks

## Dependencies

All dependencies are Pure Go (C/C++ free):

- Standard library only (no external dependencies for core functionality)
- `golang.org/x/time/rate` for rate limiting (Pure Go)

## License

Dual-licensed under MIT or Apache-2.0, same as the Nyx project.

## Security

- TLS 1.2+ only (configurable minimum version)
- No credential storage (pass-through to Mix Layer)
- Rate limiting to prevent abuse
- Connection timeout enforcement
- Detailed audit logging

## Performance

- Concurrent connection handling with goroutines
- Zero-copy data transfer where possible
- Connection pooling for HTTP clients
- Efficient buffer management

## Troubleshooting

### Cannot connect to Mix Layer IPC socket

```
Error: dial unix /tmp/nyx-mix.sock: connect: no such file or directory
Warning: Initial Mix Layer connection failed: ... (will retry on first request)
```

**Solution**: 
1. Ensure `nyx-daemon` is running: `ps aux | grep nyx-daemon`
2. Check IPC socket exists: `ls -l /tmp/nyx-mix.sock`
3. Start daemon: `cd ../nyx-daemon && cargo run --release`
4. The proxy will automatically retry connection on first request

### Connection hangs or times out

```
Error: failed to reconnect to Mix Layer: connection timeout
```

**Solution**:
1. Check daemon logs for errors
2. Verify Mix Network has at least 3 nodes available
3. Check if Mix Layer JSON-RPC is enabled in `nyx.toml`

### Traffic not going through Mix Network

**Verify routing:**
```bash
# Check proxy logs - you should see:
# "Mix Layer RPC -> proxy.connect (ID: 1)"
# "Mix Layer RPC <- proxy.connect (ID: 1, Error: false)"
# "SOCKS5 Mix connection established to example.com:443 (StreamID: abc123)"

# If you see "direct connection" or no Mix logs, daemon is not running properly
```

### SOCKS5 authentication failed

```
Error: SOCKS5 authentication method not supported
```

**Solution**: Current implementation supports no-auth only. Username/password auth will be added in a future release.

### Port already in use

```
Error: bind: address already in use
```

**Solution**: Use custom ports with `-socks5` and `-http` flags.

### Performance issues

**Check Mix Network health:**
```bash
# Mix Network adds latency due to 3-hop routing (by design for anonymity)
# Typical latency: 100-500ms (vs 10-50ms direct)
# If slower, check:
# 1. Mix Node health (CPU, network)
# 2. Number of concurrent streams
# 3. FEC (Forward Error Correction) overhead
```

## Related Projects

- [nyx-daemon](../nyx-daemon/): Rust Mix Layer daemon
- [nyx-push-proxy](../nyx-push-proxy/): Push notification proxy (370 lines, reference implementation)

## Contributing

See [CONTRIBUTING.md](../CONTRIBUTING.md) for development guidelines.
