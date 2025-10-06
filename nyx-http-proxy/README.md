# Nyx HTTP Proxy

Pure Go HTTP/HTTPS proxy with SOCKS5 and HTTP CONNECT support for routing traffic through the Nyx Mix Network.

## Features

- **SOCKS5 Proxy** (RFC 1928): Compatible with browsers, curl, and other SOCKS5 clients
- **HTTP CONNECT Proxy**: Standard HTTP/1.1 CONNECT method for HTTPS tunneling
- **Pure Go TLS**: 100% Pure Go implementation using `crypto/tls` (ZERO C/C++ dependencies)
- **Mix Network Integration**: Routes traffic through Nyx Mix Layer via IPC
- **Statistics & Monitoring**: Real-time connection stats and health checks
- **Cross-Platform**: Linux, macOS, Windows support

## Architecture

```
Browser/App → SOCKS5 (localhost:9050) or HTTP CONNECT (localhost:8080)
              ↓
           Go Proxy (nyx-http-proxy)
              ↓
           IPC (/tmp/nyx-mix.sock)
              ↓
           Rust Mix Layer (nyx-daemon)
              ↓
           Exit Node
              ↓
           Internet
```

## Usage

### Basic

```bash
# Start the proxy with default settings
./nyx-http-proxy

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

```bash
# curl with SOCKS5
curl --socks5 localhost:9050 https://example.com

# curl with HTTP proxy
curl --proxy http://localhost:8080 https://example.com

# wget with proxy
wget -e use_proxy=yes -e http_proxy=localhost:8080 https://example.com
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
```

**Solution**: Ensure `nyx-daemon` is running with Mix Layer enabled.

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

## Related Projects

- [nyx-daemon](../nyx-daemon/): Rust Mix Layer daemon
- [nyx-push-proxy](../nyx-push-proxy/): Push notification proxy (370 lines, reference implementation)

## Contributing

See [CONTRIBUTING.md](../CONTRIBUTING.md) for development guidelines.
