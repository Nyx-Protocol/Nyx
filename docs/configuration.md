# Nyx Network Configuration Reference

**Version**: 1.0  
**Last Updated**: 2025-10-04  
**Schema**: `nyx.toml`

This document provides comprehensive documentation for all Nyx Network configuration options. Configuration is managed via TOML files (default `nyx.toml`) and environment variables.

---

## Table of Contents

1. [Root Configuration](#root-configuration)
2. [Security Settings](#security-settings)
3. [Network Configuration](#network-configuration)
4. [Cryptography](#cryptography)
5. [DHT (Distributed Hash Table)](#dht-distributed-hash-table)
6. [Service Endpoints](#service-endpoints)
7. [CLI Configuration](#cli-configuration)
8. [Performance Tuning](#performance-tuning)
9. [Plugin System](#plugin-system)
10. [Monitoring and Telemetry](#monitoring-and-telemetry)
11. [Safety Limits](#safety-limits)
12. [Development Settings](#development-settings)
13. [Multipath Routing](#multipath-routing)
14. [Mix Network (cMix)](#mix-network-cmix)
15. [Telemetry and Observability](#telemetry-and-observability)
16. [Low-Power Mode](#low-power-mode)
17. [Environment Variables](#environment-variables)
18. [Best Practices](#best-practices)

---

## Root Configuration

Core settings that apply globally to the Nyx daemon.

### `listen_port`
- **Type**: `u16`
- **Default**: `43300`
- **Range**: `1024-65535`
- **Description**: Primary port for QUIC transport listening
- **Example**: `listen_port = 43300`

### `node_id`
- **Type**: `string`
- **Default**: `"auto"`
- **Description**: Unique node identifier. Set to `"auto"` to generate Ed25519-based ID at startup
- **Example**: `node_id = "auto"`
- **Manual ID**: `node_id = "12D3KooW..."`

### `log_level`
- **Type**: `string`
- **Default**: `"info"`
- **Options**: `"error"`, `"warn"`, `"info"`, `"debug"`, `"trace"`
- **Description**: Global logging verbosity. Can be overridden by `RUST_LOG` environment variable
- **Example**: `log_level = "info"`

### `log_format`
- **Type**: `string`
- **Default**: `"json"`
- **Options**: `"json"`, `"pretty"`, `"compact"`
- **Description**: Log output format. Use `"json"` for production (structured logging)
- **Example**: `log_format = "json"`

### `bootstrap_peers`
- **Type**: `array<string>`
- **Default**: `[]`
- **Description**: Initial peer multiaddrs for network bootstrapping
- **Example**:
  ```toml
  bootstrap_peers = [
      "/dns4/validator1.nymtech.net/tcp/1789/p2p/12D3KooWNyxMainnet1",
      "/ip4/192.168.1.100/tcp/43300/p2p/12D3KooWPeer1"
  ]
  ```
- **Format**: libp2p multiaddr format

---

## Security Settings

**Section**: `[security]`

Core security parameters and rate limiting.

### `max_connections`
- **Type**: `u32`
- **Default**: `1000`
- **Range**: `10-10000`
- **Description**: Maximum concurrent peer connections
- **Recommendation**: Scale based on available memory (each connection ~1MB)

### `connection_timeout`
- **Type**: `u32` (seconds)
- **Default**: `30`
- **Range**: `5-300`
- **Description**: TCP/QUIC handshake timeout

### `max_frame_size`
- **Type**: `usize` (bytes)
- **Default**: `8388608` (8MB)
- **Range**: `1024-67108864` (1KB-64MB)
- **Description**: Maximum frame size for stream protocol
- **Security**: Lower values reduce DoS attack surface

### `rate_limit_requests`
- **Type**: `u32` (requests/second)
- **Default**: `100`
- **Range**: `1-10000`
- **Description**: Per-peer request rate limit

### `rate_limit_bytes`
- **Type**: `u64` (bytes/second)
- **Default**: `10485760` (10MB/s)
- **Range**: `1024-1073741824` (1KB/s-1GB/s)
- **Description**: Per-peer bandwidth rate limit

---

## Network Configuration

**Section**: `[network]`

Network binding and connectivity options.

### `bind_addr`
- **Type**: `string` (socket address)
- **Default**: `"127.0.0.1:43300"`
- **Description**: Socket address for QUIC transport binding
- **Examples**:
  - Development: `"127.0.0.1:43300"`
  - Production: `"0.0.0.0:43300"` (all interfaces)
  - IPv6: `"[::]:43300"`

### `ipv6_enabled`
- **Type**: `bool`
- **Default**: `true`
- **Description**: Enable IPv6 dual-stack support

### `development`
- **Type**: `bool`
- **Default**: `false`
- **Description**: Enable development mode (relaxed security, verbose logging)
- **Warning**: Never use in production

### `max_peers`
- **Type**: `u32`
- **Default**: `100`
- **Range**: `10-10000`
- **Description**: Maximum peer table size

### `peer_timeout`
- **Type**: `u32` (seconds)
- **Default**: `30`
- **Range**: `10-300`
- **Description**: Idle peer connection timeout

---

## Cryptography

**Section**: `[crypto]`

Post-quantum cryptography and key management.

### `pq_enabled`
- **Type**: `bool`
- **Default**: `true`
- **Description**: Enable post-quantum hybrid handshake (X25519 + Kyber1024)
- **Recommendation**: Always enable for future-proofing

### `key_rotation_interval`
- **Type**: `u32` (seconds)
- **Default**: `3600` (1 hour)
- **Range**: `300-86400` (5 min - 24 hours)
- **Description**: Automatic session key rotation interval for forward secrecy

### `session_timeout`
- **Type**: `u32` (seconds)
- **Default**: `7200` (2 hours)
- **Range**: `600-86400` (10 min - 24 hours)
- **Description**: Maximum session lifetime before re-handshake required

---

## DHT (Distributed Hash Table)

**Section**: `[dht]`

Kademlia DHT for peer discovery and config gossip.

### `enabled`
- **Type**: `bool`
- **Default**: `true`
- **Description**: Enable DHT peer discovery

### `port`
- **Type**: `u16`
- **Default**: `43301`
- **Range**: `1024-65535`
- **Description**: DHT bind port (separate from main `listen_port`)

### `peer_cache_size`
- **Type**: `usize`
- **Default**: `1000`
- **Range**: `100-100000`
- **Description**: Maximum entries in peer routing table

### `discovery_timeout`
- **Type**: `u32` (seconds)
- **Default**: `30`
- **Range**: `5-300`
- **Description**: DHT lookup timeout

### `refresh_interval`
- **Type**: `u32` (seconds)
- **Default**: `300` (5 minutes)
- **Range**: `60-3600`
- **Description**: Periodic routing table refresh interval

---

## Service Endpoints

**Section**: `[endpoints]`

External API and metrics endpoints.

### `grpc_addr`
- **Type**: `string` (socket address)
- **Default**: `"127.0.0.1:50051"`
- **Description**: gRPC control API address (NyxControl service)
- **Production**: Bind to localhost or use mTLS authentication

### `prometheus_addr`
- **Type**: `string` (socket address)
- **Default**: `"127.0.0.1:9090"`
- **Description**: Prometheus metrics HTTP endpoint (`/metrics`)
- **Production**: Restrict to monitoring network

### `tls_enabled`
- **Type**: `bool`
- **Default**: `false`
- **Description**: Enable TLS for gRPC endpoint

### `tls_cert`
- **Type**: `string` (file path)
- **Optional**: Required if `tls_enabled = true`
- **Description**: Path to TLS certificate (PEM format)
- **Example**: `tls_cert = "/etc/nyx/tls/cert.pem"`

### `tls_key`
- **Type**: `string` (file path)
- **Optional**: Required if `tls_enabled = true`
- **Description**: Path to TLS private key (PEM format)
- **Example**: `tls_key = "/etc/nyx/tls/key.pem"`

---

## CLI Configuration

**Section**: `[cli]`

Settings for `nyx-cli` command-line tool.

### `max_reconnect_attempts`
- **Type**: `u32`
- **Default**: `5`
- **Range**: `1-100`
- **Description**: Maximum reconnection attempts for gRPC streams

### `command_timeout`
- **Type**: `u32` (seconds)
- **Default**: `30`
- **Range**: `5-300`
- **Description**: RPC command timeout

### `output_format`
- **Type**: `string`
- **Default**: `"table"`
- **Options**: `"json"`, `"yaml"`, `"table"`
- **Description**: Default output format for CLI commands

### `colored_output`
- **Type**: `bool`
- **Default**: `true`
- **Description**: Enable ANSI color codes in terminal output

---

## Performance Tuning

**Section**: `[performance]`

Runtime performance and resource allocation.

### `worker_threads`
- **Type**: `u32`
- **Default**: `0` (auto-detect)
- **Range**: `0-256`
- **Description**: Tokio worker thread count. `0` = number of CPU cores

### `read_buffer_size`
- **Type**: `usize` (bytes)
- **Default**: `65536` (64KB)
- **Range**: `4096-1048576` (4KB-1MB)
- **Description**: Socket read buffer size

### `write_buffer_size`
- **Type**: `usize` (bytes)
- **Default**: `65536` (64KB)
- **Range**: `4096-1048576` (4KB-1MB)
- **Description**: Socket write buffer size

### `max_memory_usage`
- **Type**: `u64` (bytes)
- **Default**: `1073741824` (1GB)
- **Range**: `104857600-17179869184` (100MB-16GB)
- **Description**: Soft memory limit for heap allocation monitoring

---

## Plugin System

**Section**: `[plugins]`

Dynamic plugin loading and sandboxing.

### `enabled`
- **Type**: `bool`
- **Default**: `false`
- **Description**: Enable plugin system
- **Warning**: Experimental feature

### `plugin_dir`
- **Type**: `string` (directory path)
- **Default**: `"./plugins"`
- **Description**: Plugin WASM binary directory

### `sandbox_level`
- **Type**: `string`
- **Default**: `"strict"`
- **Options**: `"none"`, `"basic"`, `"strict"`
- **Description**: Plugin isolation level
  - `none`: Full host access (unsafe)
  - `basic`: Limited syscalls
  - `strict`: Full WASM sandbox

### `max_plugin_memory`
- **Type**: `u64` (bytes)
- **Default**: `104857600` (100MB)
- **Range**: `1048576-1073741824` (1MB-1GB)
- **Description**: Per-plugin memory limit

---

## Monitoring and Telemetry

**Section**: `[monitoring]`

Legacy monitoring settings (see also `[telemetry]` for OTLP).

### `metrics_enabled`
- **Type**: `bool`
- **Default**: `true`
- **Description**: Enable internal metrics collection

### `metrics_interval`
- **Type**: `u32` (seconds)
- **Default**: `60`
- **Range**: `1-3600`
- **Description**: Metrics aggregation interval

### `tracing_enabled`
- **Type**: `bool`
- **Default**: `false`
- **Description**: Enable distributed tracing

### `tracing_endpoint`
- **Type**: `string` (URL)
- **Optional**: Required if `tracing_enabled = true`
- **Description**: Jaeger/Zipkin HTTP endpoint
- **Example**: `tracing_endpoint = "http://localhost:14268"`

---

## Safety Limits

**Section**: `[limits]`

Hard limits to prevent resource exhaustion.

### `max_frame_len_bytes`
- **Type**: `usize` (bytes)
- **Default**: `8388608` (8MB)
- **Range**: `1024-67108864` (1KB-64MB)
- **Description**: Maximum codec frame length (see also `[security].max_frame_size`)

### `max_concurrent_connections`
- **Type**: `u32`
- **Default**: `1000`
- **Range**: `10-100000`
- **Description**: Hard limit on concurrent connections

### `max_request_size`
- **Type**: `usize` (bytes)
- **Default**: `16777216` (16MB)
- **Range**: `1024-134217728` (1KB-128MB)
- **Description**: Maximum gRPC request body size

### `idle_timeout`
- **Type**: `u32` (seconds)
- **Default**: `300` (5 minutes)
- **Range**: `10-3600`
- **Description**: Connection idle timeout before cleanup

---

## Development Settings

**Section**: `[development]`

**Warning**: Never enable in production environments.

### `dev_mode`
- **Type**: `bool`
- **Default**: `false`
- **Description**: Master development mode switch

### `debug_endpoints`
- **Type**: `bool`
- **Default**: `false`
- **Description**: Expose `/debug/pprof` HTTP endpoints

### `disable_auth`
- **Type**: `bool`
- **Default**: `false`
- **Description**: Disable gRPC authentication (UNSAFE)

### `verbose_logging`
- **Type**: `bool`
- **Default**: `false`
- **Description**: Force `log_level = "trace"` for all modules

---

## Multipath Routing

**Section**: `[multipath]`

Multipath QUIC for bandwidth aggregation and failover.

### `max_paths`
- **Type**: `u32`
- **Default**: `4`
- **Range**: `1-16`
- **Description**: Maximum concurrent paths per connection
- **Recommendation**: 2-4 for typical mobile/desktop, 8+ for servers

### `min_path_quality`
- **Type**: `f64`
- **Default**: `0.5`
- **Range**: `0.0-1.0`
- **Description**: Minimum quality threshold for path activation
- **Calculation**: Quality = (1 - packet_loss_rate) × (1 / normalized_rtt)

### `failover_timeout_ms`
- **Type**: `u64` (milliseconds)
- **Default**: `1000`
- **Range**: `100-10000`
- **Description**: Path failure detection timeout

### `quality_monitoring_enabled`
- **Type**: `bool`
- **Default**: `true`
- **Description**: Enable continuous path quality measurement

### `probe_interval`
- **Type**: `u32` (seconds)
- **Default**: `30`
- **Range**: `5-300`
- **Description**: PATH_CHALLENGE probe interval for connectivity testing

---

## Mix Network (cMix)

**Section**: `[mix]`

cMix anonymous communication and cover traffic.

### `cmix_enabled`
- **Type**: `bool`
- **Default**: `false`
- **Description**: Enable cMix batch mixing protocol

### `batch_size`
- **Type**: `u32`
- **Default**: `128`
- **Range**: `32-1024`
- **Description**: Messages per mix batch (larger = better anonymity, higher latency)

### `vdf_delay_ms`
- **Type**: `u64` (milliseconds)
- **Default**: `100`
- **Range**: `10-1000`
- **Description**: Verifiable Delay Function computation time per mix round

### `mix_layers`
- **Type**: `u32`
- **Default**: `3`
- **Range**: `1-10`
- **Description**: Number of mix cascade layers (3 = standard onion routing)

### `cover_traffic_enabled`
- **Type**: `bool`
- **Default**: `true`
- **Description**: Enable adaptive cover traffic generation

### `cover_traffic_ratio`
- **Type**: `f64`
- **Default**: `0.3`
- **Range**: `0.0-1.0`
- **Description**: Target ratio of cover traffic to real traffic
- **Example**: `0.3` = 30% cover packets

---

## Telemetry and Observability

**Section**: `[telemetry]`

OpenTelemetry Protocol (OTLP) integration for distributed tracing.

### `otlp_endpoint`
- **Type**: `string` (URL)
- **Optional**: Leave commented to disable OTLP export
- **Description**: OTLP gRPC collector endpoint
- **Example**: `otlp_endpoint = "http://localhost:4317"`

### `otlp_sampling_rate`
- **Type**: `f64`
- **Default**: `1.0`
- **Range**: `0.0-1.0`
- **Description**: Span sampling rate
  - `1.0` = 100% (all spans exported)
  - `0.1` = 10% (probabilistic sampling)

### `prometheus_enabled`
- **Type**: `bool`
- **Default**: `false`
- **Description**: Enable Prometheus metrics export via OTLP
- **Requires**: `otlp_endpoint` configured

### `prometheus_addr`
- **Type**: `string` (socket address)
- **Optional**: Leave commented if using OTLP-only
- **Description**: Alternative Prometheus HTTP scrape endpoint
- **Example**: `prometheus_addr = "127.0.0.1:9100"`

### `service_name`
- **Type**: `string`
- **Default**: `"nyx-daemon"`
- **Description**: Service identifier for traces/metrics

### `span_export_enabled`
- **Type**: `bool`
- **Default**: `false`
- **Description**: Enable span export (requires `otlp_endpoint`)

---

## Low-Power Mode

**Section**: `[low_power]`

Mobile device battery optimization (Android/iOS).

### `enabled`
- **Type**: `bool`
- **Default**: `true`
- **Description**: Enable low-power mode features

### `background_cover_traffic_ratio`
- **Type**: `f64`
- **Default**: `0.08`
- **Range**: `0.05-0.1`
- **Description**: Cover traffic ratio when screen is off or app backgrounded

### `active_cover_traffic_ratio`
- **Type**: `f64`
- **Default**: `0.4`
- **Range**: `0.3-0.5`
- **Description**: Cover traffic ratio when screen is on and app foregrounded

### `battery_critical_threshold`
- **Type**: `u8` (percentage)
- **Default**: `10`
- **Range**: `5-20`
- **Description**: Triggers aggressive power saving (minimal cover traffic)

### `battery_low_threshold`
- **Type**: `u8` (percentage)
- **Default**: `20`
- **Range**: `10-30`
- **Description**: Triggers moderate power saving

### `battery_hysteresis`
- **Type**: `u8` (percentage)
- **Default**: `5`
- **Range**: `1-10`
- **Description**: Prevents rapid state oscillation (e.g., 10% threshold with 5% hysteresis = transition at 10% down, 15% up)

### `screen_off_cooldown_ms`
- **Type**: `u64` (milliseconds)
- **Default**: `5000`
- **Range**: `1000-30000`
- **Description**: Debounce interval for screen state changes

### `app_background_timeout`
- **Type**: `u32` (seconds)
- **Default**: `10`
- **Range**: `5-60`
- **Description**: Delay before considering app truly backgrounded (prevents transient app switches)

---

## Environment Variables

Environment variables override `nyx.toml` settings (highest priority).

### Authentication
- **`NYX_DAEMON_TOKEN`**: Authentication token for gRPC API (overrides cookie file)
- **`NYX_DAEMON_COOKIE`**: Explicit path to cookie file (default: `~/.nyx/daemon.cookie`)
- **`NYX_DAEMON_STRICT_AUTH`**: Set to `1` to require token for all privileged operations

### Networking
- **`NYX_PROMETHEUS_ADDR`**: Override Prometheus bind address (e.g., `127.0.0.1:0` for random port)
- **`NYX_BIND_ADDR`**: Override `[network].bind_addr`

### Configuration
- **`NYX_CONFIG`**: Path to custom `nyx.toml` (default: `./nyx.toml`)
- **`RUST_LOG`**: Override `log_level` (e.g., `RUST_LOG=debug,tokio=info`)

### Development
- **`NYX_DEV_MODE`**: Set to `1` to force development mode
- **`NYX_DISABLE_AUTH`**: Set to `1` to disable authentication (UNSAFE)

---

## Best Practices

### Security
1. **Production Deployments**:
   - Set `[network].bind_addr = "0.0.0.0:43300"` for external access
   - Set `[network].development = false`
   - Enable TLS: `[endpoints].tls_enabled = true` with valid certificates
   - Restrict `grpc_addr` and `prometheus_addr` to localhost or monitoring networks

2. **Authentication**:
   - Always set `NYX_DAEMON_TOKEN` or secure `daemon.cookie` file (chmod 600)
   - Never use `disable_auth = true` in production

3. **Rate Limiting**:
   - Adjust `[security].rate_limit_requests` and `rate_limit_bytes` based on expected traffic
   - Lower `max_frame_size` to reduce DoS attack surface

### Performance
1. **Resource Allocation**:
   - Set `[performance].worker_threads` to available CPU cores for maximum throughput
   - Increase `max_connections` on high-capacity servers

2. **Multipath**:
   - Use `max_paths = 2` for typical mobile connections (WiFi + cellular)
   - Use `max_paths = 4+` for load balancing servers

3. **Monitoring**:
   - Enable `[telemetry].otlp_endpoint` for production observability
   - Set `otlp_sampling_rate = 0.1` (10%) in high-traffic environments to reduce overhead

### Low-Power Mode (Mobile)
1. Configure battery thresholds based on device characteristics:
   - **High-capacity devices**: `battery_critical_threshold = 15`, `battery_low_threshold = 30`
   - **Low-capacity devices**: `battery_critical_threshold = 10`, `battery_low_threshold = 20`

2. Adjust cover traffic ratios based on threat model:
   - **High anonymity**: `active_cover_traffic_ratio = 0.5`, `background_cover_traffic_ratio = 0.1`
   - **Balanced**: `active_cover_traffic_ratio = 0.4`, `background_cover_traffic_ratio = 0.08` (default)
   - **Battery-first**: `active_cover_traffic_ratio = 0.3`, `background_cover_traffic_ratio = 0.05`

### Development
1. **Local Testing**:
   - Use `[network].bind_addr = "127.0.0.1:43300"` to prevent external access
   - Set `[network].development = true` for verbose logging
   - Disable TLS: `[endpoints].tls_enabled = false`

2. **Debugging**:
   - Set `log_level = "debug"` or `RUST_LOG=debug` for detailed logs
   - Enable `[development].debug_endpoints = true` for pprof profiling

---

## Configuration Validation

Use `nyx-cli config validate` to check configuration syntax and semantics:

```bash
# Basic validation (syntax and types)
nyx-cli config validate /path/to/nyx.toml

# Strict validation (includes endpoint connectivity checks)
nyx-cli config validate --strict /path/to/nyx.toml
```

**Exit Codes**:
- `0`: Configuration valid
- `1`: Validation failed (errors printed to stderr)

---

## See Also

- **[Architecture](architecture.md)**: System design and component overview
- **[API Reference](api.md)**: gRPC API documentation
- **[Quickstart](quickstart-ubuntu-k8s.md)**: Deployment guide
- **[Specification](../spec/)**: Protocol specifications

---

**Document Version**: 1.0  
**Configuration Schema**: `nyx.toml` (208 lines)  
**Total Sections**: 16  
**Environment Variables**: 10
