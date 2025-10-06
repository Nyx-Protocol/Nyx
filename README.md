<div align="center">

# NyxNet

Modular, privacy-first networking stack in Rust. Clean architecture, safe-by-default, and OSS-friendly.

[![CI](https://img.shields.io/github/actions/workflow/status/SeleniaProject/Nyx/ci.yml?branch=main&label=CI)](https://github.com/SeleniaProject/Nyx/actions)
[![Integration Tests](https://img.shields.io/github/actions/workflow/status/SeleniaProject/Nyx/integration-tests.yml?branch=main&label=Integration)](https://github.com/SeleniaProject/Nyx/actions)
[![Fuzzing](https://img.shields.io/github/actions/workflow/status/SeleniaProject/Nyx/fuzzing.yml?label=Fuzzing)](https://github.com/SeleniaProject/Nyx/actions)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE-MIT)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE-APACHE)
![Rust Edition](https://img.shields.io/badge/Rust-2021-orange)
![OS](https://img.shields.io/badge/OS-Linux%20%7C%20macOS%20%7C%20Windows-555)
![Tests](https://img.shields.io/badge/Tests-410%2B%20passing-success)

</div>

## Overview

NyxNet is a privacy-first, post-quantum secure networking stack implemented in pure Rust. It provides multipath QUIC transport, hybrid cryptography (X25519 + Kyber1024), gRPC control APIs, and comprehensive observability for building resilient peer-to-peer applications. Dual-licensed under MIT or Apache-2.0.

**Status**: ✅ **v1.0 Complete** - All core features implemented (Sphinx encryption, HTTP/SOCKS5 proxy, Mix Network integration). Integration testing in progress.

## Key Features

- **Post-Quantum Cryptography**: Hybrid handshake (X25519 + ML-KEM-768) with automatic key rotation
- **Multipath QUIC**: Automatic failover, bandwidth aggregation, sub-second failure detection
- **Sphinx Onion Routing**: 3-hop mix network with ChaCha20Poly1305 encryption ✨ **NEW**
- **Tor-Compatible Proxy**: SOCKS5 + HTTP CONNECT with JSON-RPC 2.0 bridge ✨ **NEW**
- **NAT Traversal**: ICE Lite implementation with STUN for P2P connectivity
- **gRPC Control API**: 20+ RPCs for node management, stream control, topology queries
- **OTLP Telemetry**: OpenTelemetry integration (Jaeger/Tempo) with configurable sampling
- **Kubernetes-Native**: Helm charts with HPA, PDB, ServiceMonitor support
- **Pure Rust + Go**: Zero C/C++ dependencies, memory-safe implementation
- **315+ Tests**: Comprehensive test coverage (unit, integration, fuzzing)

## Crate Structure

- **nyx-daemon**: Main daemon with gRPC control API, OTLP exporter, hot-reloadable config
- **nyx-cli**: CLI for daemon operations, configuration validation, diagnostics
- **nyx-core**: Core primitives (IDs, time, config, rate limiting, i18n)
- **nyx-crypto**: Hybrid handshake, HPKE encryption, session key management, replay protection
- **nyx-transport**: QUIC datagram transport with multipath routing
- **nyx-stream**: Stream management with extended packet format
- **nyx-mix**: Mix network framework with cover traffic generation
- **nyx-control**: gRPC service definitions and server implementation
- **nyx-telemetry**: OTLP span export, Prometheus metrics, telemetry schema
- **nyx-sdk**: Application SDK with async stream API, daemon client
- **nyx-sdk-wasm**: WASM SDK for browser/Node.js environments
- **nyx-mobile-ffi**: C-ABI for iOS/Android integration
- **nyx-fec**: Forward Error Correction with adaptive redundancy
- **nyx-conformance**: Deterministic network simulator for property testing
- **nyx-http-proxy**: Tor-compatible SOCKS5/HTTP CONNECT proxy (Go) ✨ **NEW**
- **nyx-push-proxy**: Mobile push notification relay (Go)

See `Cargo.toml` for the complete workspace structure.

## Quick Start

### Local Development

**1. Build**

```bash
cargo build --release
```

**2. Run Daemon**

```bash
./target/release/nyx-daemon --config nyx.toml
```

**3. Use CLI**

```bash
# Get node information
./target/release/nyx-cli node info

# Validate configuration
./target/release/nyx-cli config validate nyx.toml

# Open a stream to a peer
./target/release/nyx-cli stream open <peer-id>
```

### Configuration

**Primary config file**: `nyx.toml` (see `examples/full_config.toml` for comprehensive reference)

**Minimal example**:

```toml
# nyx.toml
listen_port = 43300
node_id = "auto"
log_level = "info"

[network]
bind_addr = "127.0.0.1:43300"

[crypto]
pq_enabled = true
key_rotation_interval = 3600

[endpoints]
grpc_addr = "127.0.0.1:50051"
prometheus_addr = "127.0.0.1:9090"
```

**Environment variables**:
- `RUST_LOG`: Override log level (e.g., `RUST_LOG=debug`)
- `NYX_CONFIG`: Custom config path (default: `./nyx.toml`)
- `NYX_DAEMON_TOKEN`: gRPC API authentication token

See `docs/configuration.md` for complete reference (80+ parameters).

## Control API

### gRPC API (Default: port 50051)

**20 RPC Methods** across NyxControl service:
- **Node Management**: `GetNodeInfo`, `GetHealth`, `Shutdown`
- **Stream Control**: `OpenStream`, `CloseStream`, `SendData`, `ListStreams`
- **Event Streaming**: `SubscribeEvents` (server-side streaming)
- **Statistics**: `GetStats`, `GetPeerInfo`
- **Configuration**: `GetConfig`, `UpdateConfig`, `ReloadConfig`
- **Multipath**: `GetActivePaths`, `GetPathQuality`
- **Topology**: `GetTopology`, `GetNetworkMap`

**Authentication**: Token-based via `NYX_DAEMON_TOKEN` environment variable or `~/.nyx/daemon.cookie` file.

**Example (using nyx-sdk)**:
```rust
use nyx_sdk::NyxGrpcClient;

let client = NyxGrpcClient::connect("http://127.0.0.1:50051").await?;
let info = client.get_node_info().await?;
println!("Node ID: {}", info.node_id);
```

See `docs/api.md` for complete API reference and `nyx-sdk/examples/grpc_client_example.rs` for usage patterns.

## Observability

### Prometheus Metrics

Expose metrics at `http://127.0.0.1:9090/metrics` (configurable via `prometheus_addr`):
- Connection metrics: `nyx_connections_total`, `nyx_connections_active`
- Bandwidth: `nyx_bytes_sent_total`, `nyx_bytes_received_total`
- Multipath: `nyx_paths_active`, `nyx_path_failovers_total`
- Cover traffic: `nyx_cover_traffic_ratio`

### OTLP Telemetry

Export traces to Jaeger/Tempo (configure `telemetry.otlp.endpoint` in nyx.toml):
```toml
[telemetry]
otlp_endpoint = "http://tempo.monitoring.svc.cluster.local:4317"
otlp_sampling_rate = 0.1  # 10% sampling for production
service_name = "nyx-daemon"
```

## Kubernetes Deployment

### Helm Chart Installation

```bash
# Add repository (if published)
helm repo add nyx https://charts.nyx.network
helm repo update

# Install with default values
helm install nyx nyx/nyx --namespace nyx-system --create-namespace

# Or install from local chart
helm install nyx charts/nyx --namespace nyx-system --create-namespace
```

### Configuration Options

```yaml
# values-production.yaml
replicaCount: 6

grpc:
  enabled: true
  port: 50051

telemetry:
  otlp:
    enabled: true
    endpoint: "http://tempo.monitoring.svc.cluster.local:4317"
    samplingRate: 0.1

config:
  data: |
    listen_port = 43300
    log_level = "info"
    
    [crypto]
    pq_enabled = true
    
    [multipath]
    max_paths = 4
    min_path_quality = 0.5
```

Deploy with custom values:
```bash
helm upgrade --install nyx charts/nyx -f values-production.yaml
```

See `charts/nyx/values.yaml` for all configuration options and `docs/quickstart-ubuntu-k8s.md` for deployment guide.

## Documentation

- **Getting Started**: `docs/index.md`
- **Architecture Guide**: `docs/architecture.md` (1050+ lines, ASCII diagrams)
- **Configuration Reference**: `docs/configuration.md` (850+ lines, 80+ parameters)
- **API Documentation**: `docs/api.md` (550+ lines, 20 gRPC RPCs)
- **Specifications**: `docs/specs.md` (Implementation Status Matrix)
- **Kubernetes Deployment**: `docs/quickstart-ubuntu-k8s.md`

### Examples

- **Full Configuration**: `examples/full_config.toml` (350+ lines with inline comments)
- **gRPC Client**: `nyx-sdk/examples/grpc_client_example.rs`
- **cMix Configuration**: `examples/cmix_config.toml`

## Specifications (brief)

- Nyx Protocol v1.0 (draft; includes planned features): `spec/Nyx_Protocol_v1.0_Spec_EN.md`
	- Multipath data plane (per-packet PathID), extended header with 12-byte CID, fixed 1280B payloads
	- Hybrid post-quantum handshake (X25519 + Kyber) and HPKE support; anti-replay window 2^20 per direction
	- Plugin frames 0x50–0x5F with CBOR header; capability negotiation via CBOR list (see policy below)
	- Optional cMix mode (batch≈100, VDF≈100ms), adaptive cover traffic (target utilization 0.2–0.6)
	- Compliance levels: Core / Plus / Full; telemetry: OTLP spans alongside Prometheus
	- Note: Some items are roadmap-level and may not be fully implemented yet.
- Nyx Protocol v0.1 (baseline implemented set): `spec/Nyx_Protocol_v0.1_Spec_EN.md`
- Capability Negotiation Policy: `spec/Capability_Negotiation_Policy_EN.md`
	- CBOR entries `{id:u32, flags:u8, data:bytes}`; flags bit 0x01 = Required
	- Unsupported Required capability → CLOSE 0x07 with the 4-byte unsupported ID in reason
- Design Document: `spec/Nyx_Design_Document_EN.md`
	- Principles: security-by-design, performance without compromise, modularity, formal methods
	- Layers: secure stream, mix routing, obfuscation+FEC, transport; async pipeline with backpressure
	- Cryptography: AEAD/KDF/HPKE, key rotation, PQ readiness; threat model covers global passive/active

## Contributing

We welcome contributions! Please review `CONTRIBUTING.md` and `CODE_OF_CONDUCT.md`. Keep changes safe, focused, and well-tested.

## License

Licensed under either of:

- MIT (`LICENSE-MIT`)
- Apache-2.0 (`LICENSE-APACHE`)

Choose the license that best fits your needs.

