# NyxNet Project Overview

**Last Updated**: October 7, 2025  
**Version**: v1.0  
**Status**: ✅ Complete (Full Codebase Compliance)

[日本語版](./01_PROJECT_OVERVIEW.md)

---

## Purpose

NyxNet is a **privacy-first, post-quantum secure network stack** written in pure Rust. It provides anonymous communication using mix network architecture with built-in quantum-resistant cryptography, designed for the quantum computing era.

### Problems Solved

1. **Quantum Computer Threat**: Existing public-key cryptography (RSA, ECDH) can be broken by quantum computers. NyxNet adopts hybrid cryptography (ML-KEM + X25519) for quantum resistance.

2. **Traffic Analysis Resistance**: Modern network surveillance can infer communication content from traffic patterns even when encrypted. NyxNet prevents traffic analysis through Sphinx encryption and cover traffic generation.

3. **Trustworthy Privacy Communication**: Tor and VPNs require trust in single points of failure or operators. NyxNet eliminates single points of trust through decentralized mix network architecture.

4. **Mobile Anonymity**: Provides practical anonymity on battery-constrained mobile devices. Low Power Mode and push notification integration balance power efficiency and anonymity.

---

## Key Features

### Core Features (Core Compliance Level)

- **Post-Quantum Cryptography**: Hybrid handshake using ML-KEM-768 (NIST standardized) + X25519
- **Sphinx Onion Routing**: 3-hop mix network for traffic anonymization with layered encryption
- **QUIC Transport**: Low-latency multipath transport over UDP datagrams
- **Forward Error Correction (FEC)**: Adaptive redundancy control using Reed-Solomon codes
- **gRPC Control API**: 20+ RPCs for node management and stream control
- **Replay Attack Protection**: Timestamp-based nonce verification with Bloom filters

### Extended Features (Plus Compliance Level)

- **Multipath Routing**: Simultaneous communication over multiple paths with automatic failover
- **Cover Traffic**: Adaptive dummy packet generation based on Poisson distribution
- **NAT Traversal**: STUN support via ICE Lite implementation
- **Hot Configuration Reload**: Dynamic configuration updates without downtime
- **Internationalization (i18n)**: Fluent-format message localization

### Full Features (Full Compliance Level)

- **cMix Integration**: VDF (Verifiable Delay Function) based batch processing
- **Plugin Framework**: Dynamic protocol extension using CBOR
- **Low Power Mode**: Battery optimization for mobile environments
- **OpenTelemetry Integration**: Tracing and metrics via OTLP (Jaeger/Tempo compatible)
- **Kubernetes Support**: Helm charts, HPA, PDB, ServiceMonitor

### Proxy Features

- **Tor-compatible Proxy**: SOCKS5 (RFC 1928) and HTTP CONNECT proxy (Go implementation)
- **Browser Integration**: Compatible with Firefox, Chrome, curl, wget
- **Pure Go TLS**: Zero C/C++ dependency TLS implementation (crypto/tls)

---

## Technology Stack Overview

### Programming Languages

| Language | Purpose | Rationale |
|----------|---------|-----------|
| **Rust** | Core network stack | Memory safety, zero-cost abstractions, async/await |
| **Go** | HTTP proxy | Pure Go TLS, cross-platform |
| **TLA+** | Formal verification | Mathematical proof of protocol correctness |

### Major Frameworks & Libraries

#### Rust Crates

**Async Runtime**
- `tokio` 1.37: Async I/O, multi-threaded runtime

**Cryptography**
- `ml-kem` 0.2: ML-KEM-768 (NIST standard post-quantum cryptography)
- `x25519-dalek` 2.0: Elliptic Curve Diffie-Hellman
- `chacha20poly1305` 0.10: Authenticated Encryption with Associated Data (AEAD)
- `blake3` 1.5: Fast cryptographic hash

**Networking**
- `socket2` 0.6: Cross-platform socket API
- `tonic` 0.11: gRPC framework (Pure Rust, no TLS)

**Serialization**
- `serde` 1.0 + `serde_json`: JSON
- `ciborium` 0.2: CBOR (Concise Binary Object Representation)
- `toml` 0.7: Configuration files

**Testing & Benchmarking**
- `criterion` 0.5: Statistical benchmarking framework
- `proptest` 1.0: Property-based testing

#### Go Packages (nyx-http-proxy)

- `crypto/tls`: Pure Go TLS implementation (Zero C/C++ dependencies)
- `net/http`: HTTP/HTTPS handling
- `golang.org/x/time`: Rate limiting
- `golang.org/x/net`: Extended network primitives
- Standard library: `net`, `io`, `context`, `sync`

**Note**: Go implementation explicitly avoids C/C++ dependencies, using Pure Go implementations only.

### Database & Storage

- **In-Memory**: `DashMap` (concurrent HashMap) for fast peer cache
- **Persistence**: TOML configuration files, future consideration for BoltDB

### Cloud & Deployment

- **Containers**: Docker, multi-stage build
- **Orchestration**: Kubernetes (Helm charts provided)
- **CI/CD**: GitHub Actions (18 workflows)
- **Monitoring**: Prometheus, OpenTelemetry, Grafana

### Development Tools

- **Build System**: Cargo (Rust workspace), Go modules
- **Linters**: Clippy, cargo-audit, go vet
- **Formatters**: rustfmt, gofmt
- **Fuzzing**: cargo-fuzz (libFuzzer)

---

## Directory Structure

```
NyxNet/
├── nyx-core/              # Core utilities, types, configuration
│   ├── src/
│   │   ├── config.rs      # Configuration loading & validation
│   │   ├── types.rs       # Basic types (ConnectionId, StreamId, etc.)
│   │   ├── error.rs       # Error type definitions
│   │   ├── security.rs    # Security policies
│   │   └── i18n.rs        # Internationalization support
│   └── Cargo.toml
│
├── nyx-crypto/            # Cryptographic primitives
│   ├── src/
│   │   ├── hybrid_handshake.rs  # ML-KEM + X25519 hybrid
│   │   ├── aead.rs              # ChaCha20Poly1305 wrapper
│   │   ├── kdf.rs               # HKDF key derivation
│   │   ├── session.rs           # Session key management
│   │   └── sphinx.rs            # Sphinx onion encryption
│   └── Cargo.toml
│
├── nyx-transport/         # QUIC datagram transport
│   ├── src/
│   │   ├── udp.rs         # Pure Rust UDP implementation
│   │   ├── nat.rs         # NAT Traversal (ICE Lite)
│   │   └── multipath.rs   # Multipath routing
│   └── Cargo.toml
│
├── nyx-mix/               # Mix network layer
│   ├── src/
│   │   ├── sphinx.rs      # Sphinx onion routing
│   │   ├── cover.rs       # Cover traffic generation
│   │   ├── larmix.rs      # Latency-aware routing
│   │   └── cmix.rs        # cMix integration
│   └── Cargo.toml
│
├── nyx-stream/            # Stream management
│   ├── src/
│   │   ├── stream.rs      # Stream protocol
│   │   ├── frame.rs       # Frame definitions
│   │   └── plugin.rs      # Plugin framework
│   └── Cargo.toml
│
├── nyx-fec/               # Forward Error Correction
│   ├── src/
│   │   ├── reed_solomon.rs  # Reed-Solomon codes
│   │   └── adaptive.rs      # Adaptive redundancy control
│   └── Cargo.toml
│
├── nyx-control/           # Control plane (DHT, config sync)
│   ├── src/
│   │   ├── dht/           # Kademlia DHT implementation
│   │   ├── gossip.rs      # Configuration gossip protocol
│   │   └── push.rs        # Push notification token management
│   └── Cargo.toml
│
├── nyx-daemon/            # Main daemon
│   ├── src/
│   │   └── main.rs        # gRPC server, JSON-RPC, main loop
│   └── Cargo.toml
│
├── nyx-cli/               # Command-line interface
│   ├── src/
│   │   └── main.rs        # CLI implementation
│   └── Cargo.toml
│
├── nyx-sdk/               # Application SDK
│   ├── src/
│   │   ├── client.rs      # Daemon client
│   │   └── stream.rs      # Stream API
│   └── Cargo.toml
│
├── nyx-sdk-wasm/          # WASM SDK (Browser/Node.js)
│   └── Cargo.toml
│
├── nyx-mobile-ffi/        # Mobile FFI (iOS/Android)
│   ├── src/
│   │   └── lib.rs         # C-ABI compatible interface
│   └── Cargo.toml
│
├── nyx-http-proxy/        # Tor-compatible HTTP proxy (Go)
│   ├── main.go            # Proxy server
│   ├── socks5.go          # SOCKS5 implementation
│   ├── connect.go         # HTTP CONNECT implementation
│   └── mixbridge.go       # Mix layer IPC bridge
│
├── nyx-telemetry/         # Telemetry & metrics
│   ├── src/
│   │   ├── prometheus.rs  # Prometheus exporter
│   │   └── otlp.rs        # OpenTelemetry OTLP
│   └── Cargo.toml
│
├── nyx-conformance/       # Deterministic simulator
│   └── src/               # Property-based tests
│
├── tests/                 # Integration tests
│   ├── benchmarks/        # Application-level benchmarks
│   └── integration/       # E2E tests
│
├── formal/                # Formal verification (TLA+ specs)
│   ├── NyxBasicVerification.tla
│   └── NyxCryptography.tla
│
├── docs/                  # Documentation
├── spec/                  # Protocol specifications
├── charts/                # Helm charts
├── scripts/               # Build & deployment scripts
│
├── Cargo.toml             # Rust workspace definition
├── nyx.toml               # Sample configuration
├── Dockerfile             # Container image
├── Makefile               # Compliance test tasks
└── README.md              # Project README
```

### Role Descriptions

- **nyx-core**: Shared basic types, error handling, configuration management
- **nyx-crypto**: Cryptographic primitives (hybrid PQ crypto, AEAD, KDF)
- **nyx-transport**: Pure Rust QUIC/UDP transport, NAT Traversal
- **nyx-mix**: Sphinx onion routing, cover traffic, cMix
- **nyx-stream**: Stream protocol, frame definitions, plugins
- **nyx-fec**: Reed-Solomon FEC, adaptive redundancy control
- **nyx-control**: DHT, gossip protocol, push notification management
- **nyx-daemon**: Main server process, gRPC/JSON-RPC API
- **nyx-cli**: Command-line tool (config validation, diagnostics, stream ops)
- **nyx-sdk**: Application integration SDK (Rust)
- **nyx-sdk-wasm**: WebAssembly SDK (Browser/Node.js)
- **nyx-mobile-ffi**: iOS/Android C-ABI FFI
- **nyx-http-proxy**: SOCKS5/HTTP CONNECT proxy (Go, Pure TLS)
- **nyx-telemetry**: Prometheus/OTLP metrics & tracing
- **nyx-conformance**: Protocol compliance test framework

---

## Architecture Principles

### 1. Memory Safety First

- `#![forbid(unsafe_code)]`: Unsafe code forbidden in all crates
- Memory safety guaranteed by Rust's ownership system
- Zero-copy optimizations applied within safe bounds

### 2. Zero C/C++ Dependencies

- Pure Rust cryptography (`ml-kem`, `x25519-dalek`, `chacha20poly1305`)
- Pure Go TLS (`crypto/tls`)
- Eliminates C dependencies (ring, OpenSSL, libsodium, etc.)

### 3. Modular Design

- Each crate is independently testable
- Flexible build configuration via feature flags
- Trait-driven abstraction

### 4. Configuration-Driven

- Declarative configuration via TOML files
- Environment variable override support
- JSON Schema validation

### 5. Observability

- Structured logging (JSON format)
- Prometheus metrics
- OpenTelemetry tracing
- Health check endpoints

---

## Test Coverage

| Category | Test Count | Description |
|----------|------------|-------------|
| Unit Tests | 300+ | Per-module function-level tests |
| Integration Tests | 50+ | Cross-crate interaction tests |
| Property Tests | 30+ | Randomized tests using proptest |
| Benchmarks | 15+ | Statistical benchmarks with Criterion |
| Fuzzing | 10+ targets | Continuous fuzzing with libFuzzer |
| E2E Tests | 20+ | Real-world Kubernetes environment tests |
| Formal Verification | 15+ specs | TLA+ protocol verification |

**Total**: 400+ tests

---

## License

**Dual License**: MIT OR Apache-2.0

The entire project is provided under a dual license of MIT License or Apache-2.0 License. Users can choose either license.

---

## Security Policy

Vulnerability reporting: See `SECURITY.md`

- Report security issues privately (GitHub Security Advisories)
- Initial response within 24 hours
- 90-day confidentiality period after patch release

---

## Community

- **GitHub**: [SeleniaProject/Nyx](https://github.com/SeleniaProject/Nyx)
- **Issue Tracker**: GitHub Issues
- **Contributing**: See `CONTRIBUTING.md`
- **Code of Conduct**: See `CODE_OF_CONDUCT.md`

---

## Disclaimer: Inferred Content

The following information is reasonably inferred from existing documents and code:

- **GitHub repository URL**: Inferred from README badge links
- **Community links**: Standard OSS project structure assumption
- **Future storage**: Inferred from TODO comments in code

For precise information, please refer to actual code and configuration files.
