# NyxNet

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Rust](https://img.shields.io/badge/rust-1.70%2B-orange.svg)](https://www.rust-lang.org/)
[![Go](https://img.shields.io/badge/go-1.21%2B-00ADD8.svg)](https://go.dev/)

**NyxNet** is a privacy-first, post-quantum secure network stack written in pure Rust. It provides anonymous communication using mix network architecture with built-in quantum-resistant cryptography, designed for the era of quantum computing threats.

[日本語版 README はこちら](README-ja.md)

---

## Table of Contents

- [Features](#features)
- [Architecture](#architecture)
- [Quick Start](#quick-start)
- [Installation](#installation)
- [Usage Examples](#usage-examples)
- [Documentation](#documentation)
- [Performance](#performance)
- [Security](#security)
- [Development](#development)
- [Contributing](#contributing)
- [License](#license)

---

## Features

### 🎯 Feature Matrix

```mermaid
mindmap
  root((NyxNet))
    Security
      Post-Quantum Crypto
        ML-KEM-768
        X25519 Hybrid
      Sphinx Routing
        3-hop Mix Network
        Layered Encryption
      Replay Protection
        Bloom Filters
        Timestamp Nonce
    Performance
      QUIC Transport
        Low Latency
        UDP Datagrams
      Multipath Routing
        Auto Failover
        Load Balancing
      FEC
        Reed-Solomon
        Adaptive Redundancy
    Privacy
      Cover Traffic
        Poisson Distribution
        Dummy Packets
      Traffic Analysis Resistance
      No Single Trust Point
    Integration
      gRPC API
        20+ RPCs
        Stream Control
      SOCKS5 Proxy
        Tor Compatible
        Browser Support
      OpenTelemetry
        Jaeger
        Prometheus
    Mobile
      Low Power Mode
        Battery Optimization
      FFI Bindings
        iOS
        Android
      Push Proxy
```

### Core Features

| Feature | Description | Status |
|---------|-------------|--------|
| **🔐 Post-Quantum Cryptography** | Hybrid handshake using ML-KEM-768 (NIST-standardized) and X25519 | ✅ Complete |
| **🧅 Sphinx Onion Routing** | 3-hop mix network with layered encryption for traffic anonymization | ✅ Complete |
| **⚡ QUIC Transport** | Low-latency multipath transport over UDP datagrams | ✅ Complete |
| **🛡️ Forward Error Correction** | Adaptive redundancy control using Reed-Solomon codes | ✅ Complete |
| **🎛️ gRPC Control API** | 20+ RPCs for node management and stream control | ✅ Complete |
| **🔒 Replay Attack Protection** | Timestamp-based nonce verification with Bloom filters | ✅ Complete |

### Advanced Features

| Feature | Description | Status |
|---------|-------------|--------|
| **🛤️ Multipath Routing** | Simultaneous communication over multiple paths with automatic failover | ✅ Complete |
| **👻 Cover Traffic** | Adaptive dummy packet generation based on Poisson distribution | ✅ Complete |
| **🌐 NAT Traversal** | STUN support via ICE Lite implementation | ✅ Complete |
| **🔄 Hot Configuration Reload** | Dynamic configuration updates without downtime | ✅ Complete |
| **🌍 Internationalization** | Fluent-format message localization | ✅ Complete |

### Full Capabilities

| Feature | Description | Status |
|---------|-------------|--------|
| **⚙️ cMix Integration** | VDF (Verifiable Delay Function) based batch processing | ✅ Complete |
| **🔌 Plugin Framework** | Dynamic protocol extension using CBOR | ✅ Complete |
| **🔋 Low Power Mode** | Battery optimization for mobile environments | ✅ Complete |
| **📊 OpenTelemetry** | Tracing and metrics via OTLP (Jaeger/Tempo compatible) | ✅ Complete |
| **☸️ Kubernetes Support** | Helm charts, HPA, PDB, ServiceMonitor | ✅ Complete |

### Proxy Features

| Feature | Description | Status |
|---------|-------------|--------|
| **🌐 SOCKS5 Proxy** | RFC 1928 compliant, Tor-compatible | ✅ Complete |
| **🌐 HTTP CONNECT** | Proxy support for HTTPS traffic | ✅ Complete |
| **🔐 Pure Go TLS** | Zero C/C++ dependency TLS implementation | ✅ Complete |
| **🦊 Browser Integration** | Firefox, Chrome, curl, wget compatible | ✅ Complete |

---

## Architecture

NyxNet follows a layered architecture with clear separation of concerns:

```mermaid
graph TB
    subgraph "Application Layer"
        APP[User Applications]
        BROWSER[Web Browsers]
        MOBILE[Mobile Apps]
    end
    
    subgraph "SDK Layer"
        SDK[nyx-sdk<br/>Stream API]
        WASM[nyx-sdk-wasm<br/>WebAssembly]
        FFI[nyx-mobile-ffi<br/>iOS/Android]
    end
    
    subgraph "Proxy Layer"
        SOCKS[SOCKS5 Proxy]
        HTTP[HTTP CONNECT]
    end
    
    subgraph "Control Plane"
        DAEMON[nyx-daemon<br/>gRPC/JSON-RPC API]
        CLI[nyx-cli<br/>Management Tool]
    end
    
    subgraph "Data Plane"
        STREAM[nyx-stream<br/>Stream Manager]
        MIX[nyx-mix<br/>Sphinx Routing]
        TRANSPORT[nyx-transport<br/>QUIC Multipath]
        FEC[nyx-fec<br/>Reed-Solomon]
    end
    
    subgraph "Foundation Layer"
        CRYPTO[nyx-crypto<br/>ML-KEM + X25519]
        CORE[nyx-core<br/>Types & Config]
        TELEMETRY[nyx-telemetry<br/>Metrics & Tracing]
    end
    
    APP --> SDK
    BROWSER --> SOCKS
    BROWSER --> HTTP
    MOBILE --> FFI
    
    SDK --> DAEMON
    WASM --> DAEMON
    FFI --> DAEMON
    SOCKS --> DAEMON
    HTTP --> DAEMON
    CLI --> DAEMON
    
    DAEMON --> STREAM
    DAEMON --> MIX
    
    STREAM --> MIX
    MIX --> TRANSPORT
    MIX --> FEC
    TRANSPORT --> FEC
    
    STREAM --> CRYPTO
    MIX --> CRYPTO
    TRANSPORT --> CORE
    FEC --> CORE
    
    DAEMON --> TELEMETRY
    STREAM --> TELEMETRY
    
    style APP fill:#e1f5ff
    style BROWSER fill:#e1f5ff
    style MOBILE fill:#e1f5ff
    style CRYPTO fill:#ffe1e1
    style CORE fill:#ffe1e1
    style DAEMON fill:#fff4e1
    style MIX fill:#e8f5e1
```

### Key Components

| Component | Description | Key Features |
|-----------|-------------|--------------|
| **nyx-core** | Core utilities, types, configuration | Error handling, config hot-reload, i18n |
| **nyx-crypto** | Post-quantum cryptography | ML-KEM-768, X25519, ChaCha20-Poly1305, BLAKE3 |
| **nyx-transport** | QUIC-based transport layer | Multipath routing, NAT traversal, UDP datagrams |
| **nyx-mix** | Mix network implementation | Sphinx packet format, 3-hop routing, cover traffic |
| **nyx-fec** | Forward Error Correction | Reed-Solomon codes, adaptive redundancy |
| **nyx-stream** | Stream management | Multiplexing, flow control, reconnection |
| **nyx-daemon** | Control plane daemon | gRPC API (20+ RPCs), JSON-RPC 2.0, node management |
| **nyx-sdk** | Client SDK | High-level API, async/await, error recovery |
| **nyx-cli** | Command-line tool | Node control, stream inspection, diagnostics |
| **nyx-http-proxy** | SOCKS5/HTTP proxy | Tor-compatible, pure Go TLS, browser integration |

---

## Quick Start

### Prerequisites

- **Rust**: 1.70.0+ (recommended: 1.75+)
- **Cargo**: 1.70.0+
- **Go**: 1.21+ (for HTTP proxy)
- **Git**: 2.30+

### Build from Source

```bash
# Clone the repository
git clone https://github.com/SeleniaProject/Nyx.git
cd Nyx

# Build Rust workspace (release mode)
cargo build --release

# Build Go HTTP proxy
cd nyx-http-proxy
go build -o nyx-http-proxy
cd ..
```

### Run the Daemon

```bash
# Start the NyxNet daemon
./target/release/nyx-daemon --config nyx.toml

# In another terminal, check status
./target/release/nyx-cli status
```

### Start the Proxy

```bash
# Start SOCKS5 proxy on localhost:9050
./nyx-http-proxy/nyx-http-proxy --socks-port 9050
```

---

## Installation

### From Source

```bash
# Install system-wide (requires sudo/admin)
cargo install --path nyx-daemon
cargo install --path nyx-cli

# Or use the binaries directly from target/release/
```

### Using Docker

```bash
# Build Docker image
docker build -t nyxnet:latest .

# Run daemon
docker run -d --name nyx-daemon \
  -p 9050:9050 \
  -v $(pwd)/nyx.toml:/etc/nyx/nyx.toml \
  nyxnet:latest
```

### Using Kubernetes (Helm)

```bash
# Install Helm chart
helm install nyx ./charts/nyx \
  --namespace nyx-system \
  --create-namespace

# Check deployment status
kubectl get pods -n nyx-system
```

---

## Usage Examples

### Communication Flow

```mermaid
sequenceDiagram
    participant App as Application
    participant SDK as nyx-sdk
    participant Daemon as nyx-daemon
    participant Mix1 as Mix Node 1
    participant Mix2 as Mix Node 2
    participant Mix3 as Mix Node 3
    participant Dest as Destination
    
    App->>SDK: create_stream(config)
    SDK->>Daemon: gRPC: CreateStream
    Daemon->>Daemon: Generate Sphinx packet
    
    Note over Daemon,Mix1: Layer 3 Encryption
    Daemon->>Mix1: Encrypted packet (Layer 3,2,1)
    
    Note over Mix1,Mix2: Layer 2 Encryption
    Mix1->>Mix1: Decrypt Layer 3
    Mix1->>Mix2: Encrypted packet (Layer 2,1)
    
    Note over Mix2,Mix3: Layer 1 Encryption
    Mix2->>Mix2: Decrypt Layer 2
    Mix2->>Mix3: Encrypted packet (Layer 1)
    
    Mix3->>Mix3: Decrypt Layer 1
    Mix3->>Dest: Forward to destination
    
    Dest-->>Mix3: Response
    Mix3-->>Mix2: Encrypted response
    Mix2-->>Mix1: Encrypted response
    Mix1-->>Daemon: Encrypted response
    Daemon-->>SDK: Decrypted data
    SDK-->>App: Application data
```

### Using the SDK (Rust)

```rust
use nyx_sdk::{DaemonClient, StreamConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Connect to local daemon
    let client = DaemonClient::connect("http://localhost:50051").await?;
    
    // Create anonymous stream to destination
    let config = StreamConfig {
        destination: "example.com:443".to_string(),
        multipath: true,
        low_power: false,
    };
    
    let mut stream = client.create_stream(config).await?;
    
    // Send data through anonymous network
    stream.write_all(b"GET / HTTP/1.1\r\nHost: example.com\r\n\r\n").await?;
    
    // Read response
    let mut buffer = vec![0u8; 4096];
    let n = stream.read(&mut buffer).await?;
    println!("Received {} bytes", n);
    
    Ok(())
}
```

### Using SOCKS5 Proxy with curl

```bash
# Configure curl to use NyxNet SOCKS5 proxy
curl --socks5 localhost:9050 https://example.com

# Or set environment variable
export ALL_PROXY=socks5://localhost:9050
curl https://example.com
```

### Using with Firefox

1. Open Firefox Settings → Network Settings
2. Select "Manual proxy configuration"
3. SOCKS Host: `localhost`, Port: `9050`
4. Select "SOCKS v5"
5. Check "Proxy DNS when using SOCKS v5"

---

## Documentation

Comprehensive documentation is available in the `docs/` directory:

- [**Project Overview**](docs/01_PROJECT_OVERVIEW.md) - Goals, use cases, and compliance levels
- [**System Architecture**](docs/02_SYSTEM_ARCHITECTURE.md) - Detailed architecture design
- [**Major Features**](docs/03_MAJOR_FEATURES.md) - In-depth feature descriptions
- [**API Reference**](docs/04_API_REFERENCE.md) - gRPC/JSON-RPC API documentation
- [**Development Setup**](docs/05_DEVELOPMENT_SETUP.md) - Environment setup and contribution guide

### Comparison with Tor

See [Tor Comparison Guide](docs/ACTUAL_TOR_COMPARISON.md) for detailed comparison with Tor network.

### Formal Verification

NyxNet includes formal verification using TLA+ specifications in the `formal/` directory. See [Verification Status](formal/FINAL_VERIFICATION_STATUS.md) for details.

---

## Performance

### Benchmarks

```mermaid
graph LR
    subgraph "Performance Metrics"
        A[Handshake<br/>~2.5ms] --> B[Packet Processing<br/>~150µs]
        B --> C[Throughput<br/>500 Mbps]
        C --> D[Latency<br/>+80-120ms]
    end
    
    style A fill:#90EE90
    style B fill:#90EE90
    style C fill:#87CEEB
    style D fill:#FFD700
```

NyxNet achieves competitive performance with strong security guarantees:

| Metric | Value | Details |
|--------|-------|---------|
| **Handshake** | ~2.5ms | Hybrid PQ handshake (ML-KEM-768 + X25519) |
| **Packet Processing** | ~150µs | Per packet (3-hop Sphinx routing) |
| **Throughput** | Up to 500 Mbps | Per stream with FEC enabled |
| **Latency** | +80-120ms | vs. direct connection (3-hop mix network) |
| **Memory** | ~50MB | Per daemon instance (typical workload) |
| **CPU** | <5% | Per stream on modern CPU |

Run benchmarks locally:

```bash
# Crypto benchmarks
cargo bench -p nyx-crypto

# Core performance benchmarks
cargo bench -p nyx-core --bench security_scalability_benchmark

# Full integration benchmarks
cargo bench -p tests --bench integration_benchmark
```

### Comparison with Tor

```mermaid
graph TB
    subgraph "Security Features"
        N1[NyxNet<br/>ML-KEM-768 ✅]
        T1[Tor<br/>No PQ ❌]
    end
    
    subgraph "Routing"
        N2[NyxNet<br/>Multipath ✅]
        T2[Tor<br/>Single Path ❌]
    end
    
    subgraph "Mobile"
        N3[NyxNet<br/>Low Power ✅]
        T3[Tor<br/>Limited ⚠️]
    end
    
    subgraph "Verification"
        N4[NyxNet<br/>TLA+ Specs ✅]
        T4[Tor<br/>Partial ⚠️]
    end
    
    style N1 fill:#90EE90
    style N2 fill:#90EE90
    style N3 fill:#90EE90
    style N4 fill:#90EE90
    style T1 fill:#FFB6C6
    style T2 fill:#FFB6C6
    style T3 fill:#FFD700
    style T4 fill:#FFD700
```

| Metric | NyxNet | Tor |
|--------|--------|-----|
| **Post-Quantum Security** | ✅ ML-KEM-768 (NIST standardized) | ❌ Not yet implemented |
| **Multipath Support** | ✅ Native support with auto-failover | ❌ Single path only |
| **Mobile Optimization** | ✅ Low Power Mode, battery-aware | ⚠️ Limited optimization |
| **Formal Verification** | ✅ TLA+ specifications | ⚠️ Partial coverage |
| **Transport** | ✅ QUIC (UDP) | ⚠️ TCP only |
| **FEC** | ✅ Adaptive Reed-Solomon | ❌ No FEC |
| **Language** | ✅ Pure Rust (memory-safe) | ⚠️ C (memory-unsafe) |

---

## Security

### Cryptographic Stack

```mermaid
graph TD
    subgraph "Key Exchange Layer"
        KEM[ML-KEM-768<br/>NIST FIPS 203]
        ECDH[X25519<br/>Curve25519]
        KEM -.Hybrid.-> HYBRID[Hybrid KEM]
        ECDH -.Hybrid.-> HYBRID
    end
    
    subgraph "Encryption Layer"
        HYBRID --> KDF[HKDF-SHA256<br/>Key Derivation]
        KDF --> AEAD[ChaCha20-Poly1305<br/>AEAD Cipher]
    end
    
    subgraph "Integrity Layer"
        AEAD --> HASH[BLAKE3<br/>Cryptographic Hash]
        HASH --> SPHINX[Sphinx Packet Format<br/>Layered Encryption]
    end
    
    subgraph "Protection Layer"
        SPHINX --> BLOOM[Bloom Filter<br/>Replay Protection]
        SPHINX --> TIMESTAMP[Timestamp Nonce<br/>Time Window]
    end
    
    style KEM fill:#FFE1E1
    style ECDH fill:#FFE1E1
    style HYBRID fill:#90EE90
    style AEAD fill:#87CEEB
    style SPHINX fill:#DDA0DD
```

### Cryptographic Primitives

| Component | Algorithm | Purpose | Standard |
|-----------|-----------|---------|----------|
| **Key Exchange** | ML-KEM-768 | Post-quantum KEM | NIST FIPS 203 |
| **Key Exchange** | X25519 | Classical ECDH | RFC 7748 |
| **AEAD** | ChaCha20-Poly1305 | Authenticated encryption | RFC 8439 |
| **Hash** | BLAKE3 | Cryptographic hash | Fast, secure |
| **KDF** | HKDF-SHA256 | Key derivation | RFC 5869 |
| **Packet Format** | Sphinx | Mix network routing | Mixnet research |

### Security Properties

```mermaid
mindmap
  root((Security))
    Anonymity
      Sender Anonymity
      Receiver Anonymity
      Relationship Anonymity
    Confidentiality
      End-to-End Encryption
      Layered Encryption
      Forward Secrecy
    Integrity
      Message Authentication
      Replay Protection
      Timestamp Validation
    Availability
      Multipath Resilience
      FEC Recovery
      Auto Failover
```

### Security Audits

NyxNet is under active development. Security audit reports will be published upon completion.

### Reporting Vulnerabilities

Please report security vulnerabilities to: **security@selenia-project.org**

See [SECURITY.md](SECURITY.md) for our security policy.

---

## Development

### Building and Testing

```bash
# Run all tests
cargo test --workspace --release

# Run tests with coverage
cargo install cargo-tarpaulin
cargo tarpaulin --workspace --out Html

# Run linters
cargo clippy --workspace --all-features -- -D warnings

# Format code
cargo fmt --all -- --check
```

### Project Structure

```mermaid
graph TD
    subgraph "Core Libraries"
        CORE[nyx-core<br/>Core Types & Config]
        CRYPTO[nyx-crypto<br/>PQ Cryptography]
    end
    
    subgraph "Network Layer"
        TRANSPORT[nyx-transport<br/>QUIC Transport]
        MIX[nyx-mix<br/>Mix Network]
        FEC[nyx-fec<br/>Error Correction]
        STREAM[nyx-stream<br/>Stream Manager]
    end
    
    subgraph "Control Layer"
        DAEMON[nyx-daemon<br/>Control Plane]
        CONTROL[nyx-control<br/>Node Control]
        TELEMETRY[nyx-telemetry<br/>Observability]
    end
    
    subgraph "Client Layer"
        SDK[nyx-sdk<br/>Rust SDK]
        WASM[nyx-sdk-wasm<br/>WebAssembly]
        FFI[nyx-mobile-ffi<br/>Mobile FFI]
        CLI[nyx-cli<br/>CLI Tool]
    end
    
    subgraph "Proxy Layer"
        PROXY[nyx-http-proxy<br/>SOCKS5/HTTP]
        PUSH[nyx-push-proxy<br/>Push Notifications]
    end
    
    subgraph "Support"
        DOCS[docs/<br/>Documentation]
        FORMAL[formal/<br/>TLA+ Specs]
        TESTS[tests/<br/>Integration Tests]
        EXAMPLES[examples/<br/>Usage Examples]
    end
    
    CORE --> CRYPTO
    CRYPTO --> TRANSPORT
    CRYPTO --> MIX
    TRANSPORT --> FEC
    MIX --> STREAM
    STREAM --> DAEMON
    DAEMON --> SDK
    DAEMON --> CLI
    DAEMON --> PROXY
    DAEMON --> TELEMETRY
    
    style CORE fill:#FFE1E1
    style CRYPTO fill:#FFE1E1
    style DAEMON fill:#FFD700
    style SDK fill:#87CEEB
    style DOCS fill:#DDA0DD
```

**Directory Layout:**

```
NyxNet/
├── nyx-core/          # Core utilities and types
├── nyx-crypto/        # Cryptographic primitives
├── nyx-transport/     # QUIC transport layer
├── nyx-mix/           # Mix network implementation
├── nyx-fec/           # Forward Error Correction
├── nyx-stream/        # Stream management
├── nyx-daemon/        # Control plane daemon
├── nyx-sdk/           # Client SDK
├── nyx-cli/           # CLI tool
├── nyx-http-proxy/    # SOCKS5/HTTP proxy (Go)
├── docs/              # Documentation
├── formal/            # TLA+ specifications
├── tests/             # Integration tests
└── examples/          # Usage examples
```

### Contributing

We welcome contributions! Please see [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Commit your changes (`git commit -m 'Add amazing feature'`)
4. Push to the branch (`git push origin feature/amazing-feature`)
5. Open a Pull Request

### Code of Conduct

This project adheres to the [Code of Conduct](CODE_OF_CONDUCT.md). By participating, you are expected to uphold this code.

---

## License

NyxNet is dual-licensed under:

- **MIT License** ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)
- **Apache License, Version 2.0** ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)

You may choose either license for your purposes.

---

## Acknowledgments

NyxNet builds upon research and protocols from:

- **Tor Project**: Onion routing concepts
- **Mixnet Research**: Sphinx packet format, Loopix timing strategy
- **NIST PQC**: ML-KEM standardization
- **Rust Community**: Excellent cryptographic libraries

---

## Contact

- **Project Website**: https://selenia-project.org
- **GitHub**: https://github.com/SeleniaProject/Nyx
- **Email**: contact@selenia-project.org

---

**Built with ❤️ by the Selenia Project team**