# NyxNet System Architecture Design Document

**Last Updated**: October 7, 2025  
**Target Version**: v1.0

[日本語版](./02_SYSTEM_ARCHITECTURE.md)

---

## Overview

NyxNet is a distributed privacy network stack based on layered architecture. Each layer has clear responsibilities and can be tested independently without dependencies on lower layers.

---

## Architecture Diagram (Text Representation)

```
┌─────────────────────────────────────────────────────────────┐
│                    Application Layer                         │
│  (User Apps, Browser Extensions, Mobile Apps)                │
└────────────────┬────────────────────────────────────────────┘
                 │
                 ▼
┌─────────────────────────────────────────────────────────────┐
│                   SDK Layer (nyx-sdk)                        │
│  - Stream API                                                │
│  - Daemon Client (gRPC/JSON-RPC)                             │
│  - Reconnection & Error Handling                             │
└────────────────┬────────────────────────────────────────────┘
                 │
                 ▼
┌─────────────────────────────────────────────────────────────┐
│              Control Plane (nyx-daemon)                      │
│  - gRPC Service (20+ RPCs)                                   │
│  - JSON-RPC 2.0 (IPC: Unix socket / Named pipe)             │
│  - Configuration Management                                  │
│  - Node Lifecycle Management                                 │
└────────┬────────┬────────┬────────┬────────┬────────────────┘
         │        │        │        │        │
         ▼        ▼        ▼        ▼        ▼
┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌───────────┐
│ Stream  │ │   Mix   │ │Transport│ │  Crypto │ │Telemetry  │
│ Manager │ │ Network │ │  Layer  │ │  Layer  │ │  Layer    │
│(nyx-    │ │(nyx-mix)│ │(nyx-    │ │(nyx-    │ │(nyx-      │
│stream)  │ │         │ │transport│ │crypto)  │ │telemetry) │
└────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘ └─────┬─────┘
     │           │           │           │            │
     └───────────┴───────────┴───────────┴────────────┘
                         │
                         ▼
            ┌──────────────────────────┐
            │   Core Utilities         │
            │   (nyx-core)             │
            │  - Types                 │
            │  - Config                │
            │  - Error Handling        │
            └──────────────────────────┘

External Services:
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│ Prometheus  │◄────┤OpenTelemetry├────►│   Jaeger    │
│  Metrics    │     │  Collector  │     │  Tracing    │
└─────────────┘     └─────────────┘     └─────────────┘
```

---

## Major Components and Responsibilities

### 1. Application Layer

**Responsibility**: End-user interface

**Components**:
- Web browsers (via SOCKS5/HTTP CONNECT proxy)
- Mobile apps (using nyx-mobile-ffi)
- Desktop apps (using nyx-sdk)
- CLI tools (nyx-cli)

**Interfaces**:
- SOCKS5 protocol (RFC 1928): `localhost:9050`
- HTTP CONNECT proxy: `localhost:8080`
- gRPC API (via nyx-sdk): `localhost:50051`
- JSON-RPC 2.0 (IPC): Unix socket `/tmp/nyx-daemon.sock` or Named pipe `\\.\pipe\nyx-daemon`

---

### 2. SDK Layer (nyx-sdk)

**Responsibility**: High-level API for application developers

**Key Modules**:

#### DaemonClient (`src/client.rs`)
```rust
pub struct DaemonClient {
    endpoint: String,
    channel: Channel, // tonic gRPC channel
    reconnect: bool,
}

// Key methods
impl DaemonClient {
    pub async fn connect(endpoint: &str) -> Result<Self>
    pub async fn get_node_info(&self) -> Result<NodeInfo>
    pub async fn open_stream(&self, peer_id: &str) -> Result<StreamHandle>
    pub async fn close_stream(&self, stream_id: StreamId) -> Result<()>
}
```

#### StreamHandle (`src/stream.rs`)
```rust
pub struct StreamHandle {
    stream_id: StreamId,
    tx: mpsc::Sender<Bytes>,
    rx: mpsc::Receiver<Bytes>,
}

impl StreamHandle {
    pub async fn send(&self, data: Bytes) -> Result<()>
    pub async fn recv(&self) -> Result<Option<Bytes>>
}
```

**Dependencies**:
- `nyx-core`: Type definitions
- `tonic`: gRPC client (Pure Rust, no TLS)
- `tokio`: Async runtime

**Design Patterns**:
- **Builder Pattern**: Client configuration
- **Factory Pattern**: Stream creation
- **Observer Pattern**: Event notification

---

### 3. Control Plane (nyx-daemon)

**Responsibility**: System-wide coordination, API provision, lifecycle management

**Core Structures**:

```rust
struct DaemonState {
    config: Arc<RwLock<Config>>,
    streams: Arc<DashMap<StreamId, StreamState>>,
    peers: Arc<DashMap<PeerId, PeerInfo>>,
    mix_manager: Arc<MixManager>,
    transport: Arc<UdpTransport>,
    telemetry: Arc<TelemetryExporter>,
}
```

**API Specification**:

#### gRPC Service (Pure Rust, no TLS)
```protobuf
service NyxControl {
  rpc GetNodeInfo(Empty) returns (NodeInfoResponse);
  rpc OpenStream(OpenStreamRequest) returns (StreamResponse);
  rpc CloseStream(CloseStreamRequest) returns (Empty);
  rpc ListStreams(Empty) returns (StreamListResponse);
  rpc GetMetrics(Empty) returns (MetricsResponse);
  // ... total 20+ RPCs
}
```

#### JSON-RPC 2.0 (via IPC)
```json
// Request
{
  "jsonrpc": "2.0",
  "id": "req-123",
  "method": "get_info",
  "params": {}
}

// Response
{
  "jsonrpc": "2.0",
  "id": "req-123",
  "result": {
    "node_id": "12D3KooW...",
    "version": "1.0.0",
    "capabilities": ["multipath", "hybrid_pq", "low_power"]
  }
}
```

**Design Choices**:
- Dual support: gRPC (for Rust SDK) and JSON-RPC (for Go proxy, external tools)
- Pure Rust implementation (no ring/OpenSSL dependencies) ensures cross-platform compatibility
- State management using `DashMap` (lock-free concurrent HashMap)

---

### 4. Stream Layer (nyx-stream)

**Responsibility**: Stream lifecycle management, frame processing

**Frame Definition**:

```rust
pub enum Frame {
    Data { stream_id: StreamId, seq: u64, payload: Bytes },
    Ack { stream_id: StreamId, seq: u64 },
    Close { stream_id: StreamId, reason: CloseReason },
    Ping { timestamp: u64 },
    Pong { timestamp: u64 },
}
```

**Flow Control**:
- Window-based flow control (similar to TCP)
- Congestion control (CUBIC-like algorithm)
- Priority queue (0=low, 10=high)

---

### 5. Mix Network Layer (nyx-mix)

**Responsibility**: Anonymity provision through traffic mixing

**Sphinx Onion Encryption**:

```
Client → [Encrypt Layer 3] → Mix1 → [Decrypt Layer 1] 
      → Mix2 → [Decrypt Layer 2] 
      → Mix3 → [Decrypt Layer 3] 
      → Server
```

**Cover Traffic Generation**:
- Poisson distribution (λ=5.0 packets/sec by default)
- Adaptive rate based on real traffic load
- Low Power Mode: 60% reduction (λ=2.0)

**Implementation**: `nyx-mix/src/cover.rs`

```rust
pub struct CoverTrafficGenerator {
    lambda: f32, // packets per second
    low_power: bool,
    rng: ChaCha20Rng,
}

impl CoverTrafficGenerator {
    pub fn next_interval(&mut self) -> Duration {
        let rate = if self.low_power { 
            self.lambda * 0.4 
        } else { 
            self.lambda 
        };
        Duration::from_secs_f32(poisson_sample(rate, &mut self.rng))
    }
}
```

---

### 6. Transport Layer (nyx-transport)

**Responsibility**: Low-level network communication

**QUIC Implementation**:
- UDP datagram-based
- Connection-less (no TCP-style handshake overhead)
- Multipath support (simultaneous use of multiple network paths)

**NAT Traversal**:
- ICE Lite implementation
- STUN for public IP discovery
- Hole punching for firewall traversal

**Implementation**: `nyx-transport/src/udp.rs`

---

### 7. Cryptography Layer (nyx-crypto)

**Responsibility**: All cryptographic operations

**Key Components**:

#### Hybrid Handshake
- ML-KEM-768: Post-quantum KEM (1184-byte public key)
- X25519: Classical ECDH (32-byte public key)
- HKDF: Key derivation (SHA-256 based)

#### Session Encryption
- ChaCha20Poly1305: AEAD cipher
- 32-byte session key (derived from hybrid handshake)
- 12-byte nonce (random + counter)

**Security Properties**:
- Forward secrecy (ephemeral keys)
- Post-quantum security (hybrid approach)
- Authenticated encryption (AEAD)

---

### 8. Telemetry Layer (nyx-telemetry)

**Responsibility**: Observability and monitoring

**Metrics (Prometheus)**:
- `nyx_active_connections`: Current connection count
- `nyx_bytes_sent_total`: Total bytes transmitted
- `nyx_handshake_duration_seconds`: Handshake latency histogram

**Tracing (OpenTelemetry)**:
- Span: Each stream operation
- Trace ID: End-to-end request tracking
- Baggage: Context propagation

**Export Formats**:
- Prometheus: Pull-based HTTP endpoint (`/metrics`)
- OTLP: Push-based gRPC to collector

---

## Data Flow

### Stream Establishment Flow

```
1. Client calls SDK: open_stream(peer_id)
2. SDK → Daemon: gRPC OpenStream request
3. Daemon → Mix Manager: select_path(peer_id)
4. Mix Manager: Choose 3 mix nodes (Mix1, Mix2, Mix3)
5. Daemon → Crypto: hybrid_handshake_init()
6. Crypto: Generate client keypair (ML-KEM + X25519)
7. Daemon → Transport: send_handshake(Mix1, handshake_msg)
8. Mix1 → Mix2 → Mix3 → Server: Forward encrypted layers
9. Server: Decrypt, process, respond
10. Response travels back: Server → Mix3 → Mix2 → Mix1 → Daemon
11. Daemon → SDK: StreamResponse(stream_id)
12. SDK → Client: Return StreamHandle
```

### Data Transmission Flow

```
1. Client: stream.send(data)
2. SDK → Daemon: SendData gRPC
3. Daemon → FEC: encode(data) // Add redundancy
4. FEC → Stream Layer: frame(encoded_data)
5. Stream Layer → Mix Layer: encrypt_onion(frame, path)
6. Mix Layer: Add cover traffic
7. Mix Layer → Transport: send_via_multipath(encrypted_frame)
8. Transport: Send over UDP to Mix1
9. Mix1: Decrypt outer layer, forward to Mix2
10. Mix2: Decrypt middle layer, forward to Mix3
11. Mix3: Decrypt inner layer, forward to Server
12. Server: Receive, send ACK back through reverse path
```

---

## Design Patterns

### 1. Layered Architecture
- Clear separation of concerns
- Each layer only depends on layers below
- Testable in isolation

### 2. Async/Await (Tokio)
- Non-blocking I/O
- Efficient resource utilization
- Scalable to thousands of connections

### 3. Actor Model (Channels)
- Message passing via `tokio::mpsc`
- Shared-nothing concurrency
- Avoid locks where possible

### 4. Type-Driven Design
- Rust's type system enforces invariants
- Compile-time error prevention
- Zero-cost abstractions

---

## External Integration Points

### 1. Prometheus
- **Endpoint**: `http://localhost:9090/metrics`
- **Format**: Prometheus text format
- **Scrape Interval**: 15s (configurable)

### 2. OpenTelemetry Collector
- **Protocol**: OTLP/gRPC
- **Endpoint**: `http://localhost:4317` (configurable)
- **Traces**: Jaeger-compatible
- **Metrics**: Prometheus-compatible export

### 3. gRPC Clients
- **Endpoint**: `localhost:50051`
- **Protocol**: HTTP/2 (no TLS in current version)
- **Auth**: None (localhost binding assumed)

### 4. IPC Clients
- **Unix**: `/tmp/nyx-daemon.sock`
- **Windows**: `\\.\pipe\nyx-daemon`
- **Protocol**: JSON-RPC 2.0 over streams
- **Auth**: File permissions (Unix), Named pipe ACL (Windows)

---

## Scalability Considerations

### Horizontal Scaling
- Stateless design (no sticky sessions required)
- Kubernetes HPA based on CPU/memory/connection count
- Load balancing via Kubernetes Service

### Vertical Scaling
- Multi-threaded Tokio runtime
- Worker threads = CPU cores (configurable)
- Async I/O prevents thread blocking

### Resource Limits
- Max connections: 1000 (default, configurable)
- Max frame size: 8MB (configurable)
- Memory limit: 1GB per daemon instance (configurable)

---

## Fault Tolerance

### Failure Handling

| Component Failure | Detection | Recovery |
|------------------|-----------|----------|
| Mix node down | Health check timeout (30s) | Automatic path reselection |
| Network partition | Connection loss detection | Multipath failover (3s) |
| Daemon crash | Process monitoring (systemd/k8s) | Automatic restart |
| Config error | Validation at startup | Reject invalid config, use defaults |

### Data Integrity
- FEC: Recover from packet loss (up to 30% loss tolerable)
- Checksums: Blake3 hash for integrity verification
- Replay protection: Bloom filter + timestamp nonce

---

## Performance Characteristics

### Latency
- Handshake: ~500ms (3-hop path setup + crypto)
- Data transfer: +150ms overhead vs direct (3 hops × 50ms each)
- Cover traffic: No impact on user latency (separate queue)

### Throughput
- Single stream: ~10 Mbps (limited by mixing overhead)
- Multipath: ~30 Mbps (3 paths × 10 Mbps each)
- Local testing: 100+ Mbps (no network latency)

### Resource Usage
- Memory: 500MB typical, 1GB max
- CPU: 5% idle, 50% under load (per core)
- Network: Cover traffic ~50 Kbps baseline

**Note**: Values are estimates based on typical hardware (推測値)

---

## Security Architecture

### Defense in Depth

```
Layer 1: Transport Security
  - QUIC encryption
  - Perfect Forward Secrecy

Layer 2: Mix Network
  - Sphinx onion routing
  - Traffic analysis resistance

Layer 3: Application Security
  - End-to-end encryption (optional, app-level)
  - User authentication (app-level)
```

### Threat Mitigation

| Threat | Mitigation |
|--------|-----------|
| Passive eavesdropping | Layered encryption (Sphinx) |
| Active MITM | AEAD authentication |
| Traffic analysis | Cover traffic, timing obfuscation |
| Quantum attacks | Hybrid PQ crypto (ML-KEM + X25519) |
| Replay attacks | Timestamp nonce + Bloom filter |

---

## Deployment Architectures

### Single Node (Development)

```
┌──────────────────┐
│   nyx-daemon     │
│   localhost:50051│
└──────────────────┘
```

### Multi-Node (Production)

```
┌─────────┐     ┌─────────┐     ┌─────────┐
│ Client  │────→│  Mix 1  │────→│  Mix 2  │
└─────────┘     └─────────┘     └─────────┘
                                      │
                                      ▼
                                ┌─────────┐
                                │  Mix 3  │
                                └─────────┘
                                      │
                                      ▼
                                ┌─────────┐
                                │  Server │
                                └─────────┘
```

### Kubernetes (Cloud)

```
┌──────────────────────────────────────┐
│         Ingress Controller           │
└──────────────────────────────────────┘
                  │
                  ▼
┌──────────────────────────────────────┐
│         nyx-daemon Service           │
│         (LoadBalancer)                │
└──────────────────────────────────────┘
     │              │              │
     ▼              ▼              ▼
┌────────┐    ┌────────┐    ┌────────┐
│ Pod 1  │    │ Pod 2  │    │ Pod 3  │
│ daemon │    │ daemon │    │ daemon │
└────────┘    └────────┘    └────────┘
```

---

## Configuration Management

### Configuration Hierarchy

```
1. Default values (compiled-in)
2. Config file (nyx.toml)
3. Environment variables (NYX_*)
4. Command-line flags
```

Higher levels override lower levels.

### Hot Reload

Supported for:
- Log level
- Rate limits
- Cover traffic parameters

Not supported for (requires restart):
- Bind address
- Cryptographic parameters

---

## Disclaimer: Inferred Content

The following information is reasonably inferred from code and standard practices:

- **Some performance numbers**: Estimated from typical hardware configurations
- **Deployment architecture details**: Standard patterns, not project-specific
- **Resource usage values**: Approximations based on similar systems

For precise information, refer to actual code and run benchmarks in your environment.
