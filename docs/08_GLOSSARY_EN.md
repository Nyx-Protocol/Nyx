# NyxNet Glossary

**Last Updated**: October 7, 2025  
**Target Version**: v1.0

[日本語版](./08_GLOSSARY.md)

---

## Overview

Definitions of technical terms, acronyms, and concepts used in the NyxNet project. Organized alphabetically and by category.

---

## Alphabetical Index

### A

#### AEAD (Authenticated Encryption with Associated Data)
**Category**: Cryptography  
**Description**: Encryption mode providing both confidentiality and authenticity. NyxNet uses `ChaCha20Poly1305`. Detects tampering.

#### ASan (Address Sanitizer)
**Category**: Testing  
**Description**: Dynamic analysis tool detecting memory errors (buffer overflows, use-after-free, etc.).

#### Actor Model
**Category**: Architecture  
**Description**: Concurrency model where actors communicate via message passing. Used in NyxNet via Tokio channels.

---

### B

#### BIKE (Bit Flipping Key Encapsulation)
**Category**: Cryptography  
**Description**: Post-quantum cryptography candidate (QC-MDPC code-based). Not recommended in NyxNet (use ML-KEM instead).

#### Bloom Filter
**Category**: Data Structure  
**Description**: Probabilistic data structure for set membership testing. Used for replay attack detection. False positives possible (no false negatives).

---

### C

#### CBOR (Concise Binary Object Representation)
**Category**: Serialization  
**Description**: Binary data serialization format. More efficient than JSON. Used in plugin system.

#### ChaCha20Poly1305
**Category**: Cryptography  
**Description**: AEAD cipher algorithm. ChaCha20 (stream cipher) + Poly1305 (MAC). Fast software implementation.

#### cMix
**Category**: Mix Network  
**Description**: Mix network protocol based on VDF (Verifiable Delay Function). Achieves high throughput through batch processing.

#### Cover Traffic
**Category**: Privacy  
**Description**: Dummy traffic sent to resist traffic analysis. Indistinguishable from real traffic. Generated using Poisson distribution.

#### Criterion
**Category**: Benchmarking  
**Description**: Rust benchmarking framework. Statistical analysis, HTML report generation.

---

### D

#### DashMap
**Category**: Data Structure  
**Description**: Concurrent HashMap. Lock-free design for high performance.

#### DHT (Distributed Hash Table)
**Category**: Networking  
**Description**: Peer discovery in P2P networks. NyxNet implements Kademlia DHT.

---

### E

#### ECDH (Elliptic Curve Diffie-Hellman)
**Category**: Cryptography  
**Description**: Key exchange protocol using elliptic curve cryptography. NyxNet uses X25519.

#### Ed25519
**Category**: Cryptography  
**Description**: Digital signature algorithm using Curve25519. Fast, small signatures (64 bytes).

---

### F

#### FEC (Forward Error Correction)
**Category**: Networking  
**Description**: Add redundancy before transmission to enable packet loss recovery. Uses Reed-Solomon codes.

#### FFI (Foreign Function Interface)
**Category**: Programming  
**Description**: Interface for calling functions across programming languages. C-ABI compatible FFI provided for mobile apps.

---

### G

#### gRPC
**Category**: RPC  
**Description**: RPC framework developed by Google. Uses Protocol Buffers. NyxNet uses pure Rust implementation (no TLS).

---

### H

#### HKDF (HMAC-based Key Derivation Function)
**Category**: Cryptography  
**Description**: Cryptographically secure key derivation from shared secrets. RFC 5869 compliant.

#### HPA (Horizontal Pod Autoscaler)
**Category**: Kubernetes  
**Description**: Kubernetes feature. Automatically adjusts pod count based on load.

#### Hybrid Handshake
**Category**: Cryptography  
**Description**: Post-quantum + classical key exchange. NyxNet combines ML-KEM-768 and X25519.

---

### I

#### ICE (Interactive Connectivity Establishment)
**Category**: Networking  
**Description**: Protocol for NAT traversal. NyxNet implements ICE Lite.

---

### J

#### JSON-RPC
**Category**: RPC  
**Description**: RPC protocol using JSON format. Used for CLI-daemon communication (via IPC).

---

### K

#### Kademlia
**Category**: P2P  
**Description**: Distributed hash table protocol. Efficient peer discovery using XOR metric.

#### KDF (Key Derivation Function)
**Category**: Cryptography  
**Description**: Function to generate cryptographic keys from passwords or shared secrets. Examples: HKDF.

#### KEM (Key Encapsulation Mechanism)
**Category**: Cryptography  
**Description**: Public-key encryption scheme for key exchange. ML-KEM is NIST-standardized post-quantum KEM.

---

### L

#### LARMix
**Category**: Mix Network  
**Description**: Latency-Aware Routing for Mix networks. Selects paths based on measured latency.

#### Latency
**Category**: Performance  
**Description**: Time delay from transmission to reception. NyxNet target: <200ms (3-hop mix network).

---

### M

#### ML-KEM (Module-Lattice-based Key Encapsulation Mechanism)
**Category**: Cryptography  
**Description**: NIST-standardized post-quantum KEM (FIPS 203). Based on lattice cryptography. NyxNet uses ML-KEM-768.

#### Mix Network
**Category**: Privacy  
**Description**: Network providing anonymity through layered encryption (onion routing). NyxNet uses Sphinx protocol.

#### Multipath
**Category**: Networking  
**Description**: Use multiple network paths simultaneously. Provides redundancy and load balancing.

---

### N

#### NAT (Network Address Translation)
**Category**: Networking  
**Description**: IP address translation. Creates connectivity challenges. NyxNet uses ICE for NAT traversal.

#### Nonce
**Category**: Cryptography  
**Description**: Number used once. Prevents replay attacks. NyxNet uses timestamp-based nonces.

---

### O

#### Onion Routing
**Category**: Privacy  
**Description**: Layered encryption where each hop decrypts one layer. Used in Tor and NyxNet (Sphinx protocol).

#### OTLP (OpenTelemetry Protocol)
**Category**: Observability  
**Description**: Standard protocol for telemetry data (traces, metrics, logs). gRPC-based.

---

### P

#### Poly1305
**Category**: Cryptography  
**Description**: Message authentication code (MAC). Used with ChaCha20 in AEAD mode.

#### Post-Quantum Cryptography (PQC)
**Category**: Cryptography  
**Description**: Cryptography resistant to quantum computer attacks. NyxNet uses ML-KEM-768.

#### Proptest
**Category**: Testing  
**Description**: Property-based testing framework for Rust. Generates random test cases.

---

### Q

#### QUIC
**Category**: Networking  
**Description**: Modern transport protocol (UDP-based). Low latency, built-in encryption, multiplexing.

---

### R

#### Reed-Solomon
**Category**: Error Correction  
**Description**: Forward error correction code. Used in NyxNet FEC implementation.

#### Relay
**Category**: Mix Network  
**Description**: Intermediate node in mix network. Forwards packets without knowing sender/receiver.

#### RTT (Round-Trip Time)
**Category**: Performance  
**Description**: Time for packet to travel to destination and back. Used for path selection.

---

### S

#### SOCKS5
**Category**: Proxy  
**Description**: Proxy protocol (RFC 1928). NyxNet provides SOCKS5 server for application integration.

#### Sphinx
**Category**: Mix Network  
**Description**: Compact and provably secure onion routing protocol. Used in NyxNet mix network.

#### Stream
**Category**: Networking  
**Description**: Bidirectional data flow channel. NyxNet provides stream abstraction over mix network.

---

### T

#### TLA+ (Temporal Logic of Actions)
**Category**: Formal Verification  
**Description**: Specification language for formal verification. NyxNet uses TLA+ to verify protocol correctness.

#### Tokio
**Category**: Async Runtime  
**Description**: Asynchronous runtime for Rust. Provides async/await, timers, networking.

#### Tonic
**Category**: gRPC  
**Description**: Pure Rust gRPC framework. Used in NyxNet control plane.

---

### W

#### WASM (WebAssembly)
**Category**: Compilation Target  
**Description**: Binary instruction format for web. NyxNet provides WASM SDK for browser integration.

---

### X

#### X25519
**Category**: Cryptography  
**Description**: Elliptic curve Diffie-Hellman key exchange using Curve25519. Fast, constant-time implementation.

---

### Z

#### Zeroization
**Category**: Security  
**Description**: Securely erase sensitive data from memory. NyxNet uses `zeroize` crate for automatic key cleanup.

---

## Acronym Reference

| Acronym | Full Name | Category |
|---------|-----------|----------|
| AEAD | Authenticated Encryption with Associated Data | Cryptography |
| ASan | Address Sanitizer | Testing |
| CBOR | Concise Binary Object Representation | Serialization |
| CVE | Common Vulnerabilities and Exposures | Security |
| DHT | Distributed Hash Table | Networking |
| DoS | Denial of Service | Security |
| ECDH | Elliptic Curve Diffie-Hellman | Cryptography |
| FEC | Forward Error Correction | Networking |
| FFI | Foreign Function Interface | Programming |
| FIPS | Federal Information Processing Standards | Compliance |
| gRPC | gRPC Remote Procedure Call | RPC |
| HKDF | HMAC-based Key Derivation Function | Cryptography |
| HMAC | Hash-based Message Authentication Code | Cryptography |
| HPA | Horizontal Pod Autoscaler | Kubernetes |
| HTTP | Hypertext Transfer Protocol | Networking |
| ICE | Interactive Connectivity Establishment | Networking |
| IPC | Inter-Process Communication | Operating System |
| JSON | JavaScript Object Notation | Serialization |
| KDF | Key Derivation Function | Cryptography |
| KEM | Key Encapsulation Mechanism | Cryptography |
| MAC | Message Authentication Code | Cryptography |
| ML-KEM | Module-Lattice-based KEM | Cryptography |
| NAT | Network Address Translation | Networking |
| NIST | National Institute of Standards and Technology | Standards |
| OTLP | OpenTelemetry Protocol | Observability |
| P2P | Peer-to-Peer | Networking |
| PII | Personally Identifiable Information | Privacy |
| PQC | Post-Quantum Cryptography | Cryptography |
| QUIC | Quick UDP Internet Connections | Networking |
| RFC | Request for Comments | Standards |
| RPC | Remote Procedure Call | Networking |
| RTT | Round-Trip Time | Performance |
| SDK | Software Development Kit | Development |
| SOCKS | Socket Secure | Proxy |
| TCP | Transmission Control Protocol | Networking |
| TLA+ | Temporal Logic of Actions | Formal Verification |
| TLS | Transport Layer Security | Security |
| UDP | User Datagram Protocol | Networking |
| VDF | Verifiable Delay Function | Cryptography |
| WASM | WebAssembly | Compilation |

---

## Compliance Levels

### Core
**Description**: Minimum feature set for basic NyxNet functionality.

**Required Features**:
- Hybrid post-quantum handshake (ML-KEM-768 + X25519)
- Basic stream establishment
- 3-hop Sphinx onion routing
- Essential security (replay protection, AEAD encryption)

**Use Case**: Privacy-conscious users, basic anonymity requirements.

---

### Plus
**Description**: Enhanced features for production use.

**Additional Features**:
- Multipath QUIC transport
- Prometheus metrics + OpenTelemetry tracing
- Cover traffic generation
- Advanced routing (LARMix)

**Use Case**: Enterprise deployments, high-availability requirements.

---

### Full
**Description**: Complete feature set with all extensions.

**Additional Features**:
- Plugin framework (CBOR-based protocol extension)
- Formal verification (TLA+ specs)
- Mobile optimization (low power mode)
- Advanced telemetry and diagnostics

**Use Case**: Research, maximum flexibility, cutting-edge features.

---

## Network Topology Terms

### Node Types

#### Mix Node
**Description**: Intermediate relay in the mix network. Performs onion layer unwrapping.

#### Entry Node
**Description**: First hop in anonymity path. Knows client's IP but not destination.

#### Exit Node
**Description**: Last hop in anonymity path. Knows destination but not client's IP.

#### Guard Node
**Description**: Trusted entry node used consistently to prevent certain attacks.

---

## Performance Metrics

### Throughput
**Description**: Data transfer rate (bytes/second or packets/second).  
**NyxNet Target**: 10+ Mbps per stream.

### Latency
**Description**: End-to-end delay.  
**NyxNet Target**: <200ms (3-hop mix network).

### Packet Loss
**Description**: Percentage of packets lost in transmission.  
**NyxNet Target**: <1% (with FEC enabled).

### Jitter
**Description**: Variation in packet arrival times.  
**NyxNet Target**: <50ms (standard deviation).

---

## Cryptographic Terms

### Shared Secret
**Description**: Secret value known only to communicating parties. Derived from key exchange.

### Ephemeral Key
**Description**: Temporary key used for single session. Provides forward secrecy.

### Forward Secrecy
**Description**: Property where compromise of long-term keys doesn't compromise past sessions.

### Traffic Keys
**Description**: Symmetric keys used to encrypt actual data. Derived from shared secret via HKDF.

### Nonce
**Description**: Number used once. Prevents replay attacks. In NyxNet: timestamp + random bytes.

---

## Development Terms

### Crate
**Description**: Rust package. NyxNet has 16 crates in workspace.

### Workspace
**Description**: Collection of related Rust crates. Shared dependencies and build configuration.

### Feature Flag
**Description**: Conditional compilation flag. Enables optional functionality (e.g., `hybrid`, `multipath`).

### LTO (Link-Time Optimization)
**Description**: Compiler optimization across compilation units. Enabled in release profile.

### Clippy
**Description**: Rust linter. Enforces code quality and idioms.

---

## Testing Terms

### Unit Test
**Description**: Test for single function or module. Fast, isolated.

### Integration Test
**Description**: Test for interaction between multiple modules.

### Property-Based Test
**Description**: Test that verifies properties hold for random inputs. Uses Proptest framework.

### End-to-End Test (E2E)
**Description**: Test of complete system in production-like environment.

### Fuzzing
**Description**: Automated testing with malformed/random inputs to find crashes.

### Coverage
**Description**: Percentage of code executed by tests. NyxNet target: 80%+.

---

## Deployment Terms

### Container
**Description**: Lightweight, isolated application package. NyxNet provides Docker images.

### Pod
**Description**: Kubernetes unit of deployment. Can contain multiple containers.

### Helm Chart
**Description**: Kubernetes package manager format. NyxNet provides Helm chart for easy deployment.

### StatefulSet
**Description**: Kubernetes controller for stateful applications. Used for persistent node identity.

---

## Protocol Terms

### Frame
**Description**: Unit of data in stream protocol. Header + payload.

### Session
**Description**: Established cryptographic context between two parties. Has shared keys.

### Path
**Description**: Sequence of nodes through mix network. Minimum 3 hops.

### Circuit
**Description**: Established path through mix network with negotiated keys at each hop.

---

## Compliance and Standards

### FIPS (Federal Information Processing Standards)
**Description**: US government cryptographic standards. NyxNet aims for FIPS 140-3 Level 1.

### NIST (National Institute of Standards and Technology)
**Description**: US standards organization. Standardized ML-KEM as FIPS 203.

### RFC (Request for Comments)
**Description**: Internet standards documents. NyxNet implements multiple RFCs (SOCKS5, HKDF, etc.).

### GDPR (General Data Protection Regulation)
**Description**: EU privacy regulation. NyxNet collects no PII by default.

---

## Comparison Table: Mix Networks

| Feature | Tor | I2P | NyxNet |
|---------|-----|-----|--------|
| **Routing Protocol** | Onion (custom) | Garlic | Sphinx |
| **Post-Quantum** | ❌ | ❌ | ✅ (ML-KEM-768) |
| **Multipath** | ❌ | Partial | ✅ |
| **Cover Traffic** | Partial | ✅ | ✅ (Poisson) |
| **Programming Language** | C, Python | Java | Rust, Go |
| **Memory Safety** | ❌ (C) | ✅ (Java) | ✅ (Rust) |
| **Mobile Optimized** | Partial | ❌ | ✅ |

---

## Comparison Table: Key Exchange Protocols

| Protocol | Security | Key Size | Performance | PQ Secure |
|----------|----------|----------|-------------|-----------|
| **RSA-2048** | Classical | 2048-bit | Slow | ❌ |
| **ECDH (X25519)** | Classical | 256-bit | Fast | ❌ |
| **ML-KEM-768** | Post-Quantum | 768-bit | Medium | ✅ |
| **Hybrid (ML-KEM + X25519)** | Both | 1024-bit | Medium | ✅ |

---

## Comparison Table: AEAD Ciphers

| Cipher | Block Size | Key Size | Speed (Software) | HW Acceleration |
|--------|------------|----------|------------------|-----------------|
| **AES-GCM** | 128-bit | 128/256-bit | Medium | ✅ (AES-NI) |
| **ChaCha20Poly1305** | N/A (stream) | 256-bit | Fast | ❌ |
| **XChaCha20Poly1305** | N/A (stream) | 256-bit | Fast | ❌ |

NyxNet uses **ChaCha20Poly1305** for fast software performance without hardware requirements.

---

## Disclaimer: Inferred Content

The following information is reasonably inferred from common usage and best practices:

- **Performance targets**: Based on typical network conditions
- **Security properties**: Standard interpretations of cryptographic guarantees
- **Comparison tables**: Based on publicly available information about other systems

For precise definitions, consult the respective protocol specifications and RFCs.
