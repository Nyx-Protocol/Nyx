# NyxNet Major Features Documentation

**Last Updated**: October 7, 2025  
**Target Version**: v1.0

[日本語版](./03_MAJOR_FEATURES.md)

---

## Feature 1: Hybrid Post-Quantum Handshake

### Purpose and Use Cases

Secure communication against quantum computing threats. Current ECDH-based key exchange can be broken by quantum computers running Shor's algorithm. NyxNet uses hybrid cryptography combining NIST-standardized ML-KEM-768 and X25519 to guarantee both quantum resistance and current security.

**Use Cases**:
- Long-term confidential communications (medical records, financial transactions)
- Government and military communications
- Enterprise communications with future quantum threats in mind

### Related Files and Modules

**Core Files**:
- `nyx-crypto/src/hybrid_handshake.rs` (801 lines): Hybrid handshake implementation
- `nyx-crypto/src/kdf.rs`: HKDF key derivation function
- `nyx-crypto/src/session.rs`: Session key management

**Dependency Crates**:
- `ml-kem` 0.2: ML-KEM-768 implementation (Pure Rust)
- `x25519-dalek` 2.0: X25519 implementation
- `hkdf` 0.12: HMAC-based KDF

**Tests**:
- `nyx-crypto/tests/hybrid_handshake_tests.rs`
- `nyx-conformance/tests/crypto_compliance.rs`

### Core Logic

#### Step 1: Client Initialization

```rust
pub fn client_init() -> Result<(HybridPublicKey, HybridKeyPair)> {
    // 1. Generate ML-KEM-768 keypair (lattice cryptography)
    let (kyber_pk, kyber_sk) = ml_kem::MlKem768::generate(&mut OsRng);
    
    // 2. Generate X25519 keypair (elliptic curve)
    let x25519_sk = EphemeralSecret::random_from_rng(&mut OsRng);
    let x25519_pk = x25519_dalek::PublicKey::from(&x25519_sk);
    
    // 3. Combine public keys (1184 + 32 = 1216 bytes)
    let public = HybridPublicKey {
        kyber: kyber_pk.into_bytes(),    // 1184 bytes
        x25519: x25519_pk.to_bytes(),    // 32 bytes
    };
    
    let keypair = HybridKeyPair { kyber_sk, x25519_sk };
    Ok((public, keypair))
}
```

**Details**:
- `OsRng`: OS-provided cryptographic RNG (uses `getrandom` syscall)
- `EphemeralSecret`: Ephemeral key (ensures forward secrecy)
- Key sizes: ML-KEM-768 public key 1184 bytes + X25519 public key 32 bytes = 1216 bytes

#### Step 2: Server Encapsulation

```rust
pub fn server_encapsulate(client_pk: &HybridPublicKey) 
    -> Result<(HybridCiphertext, SharedSecret)> {
    
    // 1. ML-KEM encapsulation (encrypt random shared secret)
    let kyber_pk = MlKem768EncapsulationKey::from_bytes(&client_pk.kyber)?;
    let (ct_kyber, ss_kyber) = kyber_pk.encapsulate(&mut OsRng)?;
    // ct_kyber: 1088 bytes (ciphertext)
    // ss_kyber: 32 bytes (shared secret)
    
    // 2. X25519 key exchange
    let server_sk = EphemeralSecret::random_from_rng(&mut OsRng);
    let server_pk = x25519_dalek::PublicKey::from(&server_sk);
    let client_x25519_pk = x25519_dalek::PublicKey::from(client_pk.x25519);
    let ss_x25519 = server_sk.diffie_hellman(&client_x25519_pk);
    // ss_x25519: 32 bytes (shared secret)
    
    // 3. Combine shared secrets with HKDF
    let shared = Self::derive_key(&ss_kyber, &ss_x25519)?;
    
    let ciphertext = HybridCiphertext { 
        ct_kyber,     // 1088 bytes
        server_pk,    // 32 bytes
    };
    Ok((ciphertext, shared))
}
```

**Details**:
- **ML-KEM Encapsulation**: Encrypt 32-byte random secret with public key
- **X25519 DH**: DH calculation with server's ephemeral secret key and client public key
- Returned ciphertext size: 1088 + 32 = 1120 bytes

#### Step 3: Key Derivation (HKDF)

```rust
fn derive_key(ss_kyber: &[u8], ss_x25519: &[u8]) -> Result<SharedSecret> {
    // 1. Concatenate shared secrets (64 bytes)
    let mut combined = Vec::with_capacity(64);
    combined.extend_from_slice(ss_kyber);      // 32 bytes
    combined.extend_from_slice(ss_x25519.as_bytes()); // 32 bytes
    
    // 2. HKDF-Extract (SHA-256)
    let hkdf = Hkdf::<Sha256>::new(None, &combined);
    
    // 3. HKDF-Expand (with context info)
    let mut output = [0u8; 32];
    hkdf.expand(b"nyx-hybrid-v1", &mut output)
        .map_err(|_| Error::Crypto("HKDF expand failed".into()))?;
    
    // 4. Wrap as secure memory
    Ok(SharedSecret::from_bytes(output))
}
```

**HKDF Process**:
```
IKM (Input Key Material) = ss_kyber || ss_x25519 (64 bytes)
Salt = None (all-zero salt)
Info = "nyx-hybrid-v1" (protocol identifier)

PRK = HMAC-SHA256(Salt, IKM)
OKM = HMAC-SHA256(PRK, Info || 0x01)
Output = OKM[0..32]
```

### Data Model

#### Public Key Structure

```rust
pub struct HybridPublicKey {
    pub kyber: [u8; KYBER_PUBLIC_KEY_SIZE],   // 1184 bytes
    pub x25519: [u8; X25519_PUBLIC_KEY_SIZE], // 32 bytes
}

impl HybridPublicKey {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(HYBRID_PUBLIC_KEY_SIZE);
        bytes.extend_from_slice(&self.kyber);
        bytes.extend_from_slice(&self.x25519);
        bytes
    }
}
```

#### Secret Key (with Zeroization)

```rust
#[derive(ZeroizeOnDrop)]
pub struct HybridKeyPair {
    kyber_sk: [u8; KYBER_SECRET_KEY_SIZE],    // 2400 bytes
    x25519_sk: EphemeralSecret,                // 32 bytes
}

// Automatically zeroizes memory on drop (using zeroize crate)
```

### Error Handling

```rust
pub enum Error {
    InvalidKey(String),      // Invalid public key format
    EncapFailed(String),     // Encapsulation failed
    DecapFailed(String),     // Decapsulation failed
    KdfFailed(String),       // Key derivation failed
    Crypto(String),          // General crypto error
}
```

### Testing

#### Unit Test Example

```rust
#[test]
fn test_hybrid_handshake_roundtrip() -> Result<()> {
    // Client generates keypair
    let (client_pk, client_kp) = client_init()?;
    
    // Server encapsulates
    let (ct, ss_server) = server_encapsulate(&client_pk)?;
    
    // Client decapsulates
    let ss_client = client_decapsulate(&client_kp, &ct)?;
    
    // Shared secrets must match
    assert_eq!(ss_server.as_bytes(), ss_client.as_bytes());
    Ok(())
}
```

#### Property-Based Test

```rust
proptest! {
    #[test]
    fn prop_handshake_always_succeeds(seed in any::<u64>()) {
        let mut rng = ChaCha20Rng::seed_from_u64(seed);
        let (pk, kp) = client_init_with_rng(&mut rng)?;
        let (ct, ss_s) = server_encapsulate_with_rng(&pk, &mut rng)?;
        let ss_c = client_decapsulate(&kp, &ct)?;
        prop_assert_eq!(ss_s.as_bytes(), ss_c.as_bytes());
    }
}
```

---

## Feature 2: Sphinx Onion Routing

### Purpose and Use Cases

Anonymize traffic through 3-hop mix network. Prevents any single node from knowing both sender and receiver, providing strong anonymity guarantees.

**Use Cases**:
- Anonymous browsing
- Whistleblowing platforms
- Privacy-sensitive communications
- Avoiding censorship

### Related Files and Modules

**Core Files**:
- `nyx-mix/src/sphinx.rs` (650 lines): Sphinx protocol implementation
- `nyx-mix/src/cover.rs`: Cover traffic generation
- `nyx-mix/src/larmix.rs`: Latency-aware routing

**Dependencies**:
- `nyx-crypto`: Cryptographic primitives
- `nyx-transport`: Network communication

### Core Logic

#### Sphinx Packet Structure

```
┌────────────────────────────────────────────┐
│ Header (α)                                 │
│  - Version (1 byte)                        │
│  - Group Element (32 bytes)                │
│  - Routing Info (per-hop: 32 bytes × 3)   │
│  - MAC (16 bytes)                          │
├────────────────────────────────────────────┤
│ Payload (β)                                │
│  - Encrypted message (variable length)    │
└────────────────────────────────────────────┘
```

#### Path Selection Algorithm

```rust
pub fn select_path(dest: NodeId) -> Result<Vec<NodeId>> {
    let mut path = Vec::with_capacity(3);
    let mut excluded = HashSet::new();
    
    // Select 3 diverse mix nodes
    for hop in 0..3 {
        let node = select_diverse_node(&excluded)?;
        path.push(node);
        excluded.insert(node);
    }
    
    path.push(dest); // Final destination
    Ok(path)
}

fn select_diverse_node(excluded: &HashSet<NodeId>) -> Result<NodeId> {
    // Diversity criteria:
    // 1. Different geographic regions
    // 2. Different operators
    // 3. Different AS numbers
    // 4. Good performance history
    
    let candidates = get_available_nodes()
        .filter(|n| !excluded.contains(n))
        .filter(|n| n.is_reliable())
        .collect::<Vec<_>>();
    
    candidates
        .choose(&mut thread_rng())
        .cloned()
        .ok_or(Error::NoNodesAvailable)
}
```

### Performance Characteristics

| Metric | Value |
|--------|-------|
| Latency overhead | +150ms (3 hops × 50ms each) |
| Throughput | ~10 Mbps per stream |
| Anonymity set size | 1000+ concurrent users |
| Packet overhead | ~200 bytes (headers) |

**Note**: Values are estimates (推測値)

---

## Feature 3: Multipath QUIC Transport

### Purpose and Use Cases

Resilient, high-throughput communication using multiple network paths simultaneously. Provides automatic failover and load balancing.

**Use Cases**:
- Mobile devices (WiFi + Cellular)
- Unreliable networks (poor connectivity)
- High-throughput applications (file transfer)
- Mission-critical communications

### Related Files and Modules

**Core Files**:
- `nyx-transport/src/multipath.rs` (420 lines): Multipath routing logic
- `nyx-transport/src/udp.rs`: UDP implementation
- `nyx-transport/src/nat.rs`: NAT traversal

### Core Logic

#### Path Management

```rust
pub struct MultipathManager {
    paths: Vec<Path>,
    scheduler: PathScheduler,
    max_paths: usize,
}

pub struct Path {
    id: PathId,
    local_addr: SocketAddr,
    remote_addr: SocketAddr,
    state: PathState,
    rtt: Duration,
    loss_rate: f32,
    last_used: Instant,
}

impl MultipathManager {
    pub fn select_path(&self) -> Option<PathId> {
        // Select path based on:
        // 1. Path state (active/backup)
        // 2. RTT (prefer lower)
        // 3. Loss rate (prefer lower)
        // 4. Recent usage (load balancing)
        
        self.paths.iter()
            .filter(|p| p.state == PathState::Active)
            .min_by_key(|p| (p.rtt, (p.loss_rate * 1000.0) as u32))
            .map(|p| p.id)
    }
}
```

#### Packet Distribution Strategy

```rust
pub enum SchedulingPolicy {
    RoundRobin,        // Distribute evenly
    LowLatency,        // Prefer lowest RTT
    HighThroughput,    // Use all paths simultaneously
    RedundantSend,     // Send on multiple paths (FEC)
}
```

### Failover Mechanism

```
Path 1 (Primary): ──────●──────────────────────
                        │ (failure detected)
                        │
Path 2 (Backup):  ──────────────●──────────────
                                │ (3s failover)
                                └→ Now Primary
```

**Failover Time**: < 3 seconds (target)

---

## Additional Features (Brief)

### Feature 4: Forward Error Correction (FEC)

**Purpose**: Recover from packet loss without retransmission

**Algorithm**: Reed-Solomon codes  
**Redundancy**: 10-30% (adaptive based on network conditions)  
**Recovery**: Up to 30% packet loss tolerable

### Feature 5: Cover Traffic

**Purpose**: Resist traffic analysis attacks

**Generation**: Poisson distribution (λ=5.0 pps default)  
**Adaptation**: Increases with real traffic load  
**Low Power Mode**: 60% reduction (λ=2.0 pps)

### Feature 6: Low Power Mode

**Purpose**: Battery optimization for mobile devices

**Power Savings**:
- Reduce cover traffic (60% reduction)
- Increase sleep intervals (2x longer)
- Defer non-critical operations

**Trade-offs**:
- Slightly reduced anonymity (still acceptable for most use cases)
- Increased latency (+50ms)

---

## Feature Comparison Matrix

| Feature | Tor | VPN | NyxNet |
|---------|-----|-----|--------|
| Post-Quantum Crypto | ❌ | ❌ | ✅ |
| Onion Routing | ✅ | ❌ | ✅ |
| Multipath | ❌ | Partial | ✅ |
| Cover Traffic | Partial | ❌ | ✅ |
| Mobile Optimized | ❌ | ✅ | ✅ |
| Open Source | ✅ | Varies | ✅ |

---

## Disclaimer: Inferred Content

The following information is reasonably inferred from code and typical system behavior:

- **Performance numbers**: Estimated from typical network conditions
- **Anonymity set size**: Projected from similar systems
- **Failover timing**: Target value, actual may vary

For precise measurements, run benchmarks in your specific environment.
