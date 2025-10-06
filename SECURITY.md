# Security Policy

## Reporting Security Issues

- **Please report vulnerabilities privately** via GitHub Security Advisories
- **Do not open public issues** for security reports
- **Do not disclose security vulnerabilities publicly** until they are fixed
- We aim to acknowledge reports within 24 hours and provide a timeline for fixes
- **Critical vulnerabilities** will be addressed within 48 hours
- **High-severity issues** will be patched within 7 days

## Supported Versions

| Version | Supported | Notes |
|---------|-----------|-------|
| Latest main branch | ✅ | Full security support |
| Pre-release versions | ⚠️ | Limited support |
| All others | ❌ | Upgrade required |

## Security Architecture

### Zero-Trust Design Principles
- **Principle of Least Privilege**: Minimal required permissions
- **Defense in Depth**: Multiple security layers
- **Secure by Default**: Conservative default configurations
- **Fail Securely**: Graceful degradation under attack

## Security Features

### Cryptographic Security
- **Post-Quantum Ready**: Hybrid X25519 + ML-KEM (Kyber) NIST-standardized algorithms
- **AEAD Encryption**: ChaCha20-Poly1305 for authenticated encryption with associated data
- **Perfect Forward Secrecy**: HKDF-based key derivation ensures past communications remain secure
- **Anti-Replay Protection**: Temporal and sequence-based replay attack prevention
- **Key Rotation**: Automatic cryptographic key rotation with configurable intervals
- **Secure Random**: Hardware-backed entropy sources for all cryptographic operations

### Network Security
- **Traffic Analysis Resistance**: Adaptive cover traffic and sophisticated padding schemes
- **Metadata Protection**: Header obfuscation and timing randomization
- **Connection Security**: Noise Protocol Framework providing TLS 1.3+ equivalent security
- **Path Diversity**: Multiple transport paths to prevent single points of failure
- **Rate Limiting**: Sophisticated DDoS protection and traffic shaping
- **Authenticated Encryption**: All network communications are authenticated and encrypted

### Implementation Security
- **Memory Safety**: Rust's ownership system prevents buffer overflows, use-after-free, and double-free vulnerabilities
- **Zero Unsafe Code**: Complete avoidance of unsafe Rust code across the entire codebase
- **Constant-Time Cryptography**: All cryptographic operations use constant-time algorithms to prevent timing attacks
- **Secure Memory Management**: Sensitive data is zeroized immediately after use using compiler-enforced techniques
- **Stack Protection**: Compiler-enforced stack canaries and control flow integrity
- **ASLR/PIE**: Position-independent executables with address space layout randomization
- **Sandboxing**: Plugin system isolation using OS-level sandboxing (seccomp, capabilities, job objects)

### Supply Chain Security
- **Dependency Scanning**: Automated vulnerability scanning of all dependencies
- **Minimal Dependencies**: Reduced attack surface through careful dependency selection
- **Reproducible Builds**: Deterministic build process for verification
- **Code Signing**: All releases are cryptographically signed
- **SBOM Generation**: Software Bill of Materials for transparency

## Security Testing

### Automated Security Testing
- **Static Analysis**: Clippy with security-focused lints
- **Dependency Auditing**: `cargo audit` in CI/CD pipeline
- **Fuzz Testing**: Continuous fuzzing of critical parsing and cryptographic code
- **Property-Based Testing**: Formal verification of security properties
- **Coverage Analysis**: Security-critical code paths have 100% test coverage

### Manual Security Review
- **Threat Modeling**: Regular threat model updates and reviews
- **Code Review**: Security-focused code review process
- **Penetration Testing**: Regular external security assessments
- **Cryptographic Review**: Expert review of all cryptographic implementations

## Security Best Practices

### For Developers
- **Always use the latest stable Rust compiler** with all security patches
- **Enable security compiler flags**: `-Z sanitizer=address`, `-Z sanitizer=memory`
- **Review code for timing attacks** and side-channel vulnerabilities
- **Implement proper error handling** without information leakage
- **Use security-focused development practices**: secure coding guidelines, threat modeling
- **Validate all inputs** at trust boundaries
- **Follow principle of least privilege** in all system interactions

### For Operators
- **Network Security**: Run Nyx behind a firewall with proper network segmentation
- **Authentication**: Use strong, randomly generated authentication tokens (minimum 256-bit entropy)
- **System Updates**: Keep all systems updated with latest security patches
- **Monitoring**: Implement comprehensive logging and monitoring for suspicious activity
- **TLS Termination**: Use TLS termination proxies when exposing services
- **Resource Limits**: Configure appropriate resource limits to prevent DoS attacks
- **Backup Security**: Encrypt all backups and store them securely
## Incident Response

<!--
	NyxNet SECURITY.md
	High-level threat model, cryptographic rationale, lifecycle policy, and hardening roadmap.
	IMPORTANT: Keep this file stable; external users and auditors may deep link to sections.
-->

# NyxNet Security Overview

> Living document: threat model, key lifecycle, defensive controls & roadmap. Pure Rust & **no unsafe** guarantee across critical crates.

## 1. Threat Model
| Actor | Capabilities | Goals | In-Scope Mitigations |
|-------|--------------|-------|----------------------|
| Passive Global Observer | Bulk capture, timing correlation | Deanonymize flows | Adaptive & Poisson cover traffic, padding, (future) path diversity, anti‑replay |
| Active Network Adversary | Inject / drop / reorder / delay / path kill | Downgrade / partition / correlation | Hybrid handshake validation, invalid key guards, multipath failover, strict parsing |
| Malicious Peer (Byzantine) | Malformed frames, protocol deviation | Resource exhaustion, state desync | Size bounds, capability negotiation enforcement, error categorization |
| Compromised Node (Post‑Compromise) | Key exfiltration, traffic pattern leak | Long‑term decryption, impersonation | Ephemeral keys, rekey policy, zeroization, hybrid secrecy |
| Local Side‑Channel Attacker | Cache / timing observation | Secret extraction | Constant‑time primitives (deps), no unsafe, avoid secret‑dependent branching |
| Supply Chain Attacker | Dependency swap / injection | Backdoor / exfiltration | Version pinning, no network build.rs, (planned) cargo‑deny & SBOM |

Out-of-scope (initial): simultaneous catastrophic break of both ML-KEM-768 & X25519, physical hardware attacks.

## 2. Cryptographic Design
- Hybrid Secret = `HKDF(salt = SHA256(client_pub||server_pub), ikm = kyber_ss || x25519_ss)` for robustness.
- ML-KEM-768 (post‑quantum IND‑CCA) + X25519 (mature, small key, constant‑time implementation).
- AEAD: ChaCha20-Poly1305 (ubiquitous constant‑time path). HPKE optional for plugin microchannels.
- Zeroization: `ZeroizeOnDrop` for long-lived secret containers.

## 3. Key & Session Lifecycle
| Material | Generation | Storage | Lifetime / Rekey Trigger (Target) | Disposal |
|----------|-----------|---------|----------------------------------|----------|
| Hybrid Handshake Key Pair | Ephemeral per session (OsRng) | RAM only | One connection | Drop → zeroize secret parts |
| Shared Secret | HKDF from hybrid | RAM only | Min(1GB data, 10 min) (configurable **planned hook**) | `ZeroizeOnDrop` |
| Plugin Session Keys | Derived (context KDF) | RAM | Plugin-defined (<= shared secret window) | Zeroize on plugin unload |
| Anti‑Replay Windows | Initialized per direction | RAM ring buffer | Rotated on rekey | Cleared at close |

Planned telemetry: `nyx_rekey_bytes_since`, `nyx_rekey_seconds_since`.

## 4. Defensive Controls
| Layer | Control | Description |
|-------|---------|-------------|
| Framing | Strict size bounds | Early reject oversize / malformed frames |
| Replay | Sliding windows & nonces | Separate windows for early data & multipath dataplane |
| Memory Safety | `#![forbid(unsafe_code)` | Enforced in core, crypto, transport, stream, conformance |
| Secret Hygiene | Ephemeral keys, zeroize | Minimizes long-term exposure window |
| Capability Negotiation | Required vs optional gating | Unsupported required → structured CLOSE frame |
| Observability | Prometheus & OTLP (opt-in) | Security events to become counters (invalid_key, replay) |
| Sandbox (future) | `os_sandbox` feature | OS-level restrictions / job objects / pledge analogs |

## 5. Side‑Channel Considerations
- Depend on constant‑time properties of upstream crates (`ml-kem`, `x25519-dalek`, `chacha20poly1305`, `blake3`, `sha2`).
- No secret‑dependent branching in handshake orchestration (reviewed).
- Pending: lightweight static scan for early‑exit comparisons / pattern leaks.

## 6. Telemetry & Privacy
- No raw secret values logged; debug prints redact or hash prefixes.
- Sampling (`otlp_sampling_rate`) to bound PII leakage risk.
- Future: hashed anonymized connection IDs in exported traces.

## 7. Supply Chain & Build Integrity
Current:
- Version pinning via workspace.
- No network fetch in build scripts (proto generation is local).
Planned:
- `cargo audit` + `cargo deny` CI gating.
- CycloneDX SBOM + signed release artifacts.
- Reproducible build (vendor + SHA256 manifest script).

## 8. Known Gaps / Roadmap
| Item | Status | Plan |
|------|--------|------|
| Rekey Enforcement Hook | WIP | Implement scheduler + counters |
| Formal Scope Doc | Pending | `FORMAL_SCOPE.md` enumerating safety/liveness |
| Entropy Anonymity Metrics | Planned | Compute & export anonymity set / entropy |
| QUIC Implementation | Stub | Integrate pure Rust QUIC lib (no C deps) |
| Side‑Channel Audit Script | Missing | Add pattern-based scanner in `scripts/` |
| Security Event Metrics | Partial | Add counters & docs |

## 9. Responsible Disclosure
Private channel (TBD). Please **avoid public issue** submission for vulnerabilities. Target SLA: acknowledge <72h, preliminary assessment <7d.

## 10. Licensing & Compatibility
- Dual MIT / Apache‑2.0 (permissive, audit‑friendly).
- No GPL contamination → easy downstream embedding.

---
*Contributions welcome – include rationale with each cryptographic or policy change.*
