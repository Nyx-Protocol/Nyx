# NyxNet Security Guide

**Last Updated**: October 7, 2025  
**Target Version**: v1.0

[日本語版](./07_SECURITY_GUIDE.md)

---

## Overview

NyxNet is a privacy network stack designed with security as the top priority. This document describes the security architecture, threat model, security best practices, and vulnerability reporting process.

---

## Security Principles

### 1. Memory Safety

**Implementation**: `#![forbid(unsafe_code)]` in all crates

Rust's ownership system eliminates entire vulnerability classes:
- Buffer overflows
- Use-After-Free
- Double free
- Data races

**Verification**:

```powershell
# Windows PowerShell
cargo clippy --workspace -- -D unsafe-code
```

```bash
# WSL / Linux / macOS
cargo clippy --workspace -- -D unsafe-code
```

---

### 2. Zero C/C++ Dependencies

**Rationale**: Avoid inheriting vulnerabilities from C/C++ libraries.

**Implementation**:
- Pure Rust crypto: `ml-kem`, `x25519-dalek`, `chacha20poly1305`
- Pure Go TLS: `crypto/tls` (nyx-http-proxy)
- No ring, OpenSSL, libsodium, or other C dependencies

**Verification**:

```bash
# WSL / Linux / macOS
cargo tree | grep -i "openssl\|ring\|libsodium"
# Expected: no matches
```

```powershell
# Windows PowerShell
cargo tree | Select-String -Pattern "openssl|ring|libsodium"
# Expected: no matches
```

---

### 3. Principle of Least Privilege

**Implementation**:
- Daemon runs as non-privileged user
- Minimal system calls
- Sandboxing (Linux: seccomp, Windows: AppContainer under consideration)

---

### 4. Secure by Default

**Default Settings**:
- Post-quantum crypto: Enabled
- Replay attack protection: Enabled
- Rate limiting: Enabled
- Encryption: Always enabled (cannot be disabled)

---

## Threat Model

### Threat Actors

| Actor | Capability | Mitigation |
|-------|-----------|------------|
| **Passive Eavesdropper** | Network traffic monitoring | Sphinx encryption, cover traffic |
| **Active Attacker** | Packet tampering, replay | AEAD authentication, timestamped nonces |
| **Quantum Computer** | Break public-key crypto | Hybrid PQ crypto (ML-KEM + X25519) |
| **Traffic Analysis** | Statistical pattern analysis | Cover traffic, timing obfuscation |
| **Malicious Mix Node** | Compromise of some nodes | 3-hop minimum, end-to-end encryption |

### Attack Scenarios

#### 1. Traffic Analysis Attack

**Attack**: Identify users through network monitoring

**Mitigation**:
- Poisson-distributed cover traffic generation
- Packet size normalization
- Timing obfuscation (delay injection)

**Residual Risk**: Long-term large-scale monitoring may enable statistical correlation (partially mitigated)

---

#### 2. Replay Attack

**Attack**: Retransmit past packets

**Mitigation**:
- Timestamp-based nonce verification (±5 min tolerance)
- Bloom filter duplicate detection (100K entries)
- Cryptographic random session IDs

**Implementation**: `nyx-core/src/security.rs`

```rust
pub struct ReplayProtection {
    bloom: BloomFilter,
    window: Duration, // 5 minutes
}

impl ReplayProtection {
    pub fn check_nonce(&self, nonce: &Nonce) -> Result<()> {
        if self.bloom.contains(nonce) {
            return Err(Error::ReplayDetected);
        }
        // Timestamp verification
        if nonce.timestamp().elapsed() > self.window {
            return Err(Error::NonceExpired);
        }
        Ok(())
    }
}
```

---

#### 3. Timing Attack

**Attack**: Infer secrets from cryptographic operation execution time

**Mitigation**:
- Constant-time comparison (using `subtle` crate)
- Constant-time crypto library implementations
- Timing obfuscation (random delays)

**Example**:

```rust
use subtle::ConstantTimeEq;

// Constant-time MAC verification
fn verify_mac(expected: &[u8], actual: &[u8]) -> bool {
    expected.ct_eq(actual).into()
}
```

---

#### 4. Denial of Service (DoS)

**Attack**: Resource exhaustion causing availability degradation

**Mitigation**:
- Rate limiting: 100 req/s (configurable)
- Connection limit: 1000 (configurable)
- Memory limit: 1GB (configurable)
- CPU usage monitoring: Alert at 80%

**Implementation**: `nyx-daemon/src/rate_limit.rs`

```rust
pub struct RateLimiter {
    limit: u32,
    window: Duration,
    tokens: Arc<Mutex<HashMap<ClientId, TokenBucket>>>,
}

impl RateLimiter {
    pub fn check(&self, client: &ClientId) -> Result<()> {
        let mut tokens = self.tokens.lock().unwrap();
        let bucket = tokens.entry(*client).or_insert_with(|| {
            TokenBucket::new(self.limit, self.window)
        });
        
        if bucket.try_consume() {
            Ok(())
        } else {
            Err(Error::RateLimitExceeded)
        }
    }
}
```

---

#### 5. Sybil Attack

**Attack**: Create multiple fake identities to compromise network

**Mitigation**:
- Path diversity requirements
- Reputation system (future enhancement)
- Proof-of-work for node registration (under consideration)

**Current Status**: Partially mitigated (trust on first use model)

---

## Cryptographic Architecture

### Key Hierarchy

```
Master Secret (never transmitted)
    │
    ├─→ Handshake Keys (ephemeral, ML-KEM + X25519)
    │       │
    │       └─→ Shared Secret (32 bytes)
    │               │
    │               └─→ HKDF Expand
    │                       │
    │                       ├─→ Traffic Key (32 bytes, ChaCha20)
    │                       ├─→ MAC Key (32 bytes, Poly1305)
    │                       └─→ Nonce (12 bytes)
    │
    └─→ Long-term Identity Key (Ed25519, for node signing)
```

### Cipher Suite

| Component | Algorithm | Key Size | Security Level |
|-----------|-----------|----------|----------------|
| **Key Exchange** | ML-KEM-768 + X25519 | 768-bit + 256-bit | Post-quantum secure |
| **AEAD** | ChaCha20Poly1305 | 256-bit | 256-bit security |
| **Hash** | BLAKE3 | 256-bit output | 256-bit security |
| **MAC** | Poly1305 (in AEAD) | 256-bit | 256-bit security |
| **Signature** | Ed25519 | 256-bit | 128-bit classical security |

---

### Key Rotation

**Handshake Keys**: Per-session (ephemeral)
**Traffic Keys**: Every 1GB of data or 1 hour (whichever comes first)
**Node Identity Keys**: Manual rotation (recommended annually)

**Automatic Rekeying**:

```rust
impl Session {
    async fn auto_rekey(&mut self) -> Result<()> {
        if self.bytes_sent > REKEY_BYTES || 
           self.start_time.elapsed() > REKEY_INTERVAL {
            // Perform handshake with new ephemeral keys
            self.perform_handshake().await?;
            self.bytes_sent = 0;
            self.start_time = Instant::now();
        }
        Ok(())
    }
}
```

---

## Secure Configuration

### Recommended Settings

**File**: `nyx.toml`

```toml
[security]
# Cryptography
enable_post_quantum = true        # Always true (cannot disable)
cipher_suite = "chacha20poly1305" # Only supported suite

# Network
max_connections = 1000
connection_timeout_sec = 30
idle_timeout_sec = 300

# Rate Limiting
rate_limit_req_per_sec = 100
rate_limit_burst = 200

# Cover Traffic
cover_traffic_rate = 5.0  # packets/sec
cover_traffic_enabled = true

[mix]
# Anonymity
min_hops = 3        # Minimum 3 hops (security requirement)
max_hops = 5        # Maximum 5 hops (performance trade-off)
path_diversity = true

[replay_protection]
nonce_window_sec = 300  # 5 minutes
bloom_filter_size = 100000
```

---

### Hardening Checklist

- [ ] Run daemon as non-root user (Linux/macOS)
- [ ] Configure firewall to block external access to gRPC port (50051)
- [ ] Enable cover traffic (always recommended)
- [ ] Set appropriate rate limits
- [ ] Monitor system resource usage
- [ ] Regularly update dependencies (`cargo update`)
- [ ] Review audit logs weekly
- [ ] Rotate node identity keys annually

---

## Network Security

### Firewall Configuration

#### Linux (iptables)

```bash
# WSL / Linux
set -euo pipefail

# Allow Nyx protocol port (default 43300)
sudo iptables -A INPUT -p tcp --dport 43300 -j ACCEPT

# Block external access to gRPC (only localhost)
sudo iptables -A INPUT -p tcp --dport 50051 ! -s 127.0.0.1 -j DROP

# Allow SOCKS5 proxy (only localhost)
sudo iptables -A INPUT -p tcp --dport 1080 ! -s 127.0.0.1 -j DROP

# Save rules
sudo iptables-save > /etc/iptables/rules.v4
```

#### Windows (Windows Firewall)

```powershell
# Windows PowerShell (requires administrator)

# Allow Nyx protocol port
New-NetFirewallRule -DisplayName "Nyx Protocol" `
  -Direction Inbound -LocalPort 43300 -Protocol TCP -Action Allow

# Block external gRPC access
New-NetFirewallRule -DisplayName "Block gRPC External" `
  -Direction Inbound -LocalPort 50051 -Protocol TCP `
  -RemoteAddress !127.0.0.1 -Action Block

# Allow SOCKS5 proxy (localhost only)
New-NetFirewallRule -DisplayName "SOCKS5 Localhost" `
  -Direction Inbound -LocalPort 1080 -Protocol TCP `
  -RemoteAddress 127.0.0.1 -Action Allow
```

---

### TLS Termination (for Remote Access)

NyxNet gRPC does **not** include TLS. For remote access, use a TLS termination proxy:

**Option 1: Envoy Proxy**

```yaml
# envoy.yaml
static_resources:
  listeners:
  - name: grpc_listener
    address:
      socket_address:
        address: 0.0.0.0
        port_value: 50052
    filter_chains:
    - filters:
      - name: envoy.filters.network.http_connection_manager
        typed_config:
          "@type": type.googleapis.com/envoy.extensions.filters.network.http_connection_manager.v3.HttpConnectionManager
          stat_prefix: grpc_inbound
          codec_type: AUTO
          route_config:
            name: local_route
            virtual_hosts:
            - name: backend
              domains: ["*"]
              routes:
              - match:
                  prefix: "/"
                route:
                  cluster: nyx_grpc
      tls_context:
        common_tls_context:
          tls_certificates:
          - certificate_chain: {filename: "/etc/envoy/cert.pem"}
            private_key: {filename: "/etc/envoy/key.pem"}
  clusters:
  - name: nyx_grpc
    connect_timeout: 5s
    type: STRICT_DNS
    lb_policy: ROUND_ROBIN
    http2_protocol_options: {}
    load_assignment:
      cluster_name: nyx_grpc
      endpoints:
      - lb_endpoints:
        - endpoint:
            address:
              socket_address:
                address: 127.0.0.1
                port_value: 50051
```

**Start Envoy**:

```bash
# Linux / macOS / WSL
envoy -c envoy.yaml
```

---

## Security Auditing

### Logging

**Log Levels**:
- `ERROR`: Security incidents, authentication failures
- `WARN`: Suspicious activity, rate limit violations
- `INFO`: Connection events, configuration changes
- `DEBUG`: Detailed protocol messages (not for production)

**Configuration**:

```toml
[logging]
level = "info"
target = "file"
file_path = "/var/log/nyx/daemon.log"
max_size_mb = 100
rotation = "daily"

[audit]
enabled = true
log_auth_failures = true
log_rate_limit_violations = true
log_config_changes = true
```

---

### Monitoring

**Metrics to Monitor**:

| Metric | Alert Threshold | Action |
|--------|----------------|--------|
| Authentication failures | >10/min | Investigate source IP |
| Rate limit violations | >100/min | Check for DoS attack |
| Connection timeouts | >50% | Check network/node health |
| Memory usage | >90% | Restart daemon |
| CPU usage | >80% | Scale horizontally |
| Packet loss rate | >5% | Check network quality |

**Prometheus Alerts** (example):

```yaml
groups:
- name: nyx_security
  rules:
  - alert: HighAuthFailureRate
    expr: rate(nyx_auth_failures_total[1m]) > 10
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "High authentication failure rate"
      description: "{{ $value }} auth failures/min"
```

---

## Incident Response

### Security Incident Handling

**1. Detection**
- Monitor logs and metrics
- Automated alerts (Prometheus/Grafana)
- User reports

**2. Containment**
- Isolate affected nodes
- Block malicious IPs
- Rotate compromised keys

**3. Investigation**
- Collect logs and packet captures
- Analyze attack vectors
- Identify root cause

**4. Recovery**
- Patch vulnerabilities
- Restore from backups if needed
- Re-enable services

**5. Post-Incident**
- Update threat model
- Improve detection mechanisms
- Document lessons learned

---

### Emergency Commands

**Block malicious IP** (Linux):

```bash
# WSL / Linux
sudo iptables -A INPUT -s MALICIOUS_IP -j DROP
```

**Block malicious IP** (Windows):

```powershell
# Windows PowerShell
New-NetFirewallRule -DisplayName "Block Malicious IP" `
  -Direction Inbound -RemoteAddress MALICIOUS_IP -Action Block
```

**Emergency daemon shutdown**:

```bash
# Linux / macOS / WSL
sudo systemctl stop nyx-daemon
# Or
pkill -9 nyx-daemon
```

```powershell
# Windows PowerShell
Stop-Service NyxDaemon
# Or
Stop-Process -Name nyx-daemon -Force
```

---

## Vulnerability Reporting

### Responsible Disclosure

**Contact**: security@nyxnet.example (replace with actual contact)

**Please Include**:
1. Description of vulnerability
2. Steps to reproduce
3. Potential impact
4. Suggested fix (if any)

**Response Timeline**:
- Acknowledgment: Within 48 hours
- Initial assessment: Within 7 days
- Patch development: 30-90 days (depending on severity)
- Public disclosure: After patch release + 14 days

---

### Severity Levels

| Severity | Description | Example |
|----------|-------------|---------|
| **Critical** | Remote code execution, authentication bypass | Unauthenticated RCE |
| **High** | Privilege escalation, sensitive data leak | Admin API access without auth |
| **Medium** | DoS, information disclosure | Memory exhaustion attack |
| **Low** | Minor information leak, timing side-channel | Version fingerprinting |

---

## Security Testing

### Tools Used

1. **cargo-audit**: Dependency vulnerability scanning
2. **cargo-fuzz**: Fuzzing for crash/hang detection
3. **cargo-clippy**: Static analysis lints
4. **ASAN/MSAN**: Memory error detection (in tests)
5. **TLA+**: Formal protocol verification

### Regular Security Checks

**Daily** (automated):
- Dependency audit (`cargo audit`)
- CVE database sync

**Weekly** (automated):
- Full test suite with ASAN
- Fuzzing campaign (24hr)

**Monthly** (manual):
- Security configuration review
- Log analysis
- Threat model update

**Annually** (external):
- Third-party security audit
- Penetration testing

---

## Compliance and Standards

### Cryptographic Standards

- **NIST**: FIPS 140-3 Level 1 (goal, not yet certified)
- **ML-KEM**: NIST standardized post-quantum KEM (FIPS 203)
- **ChaCha20Poly1305**: RFC 8439
- **X25519**: RFC 7748
- **Ed25519**: RFC 8032

### Privacy Standards

- **GDPR**: No PII collection by default
- **CCPA**: User data transparency
- **ISO 27001**: Information security management (goal)

---

## Security Roadmap

### Current (v1.0)

- ✅ Memory-safe Rust implementation
- ✅ Post-quantum hybrid handshake
- ✅ Zero C/C++ dependencies
- ✅ Basic replay protection
- ✅ Rate limiting

### Near-term (v1.1-v1.2)

- 🔄 Linux seccomp sandboxing
- 🔄 Advanced traffic analysis resistance
- 🔄 Reputation system for mix nodes
- 🔄 Automated key rotation

### Long-term (v2.0+)

- 📅 Formal security audit
- 📅 FIPS 140-3 certification
- 📅 Windows AppContainer sandboxing
- 📅 Hardware security module (HSM) support
- 📅 Threshold cryptography for distributed trust

---

## Disclaimer: Inferred Content

The following information is reasonably inferred from security best practices:

- **Rate limit values**: Reasonable defaults, actual may vary per deployment
- **Alert thresholds**: Based on typical attack patterns
- **Incident response timeline**: Standard industry practice

For precise security configurations, consult with security professionals for your specific deployment environment.

---

## Security Contact

For security-sensitive questions or to report vulnerabilities, please use:

- **Email**: security@example.com (replace with actual)
- **PGP Key**: Available at https://example.com/pgp (replace with actual)
- **Bug Bounty**: Program details at https://example.com/bounty (if applicable)

**Please do NOT**:
- Open public GitHub issues for security vulnerabilities
- Discuss vulnerabilities in public channels before disclosure
- Perform security testing on production systems without permission
