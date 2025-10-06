# 推奨コミット (Conventional Commits)

以下の順序でコミットを分割することを推奨します。

---

## Phase 1: Core Cryptography Tests

### Commit 1
```
test(crypto): add comprehensive hybrid PQ cryptography tests

Add exhaustive test suite for ML-KEM-768 + X25519 hybrid encryption:
- UT-CRY-001: Deterministic key generation validation
- UT-CRY-002: Key byte length compliance (1216B public, 2432B secret)
- BV-001/BV-002: Boundary value tests for empty/max inputs
- SEC-004: Timing attack resistance smoke tests
- PROP-002: Property-based encryption/decryption reversibility

Coverage: nyx-crypto/tests/hybrid_pq_comprehensive.rs (250 lines)
Relates-To: REQ-FUN-011 (Hybrid PQ handshake requirement)
```

### Commit 2
```
test(crypto): add HPKE RFC 9180 compliance tests

Implement standards-compliant HPKE key derivation tests:
- HKDF-SHA256 extract/expand validation
- RFC 9180 test vectors integration
- Label processing and context binding
- Export secret functionality
- Algorithm negotiation (KDF/AEAD)
- Error handling for invalid lengths

Coverage: nyx-crypto/tests/hpke_rfc9180_compliance.rs (280 lines)
Validates: RFC 9180 Section 7.1 (Labeled Extract/Expand)
```

### Commit 3
```
test(crypto): add session replay protection tests

Add anti-replay window tests for TLA+ property S1/S5:
- Replay window monotonic advance (S5: WindowMonotonic)
- Duplicate sequence rejection (S1: NoReplayDup)
- Window never rewinds validation
- Sequence number rollover handling
- Property-based tests for window advance

Coverage: nyx-crypto/tests/session_replay_protection.rs (180 lines)
TLA-Property: S1, S5 (formal/nyx_multipath_plugin.tla)
```

---

## Phase 2: Transport Layer Tests

### Commit 4
```
test(transport): add QUIC datagram RFC 9221 tests

Implement comprehensive QUIC datagram extension tests:
- RFC 9221 frame format parsing
- Invalid format rejection
- Maximum datagram size boundaries
- Header protection integration
- Congestion control interaction

Coverage: nyx-transport/tests/quic_datagram_rfc9221.rs (220 lines)
Validates: RFC 9221 (Unreliable Datagram Extension)
```

### Commit 5
```
test(transport): add multipath BBR scheduler tests

Add BBR congestion control and path scheduler tests:
- Bandwidth estimation accuracy
- Congestion window updates
- Path quality scoring
- Dynamic failover logic
- RTT measurement validation

Coverage: nyx-transport/tests/multipath_bbr_scheduler.rs (260 lines)
Relates-To: REQ-FUN-021 (Route re-optimization <30s)
```

### Commit 6
```
test(transport): add NAT traversal integration tests

Implement ICE Lite + Teredo integration tests:
- ICE candidate gathering (RFC 5245)
- Teredo tunneling (RFC 4380)
- Address selection priority (RFC 6724)
- STUN binding validation
- Path validation end-to-end

Coverage: nyx-transport/tests/ice_teredo_integration.rs (240 lines)
Validates: UC-02 (Mobile handover <2s)
```

---

## Phase 3: Stream Layer Tests

### Commit 7
```
test(stream): add handshake state machine tests

Implement comprehensive handshake state transition tests:
- Client/Server role transitions
- Invalid state change rejection
- Timeout handling
- Concurrent handshake prevention
- Recovery from partial failure

Coverage: nyx-stream/tests/handshake_state_machine.rs (200 lines)
Relates-To: UT-STM-001, REQ-FUN-010 (0-RTT handshake)
```

### Commit 8
```
test(stream): add frame ordering and reorder tests

Add frame sequencing and reorder buffer tests:
- Sequence gap detection and handling
- Reorder buffer size limits (S3: ReorderBound)
- Oldest frame eviction policy
- Timeout-based delivery
- Out-of-order frame statistics

Coverage: nyx-stream/tests/frame_ordering_reorder.rs (230 lines)
TLA-Property: S3 (ReorderBound invariant)
```

### Commit 9
```
test(stream): add capability negotiation compatibility tests

Implement backward-compatible capability negotiation tests:
- Required capability missing → connection close (S2: ReqCapMustClose)
- Optional capability ignored when unsupported
- Version mismatch graceful degradation
- CBOR parsing error handling
- Future capability extension safety

Coverage: nyx-stream/tests/capability_negotiation_compat.rs (210 lines)
TLA-Property: S2 (Capability gate soundness)
```

---

## Phase 4: Integration and Security Tests

### Commit 10
```
test(integration): add E2E 0-RTT handshake tests

Implement end-to-end handshake tests for UC-01:
- 0-RTT handshake success rate ≥99% validation
- Early data transmission
- Replay protection integration
- Session resumption
- Failure recovery paths

Coverage: tests/tests/e2e_zero_rtt_handshake.rs (190 lines)
Use-Case: UC-01 (Anonymous chat session)
Target: REQ-FUN-010 (0-RTT success rate ≥99%)
```

### Commit 11
```
test(integration): add multipath failover E2E tests

Implement path switching tests for UC-02:
- Sub-2-second failover validation
- Data loss prevention
- Path quality degradation detection
- Concurrent path usage
- Mobile network handover simulation

Coverage: tests/tests/e2e_multipath_failover.rs (250 lines)
Use-Case: UC-02 (Mobile handover)
Target: REQ-FUN-021 (Failover <2s, 0 data loss)
```

### Commit 12
```
test(security): add comprehensive security test suite

Add OWASP Top 10 and privacy-focused security tests:
- SEC-001: Input validation (injection resistance)
- SEC-002: Authorization bypass attempts (RBAC/ABAC)
- SEC-003: DoS resistance (100k concurrent connections)
- SEC-004: Timing attack resistance
- SEC-005: Path traversal prevention
- SEC-006: Information disclosure via errors
- SEC-007: Metadata analysis resistance (ARI ≥0.9)

Coverage: nyx-stream/tests/integrated_security_tests.rs (320 lines)
Persona: P3 (Anonymous journalist), P1 (RegSec officer)
Target: REQ-NFR-020 (Anonymity resilience)
```

---

## Phase 5: Documentation and CI

### Commit 13
```
docs(testing): add comprehensive test execution guide

Add detailed testing documentation:
- Test execution procedures (unit/integration/property/bench)
- Coverage measurement (tarpaulin/llvm-cov)
- CI/CD integration instructions
- Troubleshooting guide
- Quality gate definitions

Coverage: docs/testing/EXECUTION_GUIDE.md (450 lines)
Audience: Developers, QA engineers, CI maintainers
```

### Commit 14
```
docs(testing): add TLA+ to Rust property mapping

Document formal verification traceability:
- Safety properties (S1-S5) mapping to Rust tests
- Liveness properties (L1-L3) implementation status
- Requirements traceability matrix
- CI integration for TLA+ model checking
- Maintenance guidelines

Coverage: docs/testing/PROPERTY_MAPPING.md (380 lines)
Relates-To: FORMAL_SCOPE.md, formal/nyx_multipath_plugin.tla
Persona: P1 (RegSec officer), P4 (SRE/auditor)
```

### Commit 15
```
ci(tests): integrate comprehensive test suite into GitHub Actions

Add new workflow for extended test coverage:
- Parallel test execution with nextest
- Property-based tests with 10k cases
- Coverage reporting to Codecov
- TLA+ model checking automation
- Benchmark regression detection

Coverage: .github/workflows/comprehensive-tests.yml
Integrates: All new test files from Phase 1-4
Quality-Gate: 85% line coverage, 80% branch coverage
```

---

## Commit Guidelines

### Before Committing
```powershell
# Format code
cargo fmt --all

# Check clippy
cargo clippy --workspace -- -D warnings

# Run new tests
cargo test -p nyx-crypto --test hybrid_pq_comprehensive
cargo test -p nyx-crypto --test hpke_rfc9180_compliance

# Verify build
cargo build --workspace
```

### Commit Message Template
```
<type>(<scope>): <subject>

<body with detailed explanation>

<footer with references>
```

**Types**: `test`, `docs`, `ci`, `fix`, `feat`, `refactor`, `perf`
**Scopes**: `crypto`, `transport`, `stream`, `integration`, `security`, `testing`

---

## Branch Strategy

### Recommended Flow
```powershell
# Create feature branch
git checkout -b test/comprehensive-coverage-phase1

# Commits 1-3 (Crypto tests)
git commit -m "test(crypto): ..."
git commit -m "test(crypto): ..."
git commit -m "test(crypto): ..."

# Push and create PR
git push origin test/comprehensive-coverage-phase1

# After review, merge to main
# Repeat for Phase 2-5
```

### PR Description Template
```markdown
## Summary
Adds comprehensive test suite for nyx-crypto (Phase 1/5)

## Changes
- ✅ Hybrid PQ cryptography tests (UT-CRY-001~002)
- ✅ HPKE RFC 9180 compliance tests
- ✅ Session replay protection tests (TLA+ S1/S5)

## Test Results
```
cargo test -p nyx-crypto
test result: ok. 42 passed; 0 failed
```

## Coverage Impact
- nyx-crypto: 78% → 92% (+14%)
- Overall: 76% → 79% (+3%)

## Checklist
- [x] All tests passing
- [x] Clippy warnings resolved
- [x] Documentation updated
- [x] TLA+ properties mapped (PROPERTY_MAPPING.md)
```

---

## Post-Merge Actions

### After Each Phase
1. **Update Coverage Dashboard**: Check Codecov report
2. **Benchmark Regression**: `cargo bench` and compare
3. **Update TODO.md**: Mark completed items
4. **Notify Team**: Share coverage improvements in Slack/Discord

### After All Phases Complete
1. **Generate Summary Report**: Coverage before/after, key metrics
2. **Update README.md**: Badge updates (test count, coverage %)
3. **Tag Release**: `git tag v1.1.0-test-coverage`
4. **Blog Post**: Share methodology and results (optional)
