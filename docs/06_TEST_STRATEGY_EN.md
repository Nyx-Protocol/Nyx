# NyxNet Test Strategy Documentation

**Last Updated**: October 7, 2025  
**Target Version**: v1.0

[日本語版](./06_TEST_STRATEGY.md)

---

## Overview

NyxNet ensures high quality and reliability through a multi-layered testing strategy. This document describes test types, coverage targets, execution methods, and CI/CD integration.

---

## Test Pyramid

```
              ┌─────────────────┐
              │  E2E Tests      │  20+
              │  (Kubernetes)   │
              └─────────────────┘
                     ▲
              ┌──────────────────────┐
              │  Integration Tests   │  50+
              │  (Multi-crate)       │
              └──────────────────────┘
                        ▲
              ┌───────────────────────────┐
              │    Unit Tests             │  300+
              │    (Per-module)           │
              └───────────────────────────┘
                          ▲
              ┌────────────────────────────────┐
              │  Property-based Tests          │  30+
              │  (Proptest, Randomized)        │
              └────────────────────────────────┘
```

**Total Test Count**: 400+ tests across all layers

---

## 1. Unit Tests

### Purpose

Verify correctness of individual functions and modules.

### Execution

#### Windows PowerShell

```powershell
# All workspace tests
cargo test --workspace

# Specific crate only
cargo test -p nyx-crypto

# With verbose logging
$env:RUST_LOG="debug"
cargo test -p nyx-crypto -- --nocapture
```

#### WSL/Linux/macOS (bash)

```bash
# All workspace tests
cargo test --workspace --no-fail-fast

# Limit parallelism
cargo test --workspace -- --test-threads=4

# Verbose logging
RUST_LOG=debug cargo test -- --nocapture
```

### Coverage Targets

- **Core crates**: 85%+ (nyx-core, nyx-crypto)
- **Business logic**: 75%+ (nyx-mix, nyx-stream)
- **Integration layers**: 60%+ (nyx-daemon, nyx-cli)

### Important Test Examples

#### nyx-crypto: Hybrid Handshake

Location: `nyx-crypto/src/hybrid_handshake.rs`

```rust
#[test]
fn test_hybrid_handshake_roundtrip() -> Result<()> {
    // Client generates keypair
    let (client_pk, client_kp) = client_init()?;
    
    // Server encapsulates
    let (ct, ss_server) = server_encapsulate(&client_pk)?;
    
    // Client decapsulates
    let ss_client = client_decapsulate(&client_kp, &ct)?;
    
    // Verify shared secrets match
    assert_eq!(ss_server.as_bytes(), ss_client.as_bytes());
    Ok(())
}
```

**Verification Items**:
- Key generation determinism (same seed → same keys)
- Encapsulation/decapsulation correctness
- Error handling (invalid public keys)

---

#### nyx-mix: Sphinx Packet Processing

Location: `nyx-mix/src/sphinx.rs`

```rust
#[test]
fn test_sphinx_packet_unwrap() -> Result<()> {
    let path = vec![node1_id, node2_id, node3_id];
    let payload = b"secret message";
    
    // Build Sphinx packet
    let packet = build_sphinx_packet(path.clone(), payload)?;
    
    // Each hop unwraps one layer
    let (packet, _) = node1.unwrap_layer(&packet)?;
    let (packet, _) = node2.unwrap_layer(&packet)?;
    let (final_payload, _) = node3.unwrap_layer(&packet)?;
    
    assert_eq!(final_payload, payload);
    Ok(())
}
```

**Verification Items**:
- Onion layer unwrapping correctness
- MAC verification at each hop
- Routing information integrity

---

## 2. Integration Tests

### Purpose

Verify interaction between multiple crates.

### Execution

#### Windows PowerShell

```powershell
# Integration test suite
cargo test -p tests --test integration

# Specific integration test
cargo test -p tests --test integration -- test_stream_lifecycle
```

#### WSL/Linux/macOS (bash)

```bash
# Integration tests
cargo test -p tests --test integration -- --nocapture

# With timeout
timeout 300 cargo test -p tests --test integration
```

### Important Integration Tests

#### Stream Lifecycle

Location: `tests/integration/stream_lifecycle.rs`

**Test Scenario**:
1. Start daemon
2. Establish stream between two peers
3. Transfer data (1KB, 1MB, 8MB)
4. Close stream
5. Verify resource cleanup

```rust
#[tokio::test]
async fn test_stream_lifecycle() -> Result<()> {
    // 1. Start two daemon instances
    let daemon1 = start_daemon(50051).await?;
    let daemon2 = start_daemon(50052).await?;
    
    // 2. Open stream from daemon1 to daemon2
    let stream = daemon1.open_stream("127.0.0.1:50052").await?;
    
    // 3. Send data
    let data = vec![0u8; 1024 * 1024]; // 1MB
    stream.send(&data).await?;
    
    // 4. Receive data
    let received = daemon2.receive().await?;
    assert_eq!(data, received);
    
    // 5. Close and verify cleanup
    stream.close().await?;
    assert_eq!(daemon1.active_streams(), 0);
    
    Ok(())
}
```

---

#### Multi-hop Routing

Location: `tests/integration/multipath_routing.rs`

**Test Scenario**:
1. Set up 5-node network
2. Build 3-hop path
3. Send 1000 packets
4. Verify all packets arrive (with FEC)

---

## 3. Property-Based Tests

### Purpose

Find edge cases through randomized testing.

### Framework

**Proptest**: Generate random test cases and verify properties hold.

### Execution

#### Windows PowerShell

```powershell
# Run property tests
cargo test -p nyx-crypto --features hybrid -- --nocapture

# With specific seed for reproducibility
$env:PROPTEST_RNG_SEED="42"
cargo test -p nyx-crypto
```

#### WSL/Linux/macOS (bash)

```bash
# Run property tests
cargo test -p nyx-crypto --features hybrid -- --nocapture

# With seed
PROPTEST_RNG_SEED=42 cargo test -p nyx-crypto
```

### Important Property Tests

#### Handshake Commutativity

Location: `nyx-crypto/tests/property_tests.rs`

```rust
proptest! {
    #[test]
    fn prop_handshake_always_succeeds(seed in any::<u64>()) {
        let mut rng = ChaCha20Rng::seed_from_u64(seed);
        
        // Client and server perform handshake
        let (pk, kp) = client_init_with_rng(&mut rng)?;
        let (ct, ss_s) = server_encapsulate_with_rng(&pk, &mut rng)?;
        let ss_c = client_decapsulate(&kp, &ct)?;
        
        // Property: shared secrets always match
        prop_assert_eq!(ss_s.as_bytes(), ss_c.as_bytes());
    }
}
```

**Properties Verified**:
- Handshake always succeeds (no random failures)
- Shared secrets always match
- Key generation never produces invalid keys

---

#### Multipath Selection Fairness

```rust
proptest! {
    #[test]
    fn prop_multipath_selection_fair(
        path_count in 2usize..10,
        selections in 1000usize..10000
    ) {
        let mut selector = PathSelector::new(path_count);
        let mut counts = vec![0; path_count];
        
        for _ in 0..selections {
            let path = selector.select();
            counts[path] += 1;
        }
        
        // Property: each path selected roughly equally
        let avg = selections / path_count;
        for count in counts {
            let deviation = (count as f64 - avg as f64).abs() / avg as f64;
            prop_assert!(deviation < 0.2); // Within 20%
        }
    }
}
```

---

## 4. End-to-End Tests

### Purpose

Verify complete system behavior in production-like environment.

### Infrastructure

- **Kubernetes**: Minikube or kind cluster
- **Nodes**: 3-5 mix nodes
- **Load**: 10-100 concurrent streams

### Execution

#### Windows PowerShell

```powershell
# Requires Docker Desktop with Kubernetes enabled
# Or use WSL with kind

# Build Docker image
docker build -t nyxnet:test .

# Run E2E tests
cargo test -p tests --test e2e -- --ignored
```

#### WSL/Linux/macOS (bash)

```bash
set -euo pipefail

# Create kind cluster
kind create cluster --config kind-config.yaml

# Load image
docker build -t nyxnet:test .
kind load docker-image nyxnet:test

# Deploy test environment
kubectl apply -f k8s-nyx-multinode.yaml

# Run E2E tests
cargo test -p tests --test e2e -- --ignored --nocapture

# Cleanup
kind delete cluster
```

### Important E2E Tests

#### Multi-node Network

Location: `tests/e2e/multinode.rs`

**Test Scenario**:
1. Deploy 5 nodes to Kubernetes
2. Wait for mesh network formation (30s)
3. Establish 10 concurrent streams
4. Transfer 100MB total data
5. Verify <1% packet loss
6. Check latency <500ms

---

## 5. Benchmarks

### Purpose

Prevent performance regressions and identify bottlenecks.

### Framework

**Criterion**: Statistical benchmarking with HTML reports.

### Execution

#### Windows PowerShell

```powershell
# Run all benchmarks
cargo bench --workspace

# Specific benchmark
cargo bench -p nyx-crypto hybrid_handshake

# View results
start .\target\criterion\report\index.html
```

#### WSL/Linux/macOS (bash)

```bash
# Run benchmarks
cargo bench --workspace

# Generate HTML report
cargo bench --features html_reports

# View results (macOS)
open target/criterion/report/index.html

# View results (Linux)
xdg-open target/criterion/report/index.html
```

### Important Benchmarks

#### Hybrid Handshake Performance

Location: `nyx-crypto/benches/hybrid_handshake.rs`

```rust
fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("hybrid_handshake_full", |b| {
        b.iter(|| {
            let (pk, kp) = client_init().unwrap();
            let (ct, ss_s) = server_encapsulate(&pk).unwrap();
            let ss_c = client_decapsulate(&kp, &ct).unwrap();
            black_box((ss_s, ss_c))
        })
    });
}
```

**Performance Targets**:
- Full handshake: <5ms (median)
- Client init: <2ms
- Server encapsulate: <2ms
- Client decapsulate: <1ms

---

#### Sphinx Packet Processing

**Performance Targets**:
- Packet build: <1ms
- Layer unwrap: <0.5ms
- Throughput: 10,000+ packets/sec per core

---

## 6. Conformance Tests

### Purpose

Verify protocol compliance and feature completeness.

### Execution

#### Compliance Gate (Mandatory for CI)

```bash
# Linux / macOS / WSL
make compliance-check

# Or directly
cargo test -p nyx-conformance ci_compliance_gate_main --features hybrid -- --nocapture
```

**Exit Code**:
- `0`: Core compliance achieved ✅
- `1`: Core compliance failed ❌

---

#### Full Compliance Matrix

```bash
# Linux / macOS / WSL
make compliance-report

# Output: ./compliance-reports/compliance_matrix.json
```

**Compliance Levels**:
- **Core**: Hybrid handshake, basic stream, essential security
- **Plus**: Multipath, telemetry, performance optimization
- **Full**: Plugin system, advanced routing, formal verification

---

### Compliance Test Structure

Location: `nyx-conformance/src/lib.rs`

```rust
#[test]
fn ci_compliance_gate_main() {
    let required_level = env::var("NYX_REQUIRED_COMPLIANCE_LEVEL")
        .unwrap_or_else(|_| "core".to_string());
    
    let result = run_compliance_suite();
    
    match required_level.as_str() {
        "core" => assert!(result.core_passed),
        "plus" => assert!(result.plus_passed),
        "full" => assert!(result.full_passed),
        _ => panic!("Invalid compliance level"),
    }
}
```

---

## 7. Formal Verification (TLA+)

### Purpose

Mathematical proof of protocol correctness.

### Tools

- **TLA+ Toolbox**: Specification and model checking
- **TLC**: Model checker

### Specifications

Located in `formal/` directory:

1. **NyxStreamProtocol.tla**: Stream state machine
2. **NyxHybridHandshake.tla**: Handshake protocol
3. **NyxMultipathRouting.tla**: Multipath selection algorithm
4. **NyxCoverTraffic.tla**: Cover traffic generation

### Verification Commands

```bash
# Linux / macOS / WSL
cd formal

# Run TLC model checker
tlc NyxStreamProtocol.tla -config stream.cfg

# Check all specifications
./check_all_syntax.sh
```

**Verified Properties**:
- **Safety**: No two parties can derive different shared secrets
- **Liveness**: All streams eventually complete or timeout
- **Deadlock-freedom**: No circular wait conditions

---

## 8. Security Testing

### Fuzzing

**Tool**: cargo-fuzz (libFuzzer)

#### Setup

```bash
# Linux / macOS / WSL
cargo install cargo-fuzz

# List fuzz targets
cargo fuzz list
```

#### Execution

```bash
# Fuzz hybrid handshake
cargo fuzz run fuzz_hybrid_handshake

# With corpus and timeout
cargo fuzz run fuzz_sphinx_packet -- -max_total_time=3600
```

**Fuzz Targets**:
- `fuzz_hybrid_handshake`: Malformed key inputs
- `fuzz_sphinx_packet`: Corrupted packet headers
- `fuzz_stream_frames`: Invalid frame structures

---

### Static Analysis

#### Clippy (Mandatory)

```bash
# Linux / macOS / WSL
cargo clippy --workspace --all-targets --all-features -- -D warnings
```

**Enforced Lints**:
- `unsafe_code`: Forbidden
- `unwrap_used`: Warning
- `panic`: Warning
- `todo`: Warning

---

#### cargo-audit (Dependency Vulnerability Scan)

```bash
# Linux / macOS / WSL
cargo install cargo-audit
cargo audit

# Check specific advisory
cargo audit --deny RUSTSEC-2024-XXXX
```

---

## 9. CI/CD Integration

### GitHub Actions Workflows

NyxNet uses **18 workflows** for comprehensive CI/CD:

1. **main.yml**: Lint, test, build (Linux, macOS, Windows)
2. **security.yml**: Audit, SBOM generation, CVE scanning
3. **compliance.yml**: Protocol compliance verification
4. **benchmarks.yml**: Performance regression testing
5. **docker.yml**: Container image builds and scans
6. **fuzzing.yml**: Continuous fuzzing (oss-fuzz integration)
7. **formal.yml**: TLA+ specification validation
8. Others: Dependency updates, release automation, documentation

---

### Test Execution Flow

```
┌──────────────┐
│  Push/PR     │
└──────┬───────┘
       │
       ▼
┌─────────────────┐
│  Fast Feedback  │  (5 min)
│  - Lint         │
│  - Format check │
│  - Type check   │
└─────┬───────────┘
      │
      ▼
┌─────────────────┐
│  Unit Tests     │  (10 min)
│  - All crates   │
│  - 300+ tests   │
└─────┬───────────┘
      │
      ▼
┌─────────────────┐
│  Integration    │  (15 min)
│  - 50+ tests    │
│  - Multi-crate  │
└─────┬───────────┘
      │
      ▼
┌─────────────────┐
│  Compliance     │  (5 min)
│  - Gate check   │
│  - Core level   │
└─────┬───────────┘
      │
      ▼
┌─────────────────┐
│  Security       │  (10 min)
│  - Audit        │
│  - SBOM         │
└─────┬───────────┘
      │
      ▼
┌─────────────────┐
│  E2E (nightly)  │  (30 min)
│  - Kubernetes   │
│  - 20+ tests    │
└─────────────────┘

Total CI time: ~45 min (fast path)
Total CI time: ~75 min (full path with E2E)
```

---

### Quality Gates

All PRs must pass:

1. ✅ All tests green (unit, integration, compliance)
2. ✅ Clippy with no warnings
3. ✅ Code formatted (cargo fmt)
4. ✅ No new security advisories
5. ✅ Core compliance level achieved
6. ✅ No performance regressions (>5% slower)

---

## 10. Test Data Management

### Test Fixtures

Location: `tests/fixtures/`

**Contents**:
- `keys/`: Pre-generated keypairs for deterministic tests
- `packets/`: Sample Sphinx packets
- `configs/`: Test configuration files

### Snapshot Testing

**Tool**: insta (snapshot testing for Rust)

```rust
#[test]
fn test_config_serialization() {
    let config = NyxConfig::default();
    let json = serde_json::to_string_pretty(&config).unwrap();
    
    // Compare with saved snapshot
    insta::assert_snapshot!(json);
}
```

---

## 11. Performance Testing

### Load Testing

**Tool**: Custom benchmark suite in `tests/benchmarks/`

**Scenarios**:
1. Concurrent streams: 100, 500, 1000
2. Data sizes: 1KB, 1MB, 10MB, 100MB
3. Packet loss rates: 0%, 1%, 5%, 10%

**Execution**:

```bash
# Linux / macOS / WSL
cd tests/benchmarks
cargo build --release
./target/release/nyx-benchmarks --scenario high-throughput
```

---

### Profiling

#### CPU Profiling

```bash
# Linux (perf)
cargo build --release
perf record --call-graph dwarf ./target/release/nyx-daemon
perf report

# macOS (Instruments)
cargo instruments --release -p nyx-daemon --template "Time Profiler"
```

#### Memory Profiling

```bash
# Linux (valgrind)
cargo build --release
valgrind --tool=massif ./target/release/nyx-daemon

# Heap profiler
cargo build --release --features jemalloc
MALLOC_CONF=prof:true ./target/release/nyx-daemon
```

---

## 12. Test Maintenance

### Coverage Tracking

**Tool**: tarpaulin (code coverage for Rust)

```bash
# Linux / macOS / WSL
cargo install cargo-tarpaulin

# Generate coverage report
cargo tarpaulin --workspace --out Html --output-dir ./coverage

# View report
xdg-open coverage/index.html
```

**Coverage Targets** (workspace average):
- Current: ~75%
- Target: 80%
- Core crates: 85%+

---

### Flaky Test Detection

**Strategy**:
1. Run tests 100 times in CI (nightly)
2. Flag tests with >1% failure rate
3. Add determinism or increase timeouts

**Command**:

```bash
# Linux / macOS / WSL
for i in {1..100}; do
  cargo test --workspace || echo "Run $i failed"
done
```

---

## Test Execution Summary

| Test Type | Count | Time | Frequency |
|-----------|-------|------|-----------|
| Unit | 300+ | 10 min | Every commit |
| Integration | 50+ | 15 min | Every commit |
| Property-based | 30+ | 5 min | Every commit |
| E2E | 20+ | 30 min | Nightly |
| Benchmarks | 15+ | 20 min | Weekly |
| Compliance | 10+ | 5 min | Every commit |
| Fuzz | Continuous | ∞ | 24/7 (oss-fuzz) |
| Formal | 15+ specs | Manual | On-demand |

**Total**: 440+ automated tests

---

## Disclaimer: Inferred Content

The following information is reasonably inferred from codebase structure and typical testing practices:

- **Test counts**: Approximate numbers based on file counts in `tests/` directories
- **Execution times**: Estimated from typical CI run durations
- **Coverage percentages**: Target values, actual may vary

For precise test metrics, run the test suite and check coverage reports.
