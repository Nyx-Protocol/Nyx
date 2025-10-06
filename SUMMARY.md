# NyxNet Project Summary (Judge-Facing)

> Concise one-page overview for evaluation. Focus: problem, solution, differentiators, measurable impact.

## 1. Problem
Modern privacy / resilience demands (PQC readiness, multipath reliability, adaptive cover traffic, formal assurance) are fragmented across separate tools (Tor, Nym, QUIC libs, ad‑hoc monitoring). Developers face:
- No unified stack combining PQC + multipath + mix routing + real telemetry.
- Operational blind spots (lack of Prometheus/OTLP observability in anonymity layers).
- Difficult mobile / WASM integration (FFI friction / multi-target builds).
- Slow iteration due to C/C++ dependencies & unsafe blocks.

## 2. Solution
NyxNet: fully modular, pure‑Rust, privacy‑first networking stack:
- Hybrid Post‑Quantum handshake (ML-KEM-768 + X25519) with rekey scheduling.
- Multipath QUIC-ready transport + adaptive path / latency / load selection.
- Mix layer with Poisson + adaptive + enhanced cover traffic & future cMix/VDF integration.
- Stream layer: extended packet format, plugin framework (CBOR frames, capability negotiation, anti-replay window, padding system, HPKE rekey scheduler).
- Observability: Prometheus metrics & OTLP traces (Tempo / Jaeger) out-of-the-box.
- Deployment: Helm charts, CLI, SDK (Rust + WASM), Mobile FFI, deterministic simulators.

## 3. Key Differentiators
| Area | NyxNet | Conventional Alternatives |
|------|--------|---------------------------|
| PQC Readiness | Hybrid ML-KEM + X25519 now | Often roadmap / absent |
| Multipath + Mix | Unified in same stack | Split across distinct projects |
| Observability | Prometheus + OTLP native | Minimal / external hacks |
| Formal + Fuzz + Conformance | Integrated (TLA+, property tests, harness) | Rarely all combined |
| Pure Rust / No unsafe | Yes (forbid) | Many mixed / C deps |
| Plugin Extensibility | CBOR framed, capability negotiation | Patch / fork heavy |
| Mobile + WASM | Feature gated, reduced deps | Frequently unsupported |

## 4. Architecture (Layered)
Core → Crypto → Transport → Mix → Stream (plugin + padding + replay) → Control / Daemon → Telemetry / SDK / CLI / FFI.
Formal + Conformance + Fuzz wrap horizontally for assurance.

## 5. Security Posture
- No `unsafe` in cryptographic / network core.
- Zeroize, hybrid KEM+DH, anti-replay windows, capability gating.
- Pure Rust cryptography only (no ring / OpenSSL). Side‑channel conscious.
- Planned: documented key lifetime & rekey triggers (1GB or 10min default target).

## 6. Performance Snapshot (Representative Targets)
> (Placeholders until automated benches inserted.)
| Metric | Target (Initial) | Method |
|--------|------------------|--------|
| Hybrid Handshake Median | < 8 ms loopback | Criterion bench (crypto) |
| Multipath Failover | < 250 ms (path loss) | Simulated link drop test |
| Cover Traffic Overhead | 0.2–0.6 utilization adaptive window | Adaptive manager stats |
| UDP Roundtrip (loopback) | < 120 µs p50 | UdpEndpoint bench |

*(Bench JSON + CI artifact pipeline WIP)*

## 7. Reliability & Assurance
- 400+ tests (unit + integration + property + benches smoke). *Exact number auto-synced planned.*
- Deterministic network simulator (`nyx-conformance`) ensures reproducible latency/reorder scenarios.
- Fuzz targets isolated (`fuzz/` workspace exclude) for security boundary.
- Formal specs (TLA+) for multipath / plugin negotiation (scope sheet forthcoming).

## 8. Operational Tooling
- Helm chart with HPA, ServiceMonitor, PDB.
- CLI: config validation, stream ops, diagnostics.
- Telemetry endpoints: `/metrics` + OTLP gRPC exporter.

## 9. Roadmap (Selected)
- QUIC full implementation (current stub when feature off).
- Enriched threat model & key lifecycle doc (SECURITY.md).
- Automated performance badge + cargo audit gating.
- Advanced anonymity metrics (entropy-based) & adaptive algorithm tuning.

## 10. License & Governance
Dual MIT / Apache-2.0. Contributor guidelines & code of conduct present. Security policy included.

## 11. Quick Start (Minimal)
```bash
cargo build --release
./target/release/nyx-daemon --config nyx.toml
./target/release/nyx-cli node info
```

## 12. Contact / Extensibility
Plugins: define CBOR header + capability ID, register in plugin registry, leverage padding + rekey hooks.

---
*(This summary is intentionally concise; see README and docs/* for full details.)*
