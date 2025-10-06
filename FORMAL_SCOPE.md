# Formal Verification Scope (Initial Draft)

> Maps specification artifacts (TLA+ / cfg scenarios / property tests) to intended safety & liveness properties. Acts as an index for auditors.

## 1. Artifacts
| File / Config | Domain | Purpose | Status |
|---------------|--------|---------|--------|
| `formal/nyx_multipath_plugin.tla` | Multipath + Plugin Frames | Ordering, replay, capability negotiation invariants | Draft model parsed |
| `formal/basic.cfg` | Core scheduling | Minimal path transitions | Executed (no counterexamples) |
| `formal/enhanced_comprehensive.cfg` | Stress multipath | Path churn, reordering window sizing | Executed (perf tuned) |
| `formal/scalability.cfg` | State growth | Memory / state bound growth | Long-run, partial completion |
| `formal/liveness_focus.cfg` | Liveness | Eventual delivery w/o deadlock | In progress |
| `formal/nyx_multipath_plugin.cfg` | Combined | Regression guard run | Periodic CI candidate |

## 2. Safety Properties (Target Set)
| ID | Property | Informal Description | Artifact Reference |
|----|----------|----------------------|-------------------|
| S1 | No Replay Acceptance | A frame with identical (conn_id, seq) accepted at most once | TLA+ invariant `NoReplayDup` |
| S2 | Capability Gate Soundness | Unsupported required capability → connection closes before data frames | Invariant `ReqCapMustClose` |
| S3 | Ordering Buffer Bounded | Reordering buffer size never exceeds configured max | Invariant `ReorderBound` |
| S4 | Rekey Atomicity | No mixed-key decrypt of a batch | Future: to be modeled |
| S5 | Anti-Replay Window Progress | Window advances or stays monotonic, never rewinds | Invariant `WindowMonotonic` |

## 3. Liveness Properties (Target Set)
| ID | Property | Informal Description | Status |
|----|----------|----------------------|--------|
| L1 | Eventual Delivery (Healthy Paths) | If at least one path remains healthy, frames are eventually delivered | Partial (liveness spec WIP) |
| L2 | Negotiation Completion | Negotiation either succeeds or terminates within bounded steps | To model |
| L3 | Rekey Completion | Rekey request yields new key state within bounded transitions | Planned |

## 4. Abstraction & Assumptions
- Cryptographic primitives abstracted as ideal (instant, authentic, no side-channels).
- Network nondeterminism: modeled via symbolic choices (delay, reorder, drop) with bounded buffers.
- Path health transitions: probabilistic in reality → nondeterministic toggles in model.
- Capability lists reduced to small representative sets to keep state tractable.

## 5. Model Checking Strategy
| Aspect | Approach |
|--------|----------|
| State Explosion | Incremental configs (basic → enhanced). Limit max paths / frame types. |
| Counterexample Analysis | `generate-verification-report.py` aggregates traces & classification. |
| Regressions | Stable subset (`basic.cfg`, `nyx_multipath_plugin.cfg`) marked for CI integration. |

## 6. Gaps / Next Steps
- Add Rekey invariants (S4) once scheduler integrated.
- Introduce entropy-based anonymity approximations (abstract counter) for cover traffic fairness.
- Automate TLC run harness with resource caps & result parsing.
- Map property tests (`nyx-conformance`) to S*/L* IDs in doc comments.

## 7. Maintenance Guidelines
- Any new multipath scheduling rule ⇒ add invariant or liveness note.
- Remove deprecated invariant IDs only with explicit CHANGELOG entry.
- Keep models minimal: push performance/throughput to simulation layer (`nyx-conformance`).

---
*Contributions: add new rows with clear, testable phrasing. Avoid ambiguous security terminology.*
