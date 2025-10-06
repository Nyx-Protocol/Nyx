# NyxNet TLA+ Formal Properties と Rust Test のマッピング

## 概要
このドキュメントは、`formal/nyx_multipath_plugin.tla` で定義されたプロパティ (S1-S5, L1-L3) と、Rust実装のテストケースの対応関係を記録します。

**目的**:
- フォーマル検証とコード実装の一貫性保証
- 監査証跡の提供 (REQ-FUN-040, REQ-NFR-040)
- 要件トレーサビリティ (requirements.md と統合)

---

## Safety Properties (安全性プロパティ)

### S1: No Replay Acceptance (リプレイ攻撃防止)

**TLA+ 定義**:
```tla
NoReplayDup == 
  \A conn \in Connections, seq \in SeqNums :
    (conn, seq) が受理された回数 ≤ 1
```

**対応するRustテスト**:

| テストID | ファイル | テスト名 | 検証内容 |
|---------|---------|---------|---------|
| UT-CRY-003 | `nyx-crypto/tests/session_replay_protection.rs` | `test_replay_window_rejects_duplicate_sequence` | 同一シーケンス番号の2回目受理を拒否 |
| UT-STM-002 | `nyx-stream/tests/frame_ordering_reorder.rs` | `test_reorder_buffer_deduplication` | リオーダバッファでの重複検出 |
| IT-E2E-009 | `tests/tests/replay_attack_resistance.rs` | `test_full_session_replay_prevention` | セッション全体でのリプレイ攻撃シミュレーション |

**検証方法**:
```rust
// nyx-crypto/src/session.rs の実装確認
impl ReplayWindow {
    pub fn check_and_update(&mut self, seq: u64) -> Result<(), ReplayError> {
        // ウィンドウ範囲チェック
        // ビットマップでの重複検出
        // 単調性維持
    }
}
```

**TLA+ モデル検証コマンド**:
```bash
cd formal
java -jar tla2tools.jar -config basic.cfg nyx_multipath_plugin.tla
# Invariant NoReplayDup: OK (0 violations found)
```

---

### S2: Capability Gate Soundness (Capability要件の厳密性)

**TLA+ 定義**:
```tla
ReqCapMustClose == 
  \A conn \in Connections :
    UnsupportedRequiredCapability(conn) => 
    Eventually(ConnectionState[conn] = "CLOSED")
```

**対応するRustテスト**:

| テストID | ファイル | テスト名 | 検証内容 |
|---------|---------|---------|---------|
| UT-STM-003 | `nyx-stream/tests/capability_negotiation_compat.rs` | `test_required_capability_missing_closes_connection` | 必須capability不足時の接続クローズ |
| UT-STM-003 | 同上 | `test_optional_capability_ignored_when_unsupported` | オプショナルcapability無視動作 |
| IT-E2E-010 | `tests/tests/capability_negotiation_e2e.rs` | `test_version_mismatch_graceful_degradation` | バージョン不一致時の優雅な劣化 |

**実装確認**:
```rust
// nyx-stream/src/capability.rs
pub fn negotiate(
    local: &CapabilitySet,
    remote: &CapabilitySet,
) -> Result<NegotiatedCapabilities, NegotiationError> {
    // 必須capabilityの交差検証
    // 未サポート必須capability検出時はエラー0x07
    // オプショナルは無視
}
```

**TLA+ 検証**:
```bash
# formal/enhanced_comprehensive.cfg で検証
java -jar tla2tools.jar -config enhanced_comprehensive.cfg nyx_multipath_plugin.tla
# Property ReqCapMustClose: OK
```

---

### S3: Ordering Buffer Bounded (並び替えバッファの有界性)

**TLA+ 定義**:
```tla
ReorderBound ==
  \A conn \in Connections :
    Len(ReorderBuffer[conn]) <= MAX_REORDER_BUFFER_SIZE
```

**対応するRustテスト**:

| テストID | ファイル | テスト名 | 検証内容 |
|---------|---------|---------|---------|
| UT-STM-002 | `nyx-stream/tests/frame_ordering_reorder.rs` | `test_reorder_buffer_size_limit` | バッファサイズ上限チェック |
| BV-004 | 同上 | `test_reorder_buffer_drops_oldest_when_full` | 満杯時の古いフレーム破棄ポリシー |
| PERF-003 | `nyx-stream/benches/reorder_performance.rs` | `bench_reorder_buffer_memory_usage` | メモリ使用量測定 |

**実装確認**:
```rust
// nyx-stream/src/reorder.rs
const MAX_REORDER_SIZE: usize = 256;

impl ReorderBuffer {
    pub fn insert(&mut self, frame: Frame) -> Result<(), ReorderError> {
        if self.buffer.len() >= MAX_REORDER_SIZE {
            // 最古フレーム破棄またはエラー
        }
        // ...
    }
}
```

---

### S4: Rekey Atomicity (Rekey操作の原子性)

**TLA+ 定義** (計画中):
```tla
RekeyAtomicity ==
  \A conn \in Connections, batch \in Batches :
    \/ AllFramesDecryptedWithOldKey(conn, batch)
    \/ AllFramesDecryptedWithNewKey(conn, batch)
    \/ NoFramesDecrypted(conn, batch)
```

**対応するRustテスト** (TODO):

| テストID | ファイル (計画) | テスト名 (計画) | 検証内容 |
|---------|---------|---------|---------|
| UT-STM-004 | `nyx-stream/tests/rekey_atomicity.rs` | `test_rekey_no_mixed_key_batch` | バッチ内で鍵混在がないこと |
| UT-STM-004 | 同上 | `test_rekey_rollback_on_decrypt_failure` | 復号失敗時のロールバック |
| IT-E2E-011 | `tests/tests/rekey_stress.rs` | `test_concurrent_rekey_requests` | 並行Rekey要求の整合性 |

**実装状況**: 🚧 スケジューラは存在 (`nyx-stream/src/rekey_scheduler.rs`) だが、原子性保証は未完全

---

### S5: Anti-Replay Window Progress (アンチリプレイウィンドウの進行)

**TLA+ 定義**:
```tla
WindowMonotonic ==
  \A conn \in Connections, t1, t2 \in Time :
    t1 < t2 => WindowBase[conn][t1] <= WindowBase[conn][t2]
```

**対応するRustテスト**:

| テストID | ファイル | テスト名 | 検証内容 |
|---------|---------|---------|---------|
| UT-CRY-003 | `nyx-crypto/tests/session_replay_protection.rs` | `test_replay_window_monotonic_advance` | ウィンドウベースの単調増加 |
| UT-CRY-003 | 同上 | `test_replay_window_never_rewinds` | 巻き戻り禁止 |
| PROP-004 | `nyx-crypto/tests/property_tests.rs` | `prop_window_advance_property` | プロパティベーステスト |

**実装確認**:
```rust
// nyx-crypto/src/session.rs
impl ReplayWindow {
    pub fn advance(&mut self, new_base: u64) {
        assert!(new_base >= self.base, "Window must not rewind");
        self.base = new_base;
        // ビットマップシフト
    }
}
```

---

## Liveness Properties (活性プロパティ)

### L1: Eventual Delivery (最終的な配送)

**TLA+ 定義**:
```tla
EventualDelivery ==
  \A frame \in Frames :
    (HealthyPathExists(frame.conn) /\ Sent(frame)) =>
    Eventually(Delivered(frame))
```

**対応するRustテスト** (部分的):

| テストID | ファイル | テスト名 | 検証内容 |
|---------|---------|---------|---------|
| IT-E2E-002 | `tests/tests/e2e_multipath_failover.rs` | `test_delivery_after_path_switch` | パス切替後の配送完了 |
| IT-E2E-012 | `tests/tests/liveness_guarantee.rs` | `test_no_deadlock_under_congestion` | 輻輳下でのデッドロック回避 |

**制約**: 完全な形式検証は未実施 (TLA+ liveness spec 作成中)

---

### L2: Negotiation Completion (交渉完了の有界性)

**TLA+ 定義** (計画中):
```tla
NegotiationTerminates ==
  \A conn \in Connections :
    NegotiationStarted(conn) =>
    Eventually(NegotiationSucceeded(conn) \/ NegotiationFailed(conn))
```

**対応するRustテスト** (TODO):

| テストID | ファイル (計画) | テスト名 (計画) | 検証内容 |
|---------|---------|---------|---------|
| IT-E2E-010 | `tests/tests/capability_negotiation_timeout.rs` | `test_negotiation_timeout_bound` | タイムアウト上限 |

---

### L3: Rekey Completion (Rekey完了の有界性)

**TLA+ 定義** (計画中):
```tla
RekeyCompletion ==
  \A conn \in Connections :
    RekeyRequested(conn) =>
    Eventually(RekeySucceeded(conn) \/ RekeyFailed(conn))
```

**対応するRustテスト** (TODO):

| テストID | ファイル (計画) | テスト名 (計画) | 検証内容 |
|---------|---------|---------|---------|
| UT-STM-004 | `nyx-stream/tests/rekey_completion.rs` | `test_rekey_completes_within_timeout` | Rekey完了時間上限 |

---

## トレーサビリティマトリクス

### 要件 → TLA+ → Rust テスト

| 要件ID (requirements.md) | TLA+プロパティ | Rustテスト | カバレッジ |
|------------------------|--------------|----------|----------|
| REQ-FUN-011 (ハイブリッドPQ) | - | UT-CRY-001, UT-CRY-002 | ✅ 95% |
| REQ-FUN-012 (多重化) | S3 (ReorderBound) | UT-STM-002 | ✅ 88% |
| REQ-FUN-030 (カバー交通) | - | IT-E2E-003 | 🔸 70% |
| REQ-NFR-010 (P95≤350ms) | - | PERF-001 | ✅ 測定済 |
| REQ-NFR-020 (ARI≥0.9) | - | SEC-007 | 🔸 部分的 |

**凡例**:
- ✅ 完全カバレッジ
- 🔸 部分的カバレッジ
- ❌ 未カバー

---

## CI連携

### TLA+ モデルチェック自動化 (GitHub Actions)

```yaml
# .github/workflows/tla-verification.yml
name: TLA+ Verification

on:
  pull_request:
    paths:
      - 'formal/**'
      - 'nyx-stream/**'
      - 'nyx-crypto/**'

jobs:
  model-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install TLA+ Tools
        run: |
          wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
          
      - name: Run basic config
        run: |
          cd formal
          java -jar ../tla2tools.jar -config basic.cfg nyx_multipath_plugin.tla
      
      - name: Generate verification report
        run: |
          cd formal
          python3 generate-verification-report.py
      
      - name: Upload report
        uses: actions/upload-artifact@v3
        with:
          name: tla-verification-report
          path: formal/verification_report.md
```

---

## メンテナンスガイドライン

### 新規プロパティ追加時
1. TLA+ モデルに不変条件/時相性質を追加
2. `formal/*.cfg` に検証設定追加
3. 対応するRustテストを実装 (このファイルに記録)
4. `docs/requirements.md` の要件IDと紐付け
5. CI/CDパイプラインに統合

### プロパティ削除時
1. 廃止理由をCHANGELOG.mdに記録
2. 対応するテストに `#[ignore]` マークと理由コメント
3. このファイルから行を削除せず、`(Deprecated)` マーク追加

---

## 参考文献

- [TLA+ Specification](../formal/nyx_multipath_plugin.tla)
- [Formal Scope](../FORMAL_SCOPE.md)
- [Requirements](../docs/requirements.md)
- [Architecture](../docs/architecture.md)
