# NyxNet セキュリティガイド

**最終更新**: 2025年10月7日  
**対象バージョン**: v1.0

---

## 概要

NyxNetは、セキュリティを最優先事項として設計されたプライバシーネットワークスタックです。このドキュメントでは、セキュリティアーキテクチャ、脅威モデル、セキュリティベストプラクティス、脆弱性報告プロセスについて説明します。

---

## セキュリティ原則

### 1. メモリ安全性

**実装**: 全クレートで`#![forbid(unsafe_code)]`

Rustの所有権システムにより、以下の脆弱性クラスを排除:
- バッファオーバーフロー
- Use-After-Free
- ダブルフリー
- データ競合

**検証方法**:

```powershell
# unsafe_code使用チェック
cargo clippy --workspace -- -D unsafe-code
```

### 2. ゼロC/C++依存

**理由**: C/C++ライブラリの脆弱性を継承しない

**実装**:
- Pure Rust暗号化: `ml-kem`, `x25519-dalek`, `chacha20poly1305`
- Pure Go TLS: `crypto/tls`（nyx-http-proxy）
- ring、OpenSSL、libsodiumなどのC依存を排除

**検証方法**:

```bash
# C/C++依存チェック
cargo tree | grep -i "openssl\|ring\|libsodium"
# 結果: マッチなし（期待値）
```

### 3. 最小権限の原則

**実装**:
- デーモンは非特権ユーザーで実行
- 必要最小限のシステムコール使用
- サンドボックス化（Linux: seccomp、Windows: AppContainer対応検討中）

### 4. デフォルトセキュア

**設定デフォルト**:
- ポスト量子暗号: 有効
- リプレイ攻撃保護: 有効
- レート制限: 有効
- 暗号化: 常時有効（無効化不可）

---

## 脅威モデル

### 想定脅威アクター

| アクター | 能力 | 対策 |
|---------|------|------|
| **パッシブ盗聴者** | ネットワークトラフィック監視 | Sphinx暗号化、カバートラフィック |
| **アクティブ攻撃者** | パケット改ざん、リプレイ | AEAD認証、タイムスタンプナンス |
| **量子コンピュータ** | 公開鍵暗号の解読 | ハイブリッドPQ暗号（ML-KEM + X25519） |
| **トラフィック分析** | 統計的パターン分析 | カバートラフィック、タイミング曖昧化 |
| **悪意のあるミックスノード** | 一部ノードの侵害 | 3ホップ最小、エンドツーエンド暗号化 |

### 想定攻撃シナリオ

#### 1. トラフィック分析攻撃

**攻撃**: ネットワーク監視によるユーザー識別

**対策**:
- Poisson分布に基づくカバートラフィック生成
- パケットサイズの正規化
- タイミング曖昧化（遅延挿入）

**残存リスク**: 長期間の大規模監視による統計的相関（部分的対策）

#### 2. リプレイ攻撃

**攻撃**: 過去のパケットの再送信

**対策**:
- タイムスタンプベースのナンス検証（±5分許容）
- Bloomフィルタによる重複検出（10万エントリ）
- セッションIDの暗号学的ランダム性

**実装**: `nyx-core/src/security.rs`

```rust
pub struct ReplayProtection {
    bloom: BloomFilter,
    window: Duration, // 5分
}

impl ReplayProtection {
    pub fn check_nonce(&self, nonce: &Nonce) -> Result<()> {
        if self.bloom.contains(nonce) {
            return Err(Error::ReplayDetected);
        }
        // タイムスタンプ検証
        if nonce.timestamp().elapsed() > self.window {
            return Err(Error::NonceExpired);
        }
        Ok(())
    }
}
```

#### 3. タイミング攻撃

**攻撃**: 暗号化操作の実行時間差からの秘密情報推測

**対策**:
- 定数時間比較（`subtle` crate使用）
- 暗号化ライブラリの定数時間実装
- タイミング曖昧化（ランダム遅延）

**実装例**:

```rust
use subtle::ConstantTimeEq;

// 定数時間MAC検証
fn verify_mac(expected: &[u8], actual: &[u8]) -> bool {
    expected.ct_eq(actual).into()
}
```

#### 4. サービス拒否攻撃（DoS）

**攻撃**: リソース枯渇による可用性低下

**対策**:
- レート制限: 100 req/s（設定可能）
- 接続数上限: 1000（設定可能）
- メモリ使用量制限: 1GB（設定可能）
- CPU使用率監視: 80%超過でアラート

**実装**: `nyx-core/src/security.rs`

```rust
pub struct RateLimiter {
    max_rate: u32, // requests per second
    buckets: DashMap<PeerId, TokenBucket>,
}
```

---

## 暗号化アーキテクチャ

### レイヤー別暗号化

```
┌──────────────────────────────────────────────────┐
│  Application Data (Plaintext)                    │
└──────────────────┬───────────────────────────────┘
                   ▼
┌──────────────────────────────────────────────────┐
│  Layer 3: End-to-End Encryption                  │
│  ChaCha20Poly1305 (Session Key)                  │
└──────────────────┬───────────────────────────────┘
                   ▼
┌──────────────────────────────────────────────────┐
│  Layer 2: Sphinx Onion Encryption                │
│  3 Layers (Mix1, Mix2, Mix3)                     │
└──────────────────┬───────────────────────────────┘
                   ▼
┌──────────────────────────────────────────────────┐
│  Layer 1: QUIC Transport Encryption              │
│  TLS 1.3-like Handshake                          │
└──────────────────────────────────────────────────┘
```

### ハイブリッドポスト量子暗号

#### アルゴリズム選択理由

| アルゴリズム | 用途 | 理由 |
|------------|------|------|
| **ML-KEM-768** | ポスト量子KEM | NIST標準化済み、Security Level 3 |
| **X25519** | 古典的ECDH | 高速、実績あり、ハイブリッド用 |
| **ChaCha20Poly1305** | AEAD暗号 | ソフトウェア実装高速、サイドチャネル耐性 |
| **BLAKE3** | ハッシュ | 超高速、並列化対応 |

#### 鍵サイズ

| 鍵 | サイズ | 備考 |
|----|-------|------|
| ML-KEM-768 公開鍵 | 1184バイト | |
| ML-KEM-768 秘密鍵 | 2400バイト | zeroize対応 |
| X25519 公開鍵 | 32バイト | |
| X25519 秘密鍵 | 32バイト | zeroize対応 |
| 共有秘密 | 32バイト | HKDF入力 |
| セッション鍵 | 32バイト | ChaCha20用 |

#### 鍵導出（HKDF）

```
Input Key Material (IKM) = ML-KEM共有秘密 || X25519共有秘密
Salt = None (all-zero)
Info = "nyx-hybrid-v1"

PRK = HMAC-SHA256(Salt, IKM)
Session Key = HKDF-Expand(PRK, Info, 32 bytes)
```

**実装**: `nyx-crypto/src/hybrid_handshake.rs`

---

## 鍵管理

### 鍵ライフサイクル

```
生成 → 保存 → 使用 → ローテーション → 破棄
 ↓      ↓      ↓         ↓          ↓
OsRng  暗号化  メモリ    定期実行    zeroize
```

### 鍵ストレージ

#### 一時鍵（Ephemeral Keys）

- **保存場所**: メモリのみ（永続化しない）
- **ライフタイム**: セッション期間のみ
- **破棄**: `ZeroizeOnDrop` trait自動適用

```rust
#[derive(ZeroizeOnDrop)]
struct EphemeralKey([u8; 32]);
```

#### 長期鍵（Long-term Keys）

- **保存場所**: 暗号化されたファイル（将来実装予定）
- **暗号化**: AES-256-GCM（パスワード派生鍵）
- **権限**: 所有者のみ読み取り（Unix: 0600、Windows: ACL）

**注**: 現在は各起動時に鍵生成（ステートレス設計）

### 鍵ローテーション

**デフォルト間隔**: 3600秒（1時間）

```toml
# nyx.toml
[crypto]
key_rotation_interval = 3600  # seconds
```

**実装**: `nyx-crypto/src/session.rs`

---

## 認証と認可

### ノード認証

**方式**: 公開鍵ベース認証

1. 各ノードは起動時に鍵ペア生成
2. ノードIDは公開鍵のハッシュ（libp2p互換）
3. 通信時に秘密鍵で署名、公開鍵で検証

### API認証

#### gRPC API

**現状**: 認証なし（localhost binding前提）

**将来計画**: トークンベース認証

```protobuf
message AuthRequest {
  string token = 1;  // JWT or static token
}
```

#### JSON-RPC API（IPC）

**現状**: Unix socketファイル権限による制限

**権限**: 所有者のみ（Unix: 0700、Windows: named pipe ACL）

---

## セキュリティ設定

### 推奨設定（本番環境）

```toml
# nyx.toml - Production Security Configuration

[security]
# 接続制限
max_connections = 1000
connection_timeout = 30  # seconds
max_frame_size = 8388608  # 8MB

# レート制限
rate_limit_requests = 100  # per second
rate_limit_bytes = 10485760  # 10MB per second

# リプレイ保護
replay_window = 300  # 5 minutes
bloom_filter_size = 100000  # entries

[crypto]
# ポスト量子暗号（必須）
pq_enabled = true

# 鍵ローテーション
key_rotation_interval = 3600  # 1 hour

# セッションタイムアウト
session_timeout = 7200  # 2 hours

[network]
# Bind address（本番環境）
bind_addr = "0.0.0.0:43300"

# IPv6有効化
ipv6_enabled = true

# 開発モード無効化
development = false
```

### 最小権限設定（制限環境）

```toml
[security]
max_connections = 100
rate_limit_requests = 10
max_frame_size = 1048576  # 1MB

[crypto]
key_rotation_interval = 1800  # 30 minutes
```

---

## 監査ログ

### ロギング設定

#### セキュリティイベント

記録対象:
- 認証失敗
- レート制限超過
- リプレイ攻撃検出
- 異常な接続パターン

**ログ形式**: JSON（構造化ログ）

```json
{
  "timestamp": "2025-10-07T12:34:56.789Z",
  "level": "WARN",
  "event": "replay_detected",
  "peer_id": "12D3KooW...",
  "nonce": "abc123...",
  "details": "Duplicate nonce detected"
}
```

#### ログ設定

```toml
# nyx.toml
log_level = "info"  # error, warn, info, debug, trace
log_format = "json"  # json, pretty, compact
```

#### PowerShell

```powershell
# ログファイル確認
Get-Content nyx-daemon.log | ConvertFrom-Json | Where-Object { $_.event -eq "replay_detected" }
```

#### bash

```bash
# セキュリティイベント抽出
jq 'select(.event == "replay_detected")' nyx-daemon.log
```

---

## 脆弱性管理

### 依存関係監査

#### 自動スキャン

```powershell
# cargo-auditインストール
cargo install cargo-audit

# 脆弱性スキャン
cargo audit

# Advisory DB更新
cargo audit fetch
```

#### CI/CD統合

GitHub Actions（`.github/workflows/security.yml`）:
- 日次スキャン
- PR時スキャン
- 脆弱性検出時にIssue自動作成

### 脆弱性報告プロセス

#### 報告方法

1. **GitHub Security Advisories** （推奨）
   - https://github.com/SeleniaProject/Nyx/security/advisories/new

2. **Email** （代替手段）
   - ※実際のメールアドレスは`SECURITY.md`参照

#### 報告テンプレート

```markdown
## 脆弱性詳細

### 影響範囲
- コンポーネント: (例: nyx-crypto)
- 深刻度: (Critical/High/Medium/Low)

### 再現手順
1. ...
2. ...

### 影響
- データ漏洩/DoS/権限昇格 など

### 提案される対策
- ...
```

#### レスポンスSLA

| フェーズ | 目標時間 |
|---------|---------|
| 初期応答 | 24時間以内 |
| 深刻度評価 | 72時間以内 |
| パッチ開発 | 7-30日（深刻度による） |
| パッチリリース | 開発完了後24時間 |
| 公開ディスクロージャ | パッチリリース後90日 |

### CVSS評価

CVSS v3.1を使用して深刻度評価:

| スコア | 深刻度 | 対応優先度 |
|-------|-------|----------|
| 9.0-10.0 | Critical | 即時 |
| 7.0-8.9 | High | 7日以内 |
| 4.0-6.9 | Medium | 30日以内 |
| 0.1-3.9 | Low | 次回リリース |

---

## セキュリティベストプラクティス

### デプロイメント

#### ネットワーク分離

```yaml
# Kubernetes NetworkPolicy例
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: nyx-network-policy
spec:
  podSelector:
    matchLabels:
      app: nyx-daemon
  policyTypes:
  - Ingress
  - Egress
  ingress:
  - from:
    - podSelector:
        matchLabels:
          app: nyx-client
    ports:
    - protocol: TCP
      port: 50051
```

#### コンテナセキュリティ

Dockerfile推奨設定:

```dockerfile
FROM rust:1.75-slim AS builder
# ... build steps ...

FROM gcr.io/distroless/cc-debian12
# 非特権ユーザー
USER 65534:65534
# 読み取り専用ルートFS
# （実装時にはvolume設定必要）
COPY --from=builder /app/nyx-daemon /usr/local/bin/
ENTRYPOINT ["/usr/local/bin/nyx-daemon"]
```

#### ファイアウォール設定

```bash
# iptables（Linux）
sudo iptables -A INPUT -p tcp --dport 43300 -j ACCEPT  # Nyx protocol
sudo iptables -A INPUT -p tcp --dport 50051 -j DROP    # gRPC（内部のみ）

# UFW（Ubuntu）
sudo ufw allow 43300/tcp
sudo ufw deny 50051/tcp
```

```powershell
# Windows Firewall
New-NetFirewallRule -DisplayName "Nyx Protocol" -Direction Inbound -LocalPort 43300 -Protocol TCP -Action Allow
New-NetFirewallRule -DisplayName "Block gRPC External" -Direction Inbound -LocalPort 50051 -Protocol TCP -Action Block
```

### 運用

#### 定期セキュリティタスク

| タスク | 頻度 | コマンド |
|-------|------|---------|
| 脆弱性スキャン | 週次 | `cargo audit` |
| ログ分析 | 日次 | `jq 'select(.level=="WARN")' nyx.log` |
| 設定レビュー | 月次 | 手動確認 |
| 鍵ローテーション | 自動 | 設定で制御 |

#### セキュリティ監視

Prometheusメトリクス監視:

```promql
# 認証失敗率
rate(nyx_auth_failures_total[5m]) > 10

# 異常な接続数
nyx_active_connections > 800

# メモリリーク検出
rate(nyx_memory_usage_bytes[1h]) > 0.1
```

---

## セキュリティチェックリスト

### 開発時

- [ ] `unsafe`コード使用なし（`#![forbid(unsafe_code)]`）
- [ ] 全入力データのバリデーション
- [ ] エラーメッセージに機密情報を含まない
- [ ] 定数時間比較使用（パスワード、MAC）
- [ ] 乱数生成に`OsRng`使用
- [ ] 秘密鍵に`ZeroizeOnDrop`適用
- [ ] レート制限実装
- [ ] ログに機密情報を記録しない

### デプロイ前

- [ ] 依存関係脆弱性スキャン（`cargo audit`）
- [ ] セキュリティ設定レビュー
- [ ] ファイアウォールルール設定
- [ ] TLS証明書有効期限確認（該当する場合）
- [ ] 非特権ユーザーで実行
- [ ] ログ監視設定
- [ ] バックアップ設定

### 運用中

- [ ] 定期的な脆弱性スキャン
- [ ] ログ分析（異常検知）
- [ ] パッチ適用（30日以内）
- [ ] インシデント対応計画準備
- [ ] セキュリティ監査（年次）

---

## 既知の制約とリスク

### 制約1: トラフィック分析耐性の限界

**説明**: 長期間の大規模監視による統計的相関は完全には防げません。

**軽減策**:
- カバートラフィック生成
- 複数パスの使用
- タイミング曖昧化

**残存リスク**: 低（実用的な攻撃は困難）

### 制約2: 悪意のある過半数ノード

**説明**: 3ホップ中2ノード以上が侵害された場合、匿名性が低下します。

**軽減策**:
- エンドツーエンド暗号化（アプリケーション層）
- 信頼できるノードの選択

**残存リスク**: 中（分散信頼モデルの根本的制約）

### 制約3: サイドチャネル攻撃

**説明**: タイミング、電力消費などの物理的漏洩。

**軽減策**:
- 定数時間アルゴリズム使用
- タイミング曖昧化

**残存リスク**: 低（ソフトウェア対策済み、ハードウェア攻撃は想定外）

---

## 参考資料

### 標準規格

- **NIST FIPS 203**: ML-KEM（Module-Lattice-Based Key-Encapsulation Mechanism）
- **RFC 7539**: ChaCha20とPoly1305
- **RFC 7748**: X25519楕円曲線Diffie-Hellman
- **RFC 5869**: HKDF（HMAC-based Key Derivation Function）

### 関連論文

- Sphinx Mix Network: "Sphinx: A Compact and Provably Secure Mix Format" (Danezis & Goldberg, 2009)
- cMix: "cMix: Mixing with Minimal Real-Time Asymmetric Cryptographic Operations" (Chaum et al., 2016)

---

## 補足: 推測箇所の明示

以下の情報は既存コード・標準的なセキュリティプラクティスから合理的に推測しています:

- **脆弱性報告のメールアドレス**: 実際は`SECURITY.md`参照
- **一部のPrometheusメトリクス名**: 実装から推測した命名規則
- **Kubernetesマニフェスト例**: 典型的な設定を記載
- **残存リスク評価**: 一般的な脅威分析に基づく推測

正確な情報は、実際のコードと設定ファイルを確認してください。
