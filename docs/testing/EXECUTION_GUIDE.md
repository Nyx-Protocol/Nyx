# NyxNet 包括的テスト実行ガイド

## 前提条件

### 必須ツール
```powershell
# Rust toolchain (既にインストール済み想定)
rustc --version  # 1.70.0以降推奨

# テストツール
cargo install cargo-nextest  # 並列テスト実行
cargo install cargo-tarpaulin  # カバレッジ測定 (Linux/WSL)
# または
cargo install cargo-llvm-cov  # LLVMベースカバレッジ (全OS対応)

# プロパティベーステスト
# proptest は Cargo.toml に既存

# ベンチマーク
# criterion は workspace依存に含まれる
```

### 環境変数設定
```powershell
# テスト用タイムアウト延長
$env:RUST_TEST_THREADS = "4"  # 並列数制御
$env:RUST_BACKTRACE = "1"     # エラー詳細表示

# 決定論的テスト用固定シード
$env:NYX_TEST_SEED = "42"

# ネットワークテスト無効化 (外部依存回避)
$env:NYX_SKIP_NETWORK_TESTS = "1"
```

---

## テスト実行手順

### 1. 単体テスト (Unit Tests)

#### 全クレートのテスト実行
```powershell
# 標準のcargoテスト
cargo test --workspace

# nextest使用 (推奨: 高速・詳細レポート)
cargo nextest run --workspace
```

#### 特定クレートのみ
```powershell
# nyx-cryptoのみ
cargo test -p nyx-crypto

# 新規追加テスト確認
cargo test -p nyx-crypto --test hybrid_pq_comprehensive
cargo test -p nyx-crypto --test hpke_rfc9180_compliance
```

#### テスト名フィルタ
```powershell
# "handshake"を含むテストのみ
cargo test handshake

# 正規表現マッチ
cargo nextest run -E 'test(crypto)'
```

### 2. 統合テスト (Integration Tests)

```powershell
# tests/クレートの実行
cargo test -p tests

# E2Eハンドシェイクテスト
cargo test -p tests --test e2e_handshake -- --test-threads=1

# マルチパス統合
cargo test -p tests --test advanced_integration
```

### 3. プロパティベーステスト

```powershell
# proptest実行 (デフォルト256ケース)
cargo test --features proptest

# ケース数増加 (CI用)
$env:PROPTEST_CASES = "10000"
cargo test property_tests
```

### 4. ベンチマーク (Criterion)

```powershell
# 全ベンチマーク実行
cargo bench --workspace

# 特定ベンチマーク
cargo bench -p nyx-core --bench security_scalability_benchmark

# 結果比較 (ベースライン保存)
cargo bench --workspace -- --save-baseline main
# 変更後
cargo bench --workspace -- --baseline main
```

### 5. ファズテスト (Fuzzing)

```powershell
# cargo-fuzzインストール
cargo install cargo-fuzz

# ファズターゲット実行 (60秒)
cd fuzz
cargo fuzz run extended_packet -- -max_total_time=60

# 既存コーパス再生
cargo fuzz run capability_negotiation corpus/capability_negotiation/
```

---

## カバレッジ測定

### 方法1: cargo-tarpaulin (Linux/WSL推奨)

```powershell
# 全体カバレッジ
cargo tarpaulin --workspace --out Html --output-dir coverage

# 閾値チェック (85%以上)
cargo tarpaulin --workspace --fail-under 85
```

### 方法2: cargo-llvm-cov (全OS対応)

```powershell
# インストール
cargo install cargo-llvm-cov

# HTML レポート生成
cargo llvm-cov --workspace --html

# JSON出力 (CI連携用)
cargo llvm-cov --workspace --json --output-path coverage.json

# 特定クレートのみ
cargo llvm-cov -p nyx-crypto -p nyx-transport --html
```

### カバレッジ目標
- **行カバレッジ**: ≥85%
- **分岐カバレッジ**: ≥80%
- **クリティカルパス**: 100% (crypto, security)

---

## CI/CD統合

### GitHub Actions ワークフロー例

```yaml
# .github/workflows/comprehensive-tests.yml (抜粋)
name: Comprehensive Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: stable
          
      - name: Install nextest
        run: cargo install cargo-nextest
      
      - name: Run unit tests
        run: cargo nextest run --workspace --no-fail-fast
      
      - name: Run integration tests
        run: cargo test -p tests --no-fail-fast
      
      - name: Generate coverage
        run: |
          cargo install cargo-llvm-cov
          cargo llvm-cov --workspace --json --output-path coverage.json
      
      - name: Upload coverage
        uses: codecov/codecov-action@v3
        with:
          files: coverage.json
```

---

## トラブルシューティング

### テストがハングする
```powershell
# タイムアウト設定
cargo test -- --test-threads=1 --nocapture

# 特定のテストをスキップ
cargo test -- --skip slow_network_test
```

### メモリ不足エラー
```powershell
# 並列数削減
$env:RUST_TEST_THREADS = "1"
cargo test
```

### 非決定的テスト失敗
```powershell
# 固定シード設定
$env:NYX_TEST_SEED = "12345"
cargo test

# 100回実行してフレーク検出
for ($i=1; $i -le 100; $i++) { 
    cargo test target_test_name 
    if ($LASTEXITCODE -ne 0) { 
        Write-Host "Failed at iteration $i" 
        break 
    } 
}
```

---

## 継続的テスト戦略

### 開発フロー
1. **機能開発前**: 関連テスト確認 `cargo test -p <crate>`
2. **開発中**: TDD (Red-Green-Refactor)
3. **コミット前**: `cargo test --workspace`
4. **PR作成時**: CI全テスト + カバレッジチェック
5. **マージ後**: ベンチマーク回帰検証

### 定期実行 (推奨)
- **毎コミット**: Unit + Integration
- **毎PR**: + Property-based + Security
- **毎日**: + Fuzzing (8時間)
- **毎週**: + Stress + Performance
- **リリース前**: + TLA+ モデル検証 + 手動監査

---

## 品質ゲート基準

### 必須条件 (CI合格)
- ✅ 全テスト成功 (`cargo test --workspace`)
- ✅ カバレッジ ≥ 85% (行)、≥ 80% (分岐)
- ✅ Clippy警告なし (`cargo clippy --workspace -- -D warnings`)
- ✅ フォーマット準拠 (`cargo fmt --all -- --check`)
- ✅ セキュリティ監査 (`cargo audit`)

### 推奨条件 (リリース前)
- 🔸 ベンチマーク回帰 < 5%
- 🔸 Fuzzing 24時間クラッシュなし
- 🔸 Property-based 10,000ケース成功
- 🔸 TLA+ モデルチェック完了

---

## 参考リンク

- [Cargo Test Book](https://doc.rust-lang.org/cargo/commands/cargo-test.html)
- [nextest](https://nexte.st/)
- [proptest](https://proptest-rs.github.io/proptest/intro.html)
- [Criterion.rs](https://bheisler.github.io/criterion.rs/book/)
- [cargo-llvm-cov](https://github.com/taiki-e/cargo-llvm-cov)
