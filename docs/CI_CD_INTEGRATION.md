# CI/CD統合ガイド

このドキュメントでは、NyxNetプロジェクトのパフォーマンスベンチマークをCI/CDパイプラインに統合する方法を説明します。

## 📋 目次

1. [GitHub Actions統合](#github-actions統合)
2. [ベンチマーク実行](#ベンチマーク実行)
3. [パフォーマンス回帰検出](#パフォーマンス回帰検出)
4. [Tor比較ベンチマーク](#tor比較ベンチマーク)
5. [結果の解釈](#結果の解釈)

---

## GitHub Actions統合

### ワークフローファイル

`.github/workflows/benchmarks.yml` は以下のジョブを含んでいます:

#### 1. **Application Benchmarks**
- **トリガー**: Push、PR、スケジュール(毎週月曜日)
- **プラットフォーム**: Ubuntu、Windows、macOS
- **出力**: Criterion HTMLレポート、ベンチマーク結果テキスト

```yaml
# 手動実行
gh workflow run benchmarks.yml
```

#### 2. **Tor Comparison** (Linuxのみ)
- **トリガー**: 手動実行のみ(`workflow_dispatch`)
- **実行条件**: `run_comparison=true`
- **所要時間**: 約15-20分

```bash
# Tor比較を含めて実行
gh workflow run benchmarks.yml -f run_comparison=true
```

#### 3. **Performance Regression Check**
- **トリガー**: プルリクエスト
- **機能**: PRのパフォーマンスをmainブランチと比較
- **出力**: 回帰分析レポート、PRコメント

#### 4. **Benchmark Summary**
- **トリガー**: ベンチマークジョブ完了後
- **機能**: 全プラットフォームの結果を集約

---

## ベンチマーク実行

### ローカル実行

#### 基本的なベンチマーク

```bash
# 全ベンチマーク実行
cargo bench --package nyx-benchmarks

# 特定のベンチマーク実行
cargo bench --package nyx-benchmarks -- file_transfer
cargo bench --package nyx-benchmarks -- messaging
cargo bench --package nyx-benchmarks -- video_streaming
```

#### HTMLレポート表示

```bash
# Criterion HTMLレポートを生成
cargo bench --package nyx-benchmarks

# レポートを開く
# Windows
start target/criterion/report/index.html

# Linux
xdg-open target/criterion/report/index.html

# macOS
open target/criterion/report/index.html
```

### CI環境での実行

#### GitHub Actions

```yaml
- name: Run benchmarks
  run: cargo bench --package nyx-benchmarks -- --output-format bencher
```

#### GitLab CI

```yaml
benchmark:
  stage: test
  script:
    - cargo bench --package nyx-benchmarks
  artifacts:
    paths:
      - target/criterion/
    expire_in: 1 week
```

#### Jenkins

```groovy
stage('Benchmark') {
    steps {
        sh 'cargo bench --package nyx-benchmarks'
        publishHTML([
            reportDir: 'target/criterion/report',
            reportFiles: 'index.html',
            reportName: 'Benchmark Report'
        ])
    }
}
```

---

## パフォーマンス回帰検出

### Critcmpを使用した比較

#### インストール

```bash
cargo install critcmp
```

#### ベースラインの保存

```bash
# 現在のmainブランチをベースラインとして保存
git checkout main
cargo bench --package nyx-benchmarks -- --save-baseline main

# 機能ブランチでベンチマーク実行
git checkout feature-branch
cargo bench --package nyx-benchmarks -- --save-baseline feature
```

#### 結果の比較

```bash
# 2つのベースラインを比較
critcmp main feature

# 例: 出力
# group                         main                                   feature
# -----                         ----                                   -------
# file_transfer/1MB             1.00     12.1±0.50ms    82.5 MB/sec    1.05     12.7±0.60ms    78.7 MB/sec
# messaging/1KB                 1.00    820.0±45.0µs                   0.98    804.0±42.0µs
```

#### 回帰の判定基準

- **Critical (要対処)**: 10%以上の性能低下
- **Warning (要確認)**: 5-10%の性能低下
- **Acceptable (許容範囲)**: 5%以内の変動

### 自動化された回帰チェック

PRが作成されると、GitHub Actionsが自動的に:

1. PRブランチでベンチマーク実行
2. mainブランチと比較
3. 結果をPRにコメント

**PRコメント例:**

```markdown
## Performance Benchmark Results

group                         main       pr         change
-----                         ----       --         ------
file_transfer/10MB            1.00       1.03       +3%
messaging/1KB                 1.00       0.98       -2% ✅
video_streaming/720p          1.00       1.01       +1%
```

---

## Tor比較ベンチマーク

### 前提条件

#### Linux/macOS

```bash
# Torのインストール
# Ubuntu/Debian
sudo apt-get install tor curl bc

# macOS
brew install tor
```

#### 実行

##### Pythonスクリプト使用

```bash
# 依存関係のインストール
pip install matplotlib pandas numpy

# 比較ベンチマーク実行
python scripts/tor-comparison-benchmark.py --output benchmarks/results
```

##### シェルスクリプト使用 (Linux/macOS)

```bash
# 実行権限を付与
chmod +x scripts/run-comparison-benchmarks.sh

# 実行
./scripts/run-comparison-benchmarks.sh
```

### 測定項目

1. **ファイル転送スループット** (10MB)
   - NyxNet vs Tor
   - 測定: MB/s

2. **メッセージングレイテンシ** (1KB)
   - NyxNet vs Tor
   - 測定: ms

3. **接続確立時間**
   - 初回接続時間
   - 測定: ms

### 結果の解釈

#### 期待される結果

| メトリクス | NyxNet | Tor | スピードアップ |
|-----------|--------|-----|--------------|
| スループット (10MB) | 82.5 MB/s | ~5-10 MB/s | **8-16×** |
| レイテンシ (1KB) | 0.82ms | ~200-400ms | **244-488×** |
| 接続確立 | ~50ms | ~5000ms | **100×** |

**注**: Torの結果はネットワーク状態とノード選択に大きく依存します。

---

## 結果の解釈

### Criterionメトリクス

#### Time (実行時間)
- **Lower is better**: 小さいほど高速
- **標準偏差**: ±値が小さいほど安定

#### Throughput (スループット)
- **Higher is better**: 大きいほど高速
- **単位**: MB/s, GB/s

### 統計的有意性

Criterionは以下を自動検出:

- **Performance improvement**: 統計的に有意な改善
- **Performance regression**: 統計的に有意な劣化
- **No change**: 統計的に有意な差なし

### ノイズとバリアンス

#### 許容可能なバリアンス
- **< 5%**: 優秀
- **5-10%**: 許容範囲
- **> 10%**: 調査が必要

#### ノイズ削減のヒント

```bash
# Linux: CPUガバナーをperformanceに設定
sudo cpupower frequency-set -g performance

# 他のプロセスを停止
# バックグラウンドアプリを最小化

# 複数回実行して平均を取る
cargo bench --package nyx-benchmarks -- --warm-up-time 10 --measurement-time 30
```

---

## トラブルシューティング

### ベンチマークが失敗する

```bash
# ビルドエラー
cargo clean
cargo build --package nyx-benchmarks --release

# 依存関係の更新
cargo update
```

### Tor比較が動作しない

```bash
# Torの状態確認
sudo systemctl status tor  # Linux
brew services list tor     # macOS

# Tor SOCKSプロキシのテスト
curl --socks5 127.0.0.1:9050 https://check.torproject.org
```

### CI/CDでタイムアウト

```yaml
# タイムアウトを延長
- name: Run benchmarks
  run: cargo bench --package nyx-benchmarks
  timeout-minutes: 30  # デフォルトは60分
```

---

## ベストプラクティス

### 1. 定期実行

```yaml
schedule:
  # 毎週月曜日00:00 UTC
  - cron: '0 0 * * 1'
```

### 2. ベースライン管理

```bash
# メジャーバージョンごとにベースライン保存
cargo bench -- --save-baseline v1.0.0
cargo bench -- --save-baseline v2.0.0

# 比較
critcmp v1.0.0 v2.0.0
```

### 3. 結果の保存

- **Artifactとして保存**: CI環境
- **Git LFSで管理**: 大きなレポート
- **Grafanaで可視化**: 時系列トレンド

### 4. アラート設定

```yaml
- name: Check regression
  run: |
    if critcmp main pr | grep -q "regression"; then
      echo "::error::Performance regression detected"
      exit 1
    fi
```

---

## まとめ

✅ **実装完了:**
- GitHub Actions統合
- 自動パフォーマンス回帰検出
- Tor比較ベンチマーク
- クロスプラットフォーム対応

📊 **次のステップ:**
1. 初回ベンチマーク実行: `cargo bench --package nyx-benchmarks`
2. ベースライン保存: `cargo bench -- --save-baseline main`
3. CI/CDワークフロー有効化
4. Tor比較実行 (オプション)

🔗 **参考リンク:**
- [Criterion.rs Documentation](https://bheisler.github.io/criterion.rs/book/)
- [GitHub Actions Workflows](https://docs.github.com/en/actions)
- [Tor Project](https://www.torproject.org/)
