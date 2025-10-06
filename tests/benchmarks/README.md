# NyxNet Performance Benchmarks - 実行ガイド

## 📊 概要

実際のNyxNetコンポーネント(UDP transport、ChaCha20Poly1305暗号化)を使用した
アプリケーションレベルのパフォーマンスベンチマークです。

## 🚀 ベンチマークの実行

### 基本実行

```bash
# すべてのベンチマークを実行
cargo bench --package nyx-benchmarks

# 特定のベンチマークのみ実行
cargo bench --package nyx-benchmarks -- file_transfer
cargo bench --package nyx-benchmarks -- messaging
cargo bench --package nyx-benchmarks -- video_streaming
cargo bench --package nyx-benchmarks -- voip
cargo bench --package nyx-benchmarks -- scalability
```

### クイックテスト(開発用)

```bash
# 短時間でテスト実行
cargo bench --package nyx-benchmarks -- --quick
```

### PowerShell (Windows)

```powershell
# 基本実行
cargo bench --package nyx-benchmarks

# 結果をファイルに保存
cargo bench --package nyx-benchmarks 2>&1 | Tee-Object -FilePath benchmark_results.txt
```

## 📈 結果の確認

ベンチマーク結果は以下に保存されます:

```
target/criterion/
├── file_transfer/
│   ├── report/
│   │   └── index.html  # HTMLレポート
│   └── base/
│       └── estimates.json
├── messaging/
├── video_streaming/
├── voip/
└── scalability/
```

### HTMLレポートを開く

**Windows:**
```powershell
# ファイル転送ベンチマーク結果
Start-Process "target\criterion\file_transfer\report\index.html"

# メッセージングベンチマーク結果
Start-Process "target\criterion\messaging\report\index.html"
```

**Linux/macOS:**
```bash
# ファイル転送ベンチマーク結果
open target/criterion/file_transfer/report/index.html

# メッセージングベンチマーク結果
open target/criterion/messaging/report/index.html
```

## 🔬 ベンチマーク内容

### 1. ファイル転送 (file_transfer)

**測定内容:**
- 1MB、10MB、100MBのファイル転送
- UDP + ChaCha20Poly1305暗号化
- MTU(1400バイト)単位でのチャンク分割

**期待値:**
- スループット: 50-100 MB/s (ローカルループバック)
- レイテンシ: < 200ms (100MB)

### 2. リアルタイムメッセージング (messaging)

**測定内容:**
- 1KB、4KB、16KBのメッセージ送受信
- ラウンドトリップレイテンシ測定
- スループット測定(1000メッセージ)

**期待値:**
- レイテンシ: < 1ms (ローカルループバック)
- スループット: > 10,000 msg/s

### 3. ビデオストリーミング (video_streaming)

**測定内容:**
- 720p相当(2.5 Mbps)の持続的ストリーミング
- 10秒間の送信
- パケットロス率測定

**期待値:**
- 持続ビットレート: 2.48+ Mbps
- パケットロス: < 0.1% (ローカルループバック)

### 4. VoIP (voip)

**測定内容:**
- Opusコーデック相当(64 kbps、20msフレーム)
- 10秒間の通話シミュレーション
- レイテンシ、ジッター、MOS測定

**期待値:**
- レイテンシ: < 20ms (ローカルループバック)
- ジッター: < 5ms
- MOS: > 4.0

### 5. スケーラビリティ (scalability)

**測定内容:**
- 10、100、500の同時接続
- 並行メッセージ送受信
- 平均レイテンシ測定

**期待値:**
- 10接続: < 5ms平均
- 100接続: < 50ms平均
- 500接続: < 500ms平均

## 📊 結果の解釈

### Criterionの出力例

```
file_transfer/nyx_network/1MB
                        time:   [12.234 ms 12.456 ms 12.678 ms]
                        thrpt:  [79.912 MiB/s 81.234 MiB/s 82.556 MiB/s]

messaging/message_latency/1KB
                        time:   [0.8234 ms 0.8456 ms 0.8678 ms]

scalability/concurrent_connections/100
                        time:   [45.234 ms 46.456 ms 47.678 ms]
```

**読み方:**
- `time`: [最小値 平均値 最大値]
- `thrpt`: スループット(該当する場合)
- 信頼区間: 95%

### パフォーマンス比較

前回の実行結果と自動比較されます:

```
change: [-5.1234% -2.3456% +0.1234%] (p = 0.23 > 0.05)
        No change in performance detected.
```

- **緑色**: 性能向上
- **赤色**: 性能低下
- **変化なし**: p > 0.05

## 🔧 トラブルシューティング

### ビルドエラー

```bash
# クリーンビルド
cargo clean
cargo build --package nyx-benchmarks --release
```

### ポート競合

ベンチマークは動的ポート(0)を使用しますが、問題がある場合:

```bash
# Windowsでポート確認
netstat -ano | findstr "LISTEN"

# プロセスを終了
taskkill /PID <PID> /F
```

### メモリ不足

大きなファイル転送ベンチマークでメモリ不足になる場合:

```bash
# 小さいサイズのみ実行
cargo bench --package nyx-benchmarks -- "file_transfer/.*1MB"
```

## 📝 カスタムベンチマーク

`tests/benchmarks/application_scenarios.rs`を編集して独自のベンチマークを追加:

```rust
fn bench_my_scenario(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    c.bench_function("my_scenario", |b| {
        b.to_async(&rt).iter(|| async {
            let network = TestNetwork::new().await;
            // ベンチマークコード
        });
    });
}

// criterion_group!に追加
criterion_group!(
    benches,
    bench_file_transfer,
    bench_messaging,
    bench_video_streaming,
    bench_voip,
    bench_scalability,
    bench_my_scenario,  // <-- 追加
);
```

## 🌐 ネットワーク遅延のシミュレーション

実際のネットワーク条件をシミュレートする場合:

**Linux (tc):**
```bash
# 50msの遅延を追加
sudo tc qdisc add dev lo root netem delay 50ms

# 解除
sudo tc qdisc del dev lo root
```

**Windows (clumsy):**
```powershell
# clumsyツールを使用
# https://jagt.github.io/clumsy/
```

## 📚 参考資料

- [Criterion.rsドキュメント](https://bheisler.github.io/criterion.rs/book/)
- [パフォーマンス評価ガイド](../../docs/PERFORMANCE_EVALUATION.md)
- [NyxNet アーキテクチャ](../../docs/architecture.md)

---

**最終更新**: 2025-10-06  
**メンテナ**: Selenia Project
