# NyxNet Simplified Testing Guide

SOCKS5プロキシを完全に削除し、純粋なネットワークパフォーマンステストに特化しました。

## クイックスタート

```bash
# シンプルなネットワークテスト (推奨)
bash scripts/k8s-simple-test.sh

# または従来のスクリプト (互換性のため残存)
bash scripts/k8s-nyx-test.sh
```

## テスト内容

### 1. Daemon ヘルスチェック
- Unix socketの存在確認
- 各クラスター内の全DaemonPodの健全性確認

### 2. ネットワーク接続性
- クラスター間のping疎通テスト
- パケット損失率の確認

### 3. ネットワークレイテンシ
- RTT (Round Trip Time) 測定
- 平均/最小/最大レイテンシ
- クラスター間の遅延プロファイル

## 削除された機能

以下の機能はテストから削除されました:

- ❌ **SOCKS5 Proxy**: Unixソケット通信の複雑さを削除
- ❌ **Mix Network Routing**: プロキシ依存のため削除
- ❌ **Anonymization Tests**: メトリクス取得の問題により削除
- ❌ **Cover Traffic Tests**: 実装未完了のため削除
- ❌ **nyx-http-proxy**: デプロイから完全に削除

## 環境変数

| 変数 | デフォルト | 説明 |
|------|-----------|------|
| `CLUSTER_COUNT` | `3` | 作成するクラスター数 |
| `SKIP_CLEANUP` | `false` | テスト後のクリーンアップをスキップ |

## 使用例

### 最小構成 (2クラスター)

```bash
CLUSTER_COUNT=2 bash scripts/k8s-simple-test.sh
```

### クラスターを残してデバッグ

```bash
SKIP_CLEANUP=true bash scripts/k8s-simple-test.sh

# 手動でクリーンアップ
kind delete clusters nyx-cluster-1 nyx-cluster-2 nyx-cluster-3
```

## 期待される出力

```
▶ 🚀 Creating Kubernetes Clusters
2025-10-13 07:00:00
ℹ️  [INFO] Creating cluster: nyx-cluster-1
...
✅  [SUCCESS] All clusters created in 45s

▶ 🚀 Building NyxNet Docker image
...
✅  [SUCCESS] Docker image built in 18s

▶ 🚀 Deploying NyxNet components
...
✅  [SUCCESS] Deployed to nyx-cluster-3

▶ 🚀 Testing NyxNet Daemon Health
ℹ️  [INFO] Checking daemon health: nyx-cluster-1/nyx-daemon-abc123
✅  [SUCCESS] Daemon healthy: nyx-cluster-1/nyx-daemon-abc123
...
ℹ️  [INFO] Daemon health tests completed: 6/6 passed

▶ 🚀 Testing Inter-Cluster Network Connectivity
ℹ️  [INFO] Testing: nyx-cluster-1 → nyx-cluster-2
✅  [SUCCESS] Connectivity OK: nyx-cluster-1 → nyx-cluster-2
...
ℹ️  [INFO] Network connectivity tests: 6/6 passed

▶ 🚀 Testing Network Latency
ℹ️  [INFO] Latency test: nyx-cluster-1 → nyx-cluster-2
✅  [SUCCESS] Latency: nyx-cluster-1 → nyx-cluster-2 = 0.524 ms
...
ℹ️  [INFO] Latency tests: 6/6 passed

▶ 🚀 Test Summary
ℹ️  [INFO] Total tests: 18
ℹ️  [INFO] Passed: 18
ℹ️  [INFO] Failed: 0
ℹ️  [INFO] Success rate: 100%
✅  [SUCCESS] All tests passed! 🎉
```

## アーキテクチャの簡素化

### 以前のアーキテクチャ
```
test-client → nyx-http-proxy (SOCKS5) → nyx-daemon (IPC via Unix socket) → Network
                     ❌ 複雑                ❌ 問題多発
```

### 現在のアーキテクチャ
```
test-client → nyx-daemon → Network
       ✅ シンプル    ✅ 安定
```

## トラブルシューティング

### メモリ不足

```bash
# クラスター数を減らす
CLUSTER_COUNT=2 bash scripts/k8s-simple-test.sh
```

### Docker Desktop設定

推奨リソース:
- **メモリ**: 8GB以上
- **CPU**: 4コア以上
- **ディスク**: 20GB以上

## 関連ファイル

- `scripts/k8s-simple-test.sh` - 新しいシンプルなテストスクリプト
- `scripts/k8s-nyx-test.sh` - 従来のテストスクリプト (互換性のため保持)
- `k8s-nyx-manifests.yaml` - Kubernetes manifest (nyx-daemonのみ)
