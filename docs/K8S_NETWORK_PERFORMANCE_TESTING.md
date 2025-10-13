# NyxNet Kubernetes Network Performance Testing

SOCKS5プロキシのテストをスキップして、Kubernetesクラスター間の直接通信とネットワークパフォーマンスを測定します。

## クイックスタート

### オプション1: ネットワークパフォーマンステストのみ実行

```bash
# SOCKS5とMix Networkテストをスキップ
SKIP_SOCKS5_TESTS=true SKIP_MIX_ROUTING_TESTS=true bash scripts/k8s-nyx-test.sh
```

### オプション2: 独立したネットワークパフォーマンステスト

```bash
# クラスターが既にデプロイされている場合
bash scripts/k8s-network-perf-test.sh
```

## テスト内容

### 1. ネットワーク接続性テスト
- クラスター間のpingテスト
- パケット損失率の測定
- 基本的なTCP/IP接続確認

```bash
✅ Connectivity OK: nyx-cluster-1 → nyx-cluster-2 (172.18.0.10)
✅ Connectivity OK: nyx-cluster-1 → nyx-cluster-3 (172.18.0.13)
```

### 2. NyxNet Daemon通信テスト
- Daemon間のメトリクス共有確認
- gRPC API応答確認
- 各クラスター内のDaemon同期状態確認

```bash
✅ Daemon communication OK in nyx-cluster-1 (42 metrics)
✅ Daemon communication OK in nyx-cluster-2 (38 metrics)
```

### 3. スループット測定 (iperf3)
- クラスター間の帯域幅測定
- TCP throughput (Mbps)
- 10秒間のデータ転送テスト

```bash
✅ Throughput: nyx-cluster-1 → nyx-cluster-2 = 1250.45 Mbps
✅ Throughput: nyx-cluster-2 → nyx-cluster-3 = 1180.32 Mbps
```

### 4. レイテンシ測定
- ICMP pingによるRTT測定
- 平均/最小/最大レイテンシ
- ジッター(変動)の測定

```bash
✅ Latency: nyx-cluster-1 → nyx-cluster-2 = 0.524 ms
✅ Latency: nyx-cluster-2 → nyx-cluster-3 = 0.618 ms
```

## 環境変数オプション

| 変数 | デフォルト | 説明 |
|------|-----------|------|
| `CLUSTER_COUNT` | `3` | 作成するクラスター数 |
| `SKIP_SOCKS5_TESTS` | `false` | SOCKS5プロキシテストをスキップ |
| `SKIP_MIX_ROUTING_TESTS` | `false` | Mix Networkルーティングテストをスキップ |
| `RUN_NETWORK_PERF_TESTS` | `true` | ネットワークパフォーマンステストを実行 |
| `SKIP_CLEANUP` | `false` | テスト後のクリーンアップをスキップ |

## 使用例

### 最小限のテスト (接続性とパフォーマンスのみ)

```bash
SKIP_SOCKS5_TESTS=true \
SKIP_MIX_ROUTING_TESTS=true \
CLUSTER_COUNT=2 \
bash scripts/k8s-nyx-test.sh
```

### クラスターを残してデバッグ

```bash
SKIP_CLEANUP=true bash scripts/k8s-nyx-test.sh
```

手動でクリーンアップ:
```bash
kind delete clusters nyx-cluster-1 nyx-cluster-2 nyx-cluster-3
```

### フルテストスイート

```bash
# 全てのテストを実行 (SOCKS5, Mix Network, パフォーマンス)
bash scripts/k8s-nyx-test.sh
```

## 期待される結果

### 成功時の出力例

```
▶ 🚀 Testing Inter-Cluster Network Connectivity
2025-10-13 06:00:00
ℹ️  [INFO] Testing: nyx-cluster-1 → nyx-cluster-2
✅  [SUCCESS] Connectivity OK: nyx-cluster-1 → nyx-cluster-2 (172.18.0.10)
ℹ️  [INFO] Testing: nyx-cluster-1 → nyx-cluster-3
✅  [SUCCESS] Connectivity OK: nyx-cluster-1 → nyx-cluster-3 (172.18.0.13)
...
ℹ️  [INFO] Network connectivity tests: 6/6 passed

▶ 🚀 Testing Network Throughput (iperf3)
2025-10-13 06:00:15
ℹ️  [INFO] Throughput test: nyx-cluster-1 → nyx-cluster-2
ℹ️  [INFO] Running iperf3 from nyx-cluster-1 to nyx-cluster-2 (10.241.2.3)...
✅  [SUCCESS] Throughput: nyx-cluster-1 → nyx-cluster-2 = 1250.45 Mbps
...
ℹ️  [INFO] Throughput tests: 6/6 passed

▶ 🚀 Test Summary
2025-10-13 06:02:30
ℹ️  [INFO] Total tests: 18
ℹ️  [INFO] Passed: 18
ℹ️  [INFO] Failed: 0
ℹ️  [INFO] Success rate: 100%
✅  [SUCCESS] All tests passed! 🎉
```

## トラブルシューティング

### iperf3が見つからない

test-clientイメージ (nicolaka/netshoot) にはiperf3が含まれています。
イメージが正しくpullされているか確認:

```bash
kubectl get pod test-client -n nyx-test -o jsonpath='{.status.phase}'
```

### タイムアウトエラー

システムリソースが不足している可能性があります:

```bash
# クラスター数を減らす
CLUSTER_COUNT=2 SKIP_SOCKS5_TESTS=true bash scripts/k8s-nyx-test.sh
```

### スループットが低い

Docker Desktopの場合、リソース割り当てを増やしてください:
- メモリ: 8GB以上推奨
- CPU: 4コア以上推奨

## 参考情報

- **iperf3**: https://iperf.fr/
- **Kind (Kubernetes in Docker)**: https://kind.sigs.k8s.io/
- **nicolaka/netshoot**: https://github.com/nicolaka/netshoot
