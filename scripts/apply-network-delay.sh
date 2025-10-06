#!/bin/bash
# Network Delay Simulation Script for NyxNet Benchmark
# このスクリプトはDocker内で実行され、各Mix nodeに遅延を追加します

set -e

SCENARIO=${1:-"lan"}

echo "=== NyxNet Network Delay Simulation ==="
echo "Scenario: $SCENARIO"
echo ""

# 遅延パラメータの定義
case $SCENARIO in
  "lan")
    # ローカルネットワーク (同じ建物内)
    DELAY="2ms"
    JITTER="1ms"
    LOSS="0.1%"
    echo "Simulating LAN environment:"
    echo "  Delay: $DELAY ± $JITTER"
    echo "  Packet loss: $LOSS"
    ;;
  
  "regional")
    # 地域ネットワーク (同じ国内)
    DELAY="25ms"
    JITTER="10ms"
    LOSS="0.5%"
    echo "Simulating Regional (WAN) environment:"
    echo "  Delay: $DELAY ± $JITTER"
    echo "  Packet loss: $LOSS"
    ;;
  
  "global")
    # グローバルネットワーク (国際)
    DELAY="100ms"
    JITTER="30ms"
    LOSS="1%"
    echo "Simulating Global environment:"
    echo "  Delay: $DELAY ± $JITTER"
    echo "  Packet loss: $LOSS"
    ;;
  
  "none")
    echo "Clearing all network delays..."
    docker exec nyx-mix-1 tc qdisc del dev eth0 root 2>/dev/null || true
    docker exec nyx-mix-2 tc qdisc del dev eth0 root 2>/dev/null || true
    docker exec nyx-mix-3 tc qdisc del dev eth0 root 2>/dev/null || true
    docker exec nyx-mix-4 tc qdisc del dev eth0 root 2>/dev/null || true
    echo "✅ All network delays cleared"
    exit 0
    ;;
  
  *)
    echo "❌ Unknown scenario: $SCENARIO"
    echo "Usage: $0 [lan|regional|global|none]"
    exit 1
    ;;
esac

echo ""
echo "Applying network delays to Mix nodes..."

# 各Mix nodeに遅延を適用
for NODE in nyx-mix-1 nyx-mix-2 nyx-mix-3 nyx-mix-4; do
  echo "  → Configuring $NODE..."
  
  # 既存の設定をクリア
  docker exec $NODE tc qdisc del dev eth0 root 2>/dev/null || true
  
  # 新しい遅延を設定
  docker exec $NODE tc qdisc add dev eth0 root netem \
    delay $DELAY $JITTER \
    loss $LOSS
  
  # 確認
  docker exec $NODE tc qdisc show dev eth0
done

echo ""
echo "✅ Network delays applied successfully!"
echo ""
echo "Expected round-trip latency (4 hops):"

case $SCENARIO in
  "lan")
    echo "  Min: ~8ms (4 × 2ms)"
    echo "  Max: ~16ms (4 × 4ms with jitter)"
    ;;
  "regional")
    echo "  Min: ~100ms (4 × 25ms)"
    echo "  Max: ~200ms (4 × 50ms with jitter)"
    ;;
  "global")
    echo "  Min: ~400ms (4 × 100ms)"
    echo "  Max: ~700ms (4 × 175ms with jitter)"
    ;;
esac

echo ""
echo "To clear delays, run: $0 none"
