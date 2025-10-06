#!/bin/bash
# Apply network delay to Docker containers using tc (traffic control)

set -e

SCENARIO=${1:-"none"}

echo "=== Applying Network Delay to NyxNet Mix Nodes ==="
echo "Scenario: $SCENARIO"
echo ""

# Define delay parameters
case $SCENARIO in
  "lan")
    DELAY="2ms"
    JITTER="1ms"
    echo "LAN scenario: ${DELAY} ± ${JITTER}"
    ;;
  "regional")
    DELAY="25ms"
    JITTER="10ms"
    echo "Regional scenario: ${DELAY} ± ${JITTER}"
    ;;
  "global")
    DELAY="100ms"
    JITTER="30ms"
    echo "Global scenario: ${DELAY} ± ${JITTER}"
    ;;
  "none")
    echo "Clearing all delays..."
    for node in nyx-mix-1 nyx-mix-2 nyx-mix-3 nyx-mix-4; do
      docker exec $node tc qdisc del dev eth0 root 2>/dev/null || true
      echo "  ✓ Cleared $node"
    done
    echo "Done!"
    exit 0
    ;;
  *)
    echo "Usage: $0 [lan|regional|global|none]"
    exit 1
    ;;
esac

# Apply delays to each mix node
for node in nyx-mix-1 nyx-mix-2 nyx-mix-3 nyx-mix-4; do
  echo "Applying delay to $node..."
  
  # Clear existing
  docker exec $node tc qdisc del dev eth0 root 2>/dev/null || true
  
  # Add new delay
  docker exec $node tc qdisc add dev eth0 root netem delay $DELAY $JITTER
  
  # Verify
  docker exec $node tc qdisc show dev eth0
  
  echo "  ✓ $node configured"
done

echo ""
echo "✅ Network delays applied successfully!"
echo "To remove delays: $0 none"
