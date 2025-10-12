#!/bin/bash
# SOCKS5 Protocol Debugging Script
# This script performs low-level SOCKS5 protocol testing

set -euo pipefail

CLUSTER="${1:-nyx-cluster-1}"
NAMESPACE="nyx-test"

echo "=== SOCKS5 Protocol Debug for ${CLUSTER} ==="
echo ""

# Get proxy pod
PROXY_POD=$(kubectl --context kind-${CLUSTER} -n ${NAMESPACE} get pods -l app=nyx-proxy -o jsonpath='{.items[0].metadata.name}')
echo "Proxy Pod: ${PROXY_POD}"

# Get service IP
SERVICE_IP=$(kubectl --context kind-${CLUSTER} -n ${NAMESPACE} get svc nyx-proxy -o jsonpath='{.spec.clusterIP}')
echo "Service IP: ${SERVICE_IP}"
echo ""

# Test 1: Check if SOCKS5 port is listening
echo "=== Test 1: Port Connectivity ==="
kubectl --context kind-${CLUSTER} -n ${NAMESPACE} exec test-client -- nc -zv ${SERVICE_IP} 9050 2>&1 || true
echo ""

# Test 2: Raw TCP connection test
echo "=== Test 2: Raw TCP Connection ==="
kubectl --context kind-${CLUSTER} -n ${NAMESPACE} exec test-client -- timeout 3 nc ${SERVICE_IP} 9050 < /dev/null 2>&1 || true
echo ""

# Test 3: Send SOCKS5 greeting manually
echo "=== Test 3: Manual SOCKS5 Greeting ==="
echo "Sending SOCKS5 greeting: 0x05 0x01 0x00 (version 5, 1 method, no-auth)"
kubectl --context kind-${CLUSTER} -n ${NAMESPACE} exec test-client -- bash -c "echo -ne '\x05\x01\x00' | nc -w 3 ${SERVICE_IP} 9050 | xxd" 2>&1 || true
echo ""

# Test 4: Test with socat (more verbose)
echo "=== Test 4: Socat SOCKS5 Test ==="
kubectl --context kind-${CLUSTER} -n ${NAMESPACE} exec test-client -- bash -c "
echo -ne '\x05\x01\x00' | socat -v - TCP:${SERVICE_IP}:9050,connect-timeout=3 2>&1 | head -20
" 2>&1 || true
echo ""

# Test 5: Test Unix socket directly on proxy pod
echo "=== Test 5: Unix Socket Health ==="
kubectl --context kind-${CLUSTER} -n ${NAMESPACE} exec ${PROXY_POD} -- bash -c "
echo 'Unix socket status:'
test -S /tmp/nyx.sock && echo '✅ Socket exists' || echo '❌ Socket missing'
ls -la /tmp/nyx.sock 2>&1 || true
echo ''
echo 'nyx-daemon process:'
ps aux | grep nyx-daemon | grep -v grep || echo '❌ Process not found'
echo ''
echo 'Recent proxy logs (last 20 lines):'
" 2>&1
echo ""

# Test 6: Check nyx-daemon logs
echo "=== Test 6: nyx-daemon Logs ==="
DAEMON_POD=$(kubectl --context kind-${CLUSTER} -n ${NAMESPACE} get pods -l app=nyx-daemon --field-selector spec.nodeName=$(kubectl --context kind-${CLUSTER} -n ${NAMESPACE} get pod ${PROXY_POD} -o jsonpath='{.spec.nodeName}') -o jsonpath='{.items[0].metadata.name}')
echo "Daemon Pod: ${DAEMON_POD}"
kubectl --context kind-${CLUSTER} -n ${NAMESPACE} logs ${DAEMON_POD} --tail=30 2>&1 || true
echo ""

# Test 7: Direct curl test with maximum verbosity
echo "=== Test 7: Curl SOCKS5 Test (Maximum Verbosity) ==="
kubectl --context kind-${CLUSTER} -n ${NAMESPACE} exec test-client -- curl -vvv \
  --socks5-hostname ${SERVICE_IP}:9050 \
  --max-time 10 \
  http://example.com 2>&1 | head -50 || true
echo ""

# Test 8: Alternative SOCKS5 URL format
echo "=== Test 8: Alternative SOCKS5 Format ==="
kubectl --context kind-${CLUSTER} -n ${NAMESPACE} exec test-client -- curl -vvv \
  -x socks5://${SERVICE_IP}:9050 \
  --max-time 10 \
  http://example.com 2>&1 | head -50 || true
echo ""

echo "=== Debug Complete ==="
