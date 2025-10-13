#!/bin/bash
# Debug script to check Unix socket access between nyx-proxy and nyx-daemon

set -e

NAMESPACE="nyx-test"

echo "===================================="
echo "Debugging Unix Socket Access"
echo "===================================="
echo ""

# Get cluster context
CLUSTER_NAME=$(kubectl config current-context | grep -o 'kind-nyx-cluster-[0-9]')
echo "Current cluster: ${CLUSTER_NAME}"
echo ""

# Check nyx-daemon pods
echo "--- nyx-daemon Pods ---"
DAEMON_PODS=$(kubectl get pods -n ${NAMESPACE} -l app=nyx-daemon -o jsonpath='{.items[*].metadata.name}')
echo "Daemon pods: ${DAEMON_PODS}"
echo ""

for pod in ${DAEMON_PODS}; do
    echo "=== Checking daemon pod: ${pod} ==="
    
    # Check if socket exists on host /tmp
    echo "1. Check socket on host /tmp:"
    NODE=$(kubectl get pod -n ${NAMESPACE} ${pod} -o jsonpath='{.spec.nodeName}')
    echo "   Running on node: ${NODE}"
    
    docker exec ${NODE} ls -la /tmp/nyx.sock 2>&1 || echo "   ⚠️ Socket not found on host /tmp"
    echo ""
    
    # Check socket inside daemon container
    echo "2. Check socket inside daemon container:"
    kubectl exec -n ${NAMESPACE} ${pod} -- ls -la /tmp/nyx.sock 2>&1 || echo "   ⚠️ Socket not found in daemon container"
    echo ""
    
    # Check daemon process
    echo "3. Check daemon process:"
    kubectl exec -n ${NAMESPACE} ${pod} -- ps aux | grep nyx-daemon | grep -v grep || echo "   ⚠️ Daemon process not found"
    echo ""
    
    # Check daemon logs
    echo "4. Recent daemon logs:"
    kubectl logs -n ${NAMESPACE} ${pod} --tail=5 2>&1
    echo ""
done

# Check nyx-proxy pods
echo "--- nyx-proxy Pods ---"
PROXY_PODS=$(kubectl get pods -n ${NAMESPACE} -l app=nyx-proxy -o jsonpath='{.items[*].metadata.name}')
echo "Proxy pods: ${PROXY_PODS}"
echo ""

for pod in ${PROXY_PODS}; do
    echo "=== Checking proxy pod: ${pod} ==="
    
    # Check if socket accessible from proxy
    echo "1. Check /host-tmp mount in proxy:"
    kubectl exec -n ${NAMESPACE} ${pod} -- ls -la /host-tmp/ 2>&1 || echo "   ⚠️ /host-tmp not accessible"
    echo ""
    
    echo "2. Check /host-tmp/nyx.sock in proxy:"
    kubectl exec -n ${NAMESPACE} ${pod} -- ls -la /host-tmp/nyx.sock 2>&1 || echo "   ⚠️ Socket not accessible in proxy"
    echo ""
    
    echo "3. Check proxy process:"
    kubectl exec -n ${NAMESPACE} ${pod} -- ps aux | grep nyx-http-proxy | grep -v grep || echo "   ⚠️ Proxy process not found"
    echo ""
    
    echo "4. Recent proxy logs:"
    kubectl logs -n ${NAMESPACE} ${pod} --tail=5 2>&1
    echo ""
    
    echo "5. Test socket connection from proxy:"
    kubectl exec -n ${NAMESPACE} ${pod} -- socat -u OPEN:/dev/null UNIX-CONNECT:/host-tmp/nyx.sock 2>&1 && echo "   ✅ Socket connection successful" || echo "   ⚠️ Socket connection failed"
    echo ""
done

echo "===================================="
echo "Debug complete"
echo "===================================="
