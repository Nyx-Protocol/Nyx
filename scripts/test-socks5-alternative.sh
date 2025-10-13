#!/bin/bash
# Alternative SOCKS5 client tests
# Tests SOCKS5 using different clients to isolate curl issues

set -euo pipefail

CLUSTER="${1:-nyx-cluster-1}"
NAMESPACE="nyx-test"
SERVICE_NAME="nyx-proxy.nyx-test.svc.cluster.local"
SERVICE_PORT="9050"

echo "=== Alternative SOCKS5 Client Tests ==="
echo "Cluster: ${CLUSTER}"
echo "Service: ${SERVICE_NAME}:${SERVICE_PORT}"
echo ""

# Get test client pod
TEST_POD=$(kubectl --context kind-${CLUSTER} -n ${NAMESPACE} get pods -l run=test-client -o jsonpath='{.items[0].metadata.name}' 2>/dev/null || echo "test-client")

echo "Using test pod: ${TEST_POD}"
echo ""

# Test 1: Python SOCKS5 client (most reliable)
echo "=== Test 1: Python SOCKS5 Client ==="
kubectl --context kind-${CLUSTER} -n ${NAMESPACE} exec ${TEST_POD} -- python3 -c "
import socket
import struct
import sys

try:
    # Connect to SOCKS5 proxy
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.settimeout(10)
    
    # Resolve service name
    import socket as s
    service_ip = s.gethostbyname('${SERVICE_NAME}')
    print(f'Resolved ${SERVICE_NAME} to {service_ip}')
    
    sock.connect((service_ip, ${SERVICE_PORT}))
    print('✅ TCP connection established')
    
    # Send SOCKS5 greeting: VER=5, NMETHODS=1, METHODS=[0 (no-auth)]
    greeting = b'\x05\x01\x00'
    sock.sendall(greeting)
    print(f'✅ Sent greeting: {greeting.hex()}')
    
    # Receive response: VER=5, METHOD=0
    response = sock.recv(2)
    print(f'✅ Received response: {response.hex()}')
    
    if len(response) != 2:
        print(f'❌ Invalid response length: {len(response)}')
        sys.exit(1)
    
    if response[0] != 0x05:
        print(f'❌ Invalid SOCKS version: {response[0]:02x}')
        sys.exit(1)
    
    if response[1] != 0x00:
        print(f'❌ Auth method not accepted: {response[1]:02x}')
        sys.exit(1)
    
    print('✅ SOCKS5 handshake successful!')
    
    # Send CONNECT request
    # VER=5, CMD=1 (CONNECT), RSV=0, ATYP=3 (domain)
    target_domain = b'example.com'
    target_port = 80
    
    connect_req = b'\x05\x01\x00\x03'  # VER, CMD, RSV, ATYP
    connect_req += bytes([len(target_domain)])  # Domain length
    connect_req += target_domain  # Domain
    connect_req += struct.pack('>H', target_port)  # Port (big-endian)
    
    sock.sendall(connect_req)
    print(f'✅ Sent CONNECT request to {target_domain.decode()}:{target_port}')
    
    # Receive CONNECT response
    connect_resp = sock.recv(1024)
    print(f'✅ Received CONNECT response: {connect_resp[:10].hex()}...')
    
    if len(connect_resp) < 4:
        print(f'❌ Invalid CONNECT response length: {len(connect_resp)}')
        sys.exit(1)
    
    if connect_resp[1] != 0x00:
        print(f'❌ CONNECT failed with code: {connect_resp[1]:02x}')
        sys.exit(1)
    
    print('✅ CONNECT successful!')
    print('✅ Mix Network connection established!')
    
    sock.close()
    print('✅ All tests passed!')
    sys.exit(0)
    
except socket.timeout:
    print('❌ Connection timeout')
    sys.exit(1)
except ConnectionRefusedError:
    print('❌ Connection refused')
    sys.exit(1)
except Exception as e:
    print(f'❌ Error: {e}')
    import traceback
    traceback.print_exc()
    sys.exit(1)
" 2>&1 || echo "Python test failed with exit code $?"

echo ""
echo "=== Test 2: netcat + socat Raw Protocol Test ==="
kubectl --context kind-${CLUSTER} -n ${NAMESPACE} exec ${TEST_POD} -- bash -c "
# Send SOCKS5 greeting and read response
echo 'Sending SOCKS5 greeting...'
response=\$(echo -ne '\x05\x01\x00' | timeout 5 nc ${SERVICE_NAME} ${SERVICE_PORT} | xxd -p)
echo \"Response (hex): \${response}\"

if [[ \"\${response}\" == \"0500\" ]]; then
    echo '✅ Valid SOCKS5 response: version=5, method=no-auth'
else
    echo \"❌ Invalid or no response: \${response}\"
fi
" 2>&1 || echo "netcat test failed"

echo ""
echo "=== Test 3: Check nyx-proxy logs after Python test ==="
PROXY_POD=$(kubectl --context kind-${CLUSTER} -n ${NAMESPACE} get pods -l app=nyx-proxy -o jsonpath='{.items[0].metadata.name}')
echo "Proxy pod: ${PROXY_POD}"
echo "Recent logs:"
kubectl --context kind-${CLUSTER} -n ${NAMESPACE} logs ${PROXY_POD} --tail=30

echo ""
echo "=== Test 4: Direct Pod IP test (bypass Service) ==="
PROXY_IP=$(kubectl --context kind-${CLUSTER} -n ${NAMESPACE} get pod ${PROXY_POD} -o jsonpath='{.status.podIP}')
echo "Proxy Pod IP: ${PROXY_IP}"

kubectl --context kind-${CLUSTER} -n ${NAMESPACE} exec ${TEST_POD} -- python3 -c "
import socket

try:
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.settimeout(5)
    sock.connect(('${PROXY_IP}', ${SERVICE_PORT}))
    print('✅ Direct Pod IP connection successful')
    
    # Send greeting
    sock.sendall(b'\x05\x01\x00')
    response = sock.recv(2)
    print(f'Response: {response.hex()}')
    
    if response == b'\x05\x00':
        print('✅ SOCKS5 handshake via direct Pod IP successful!')
    else:
        print(f'❌ Unexpected response: {response.hex()}')
    
    sock.close()
except Exception as e:
    print(f'❌ Error: {e}')
" 2>&1 || echo "Direct Pod IP test failed"

echo ""
echo "=== Summary ==="
echo "If Python test passed: nyx-http-proxy SOCKS5 implementation is correct"
echo "If Python test failed: Check nyx-proxy logs for detailed error"
echo "If curl failed but Python passed: curl SOCKS5 client has compatibility issues"
