# SOCKS5 Debugging Guide

## Current Status

### ✅ Working
- All pods deployed successfully (6/6 daemon healthy)
- Unix socket communication established (`/tmp/nyx.sock`)
- Mix Layer connections successful (cluster-2, cluster-3)
- TCP connectivity to SOCKS5 port (9050)

### ❌ Failing
- SOCKS5 protocol handshake: `auth failed: read greeting: EOF`
- All Mix Network routing tests (0/6 passed)
- Prometheus metrics collection (0/3 passed)

## Root Cause Analysis

The error `read greeting: EOF` indicates the client connection is established but:
1. Client doesn't send SOCKS5 greeting data, OR
2. Client closes connection immediately after connecting, OR
3. Client sends malformed SOCKS5 greeting

## Latest Changes (2025-10-13)

### Code Improvements in `nyx-http-proxy/socks5.go`:
1. **Better timeout handling**: Added 30-second read timeouts for auth/request phases
2. **Fixed greeting read**: Use `io.ReadFull` to ensure full header read
3. **Detailed logging**: Log every step of SOCKS5 handshake
   - Client connection details
   - Protocol version verification
   - Authentication method selection
   - Request parsing details

### New Debug Script: `scripts/debug-socks5.sh`
Performs low-level protocol testing:
- Raw TCP connectivity
- Manual SOCKS5 greeting (hex: `\x05\x01\x00`)
- socat verbose testing
- Unix socket health checks
- Daemon/proxy log correlation

## Next Steps on Linux Server

### 1. Pull Latest Changes
```bash
cd /root/Nyx
git pull
```

### 2. Rebuild and Redeploy
```bash
# Full automated test with new logging
SKIP_CLEANUP=true bash scripts/k8s-nyx-test.sh
```

### 3. Run Debug Script
```bash
# Detailed protocol-level debugging
bash scripts/debug-socks5.sh nyx-cluster-1
```

### 4. Check Detailed Logs
```bash
# View new detailed SOCKS5 logs from nyx-proxy
kubectl --context kind-nyx-cluster-1 -n nyx-test logs -l app=nyx-proxy --tail=100

# Expected new log entries:
# - "SOCKS5 new connection from X.X.X.X:XXXXX"
# - "SOCKS5 [X.X.X.X:XXXXX] starting authentication handshake"
# - "SOCKS5 client greeting: version=0x05, nmethods=1, methods=[0]"
# - "SOCKS5 selected auth method: 0x00 (no-auth)"
# - "SOCKS5 authentication successful"
```

## Expected Outcomes

### If Logs Show Connection But No Greeting:
→ Problem is with curl's SOCKS5 implementation
→ Solution: Test with alternative SOCKS5 clients (socat, proxychains, Python)

### If Logs Show Invalid Version/Format:
→ Problem is protocol mismatch
→ Solution: Fix nyx-http-proxy to handle curl's specific SOCKS5 dialect

### If Logs Show Timeout:
→ Problem is network latency or client delay
→ Solution: Increase timeout or optimize network path

### If Connection Never Reaches handleAuth:
→ Problem is before SOCKS5 layer (TCP/Service routing)
→ Solution: Check Kubernetes Service, iptables, CNI

## Alternative Testing Methods

### Test 1: Python SOCKS5 Client
```python
import socket
import struct

# Connect to SOCKS5 proxy
sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
sock.connect(('SERVICE_IP', 9050))

# Send greeting: VER=5, NMETHODS=1, METHODS=[0 (no-auth)]
sock.sendall(b'\x05\x01\x00')

# Receive response: VER=5, METHOD=0
response = sock.recv(2)
print(f"Response: {response.hex()}")  # Expected: 0500

sock.close()
```

### Test 2: Socat Verbose Mode
```bash
echo -ne '\x05\x01\x00' | socat -v - TCP:SERVICE_IP:9050
```

### Test 3: Direct Pod-to-Pod
```bash
# Get proxy pod IP
PROXY_IP=$(kubectl --context kind-nyx-cluster-1 -n nyx-test get pod -l app=nyx-proxy -o jsonpath='{.items[0].status.podIP}')

# Test from test-client
kubectl --context kind-nyx-cluster-1 -n nyx-test exec test-client -- \
  curl -v --socks5-hostname ${PROXY_IP}:9050 http://example.com
```

## Known curl SOCKS5 Issues

curl's SOCKS5 implementation may have quirks:
1. **DNS resolution**: Use `--socks5-hostname` for remote DNS
2. **Protocol version**: Some versions send SOCKS4 first
3. **Timeout handling**: curl may timeout before server responds

## Debug Checklist

- [ ] Pull latest code with improved logging
- [ ] Rebuild Docker image
- [ ] Redeploy to Kubernetes
- [ ] Run debug-socks5.sh script
- [ ] Check nyx-proxy detailed logs
- [ ] Check nyx-daemon logs for errors
- [ ] Test with alternative SOCKS5 clients
- [ ] Verify Unix socket permissions
- [ ] Check iptables/CNI rules
- [ ] Test direct pod-to-pod (bypass Service)

## Success Criteria

**SOCKS5 handshake successful when logs show:**
```
SOCKS5 new connection from 10.240.1.3:XXXXX
SOCKS5 [10.240.1.3:XXXXX] starting authentication handshake
SOCKS5 client greeting: version=0x05, nmethods=1, methods=[0]
SOCKS5 selected auth method: 0x00 (no-auth)
SOCKS5 authentication handshake successful
SOCKS5 [10.240.1.3:XXXXX] authentication successful
SOCKS5 request header: version=0x05, cmd=0x01, rsv=0x00, atyp=0x03
SOCKS5 CONNECT request parsed: target=example.com:80 (atyp=0x03)
SOCKS5 Mix connection established to example.com:80 (StreamID: ...)
```

## Troubleshooting Flow

```
Connection Established?
  ├─ NO → Check Service, CNI, iptables
  └─ YES → Check logs for "new connection"
             ├─ Missing → Check nyx-proxy process/health
             └─ Present → Check for "starting authentication"
                           ├─ Missing → Timeout/delay issue
                           └─ Present → Check for "client greeting"
                                       ├─ Missing → EOF/client issue
                                       │           → Try alternative client
                                       └─ Present → Check version/format
                                                   → May need protocol fix
```
