# NyxNet API Reference

**Last Updated**: October 7, 2025  
**API Version**: v1.0  
**Protocol**: gRPC (no TLS), JSON-RPC 2.0, SOCKS5

[日本語版](./04_API_REFERENCE.md)

---

## Overview

NyxNet provides three API interfaces:

1. **gRPC API** (`NyxControl`, `SessionService`): Rich control plane for stream management, configuration, telemetry
2. **JSON-RPC 2.0 API**: Daemon control over Unix socket (Linux/macOS) or Named Pipe (Windows)
3. **SOCKS5/HTTP CONNECT Proxy**: Standard proxy protocol for application integration

---

## gRPC API (Control Plane)

### Connection Information

**Endpoint**: `127.0.0.1:50051` (default, configurable in `nyx.toml`)  
**Protocol**: gRPC over HTTP/2 (no TLS - assumes local-only or secured external channel)  
**Proto File**: `nyx-sdk/proto/control.proto`

**Authentication**: None (local daemon access assumed). For remote access, use external TLS termination (e.g., Envoy, nginx).

### Service: `NyxControl`

#### 1. GetInfo

**Purpose**: Retrieve node information and daemon status.

**Request**: `Empty` (no parameters)

**Response**: `NodeInfo`

```json
{
  "node_id": "0x1a2b3c4d...",
  "version": "1.0.0",
  "uptime_sec": 86400,
  "bytes_in": 1048576000,
  "bytes_out": 524288000,
  "pid": 12345,
  "active_streams": 3,
  "connected_peers": 12,
  "mix_routes": ["route1", "route2"],
  "performance": {
    "cover_traffic_rate": 5.0,
    "avg_latency_ms": 120.5,
    "packet_loss_rate": 0.001,
    "bandwidth_utilization": 0.65,
    "cpu_usage": 0.15,
    "memory_usage_mb": 256.0,
    "total_packets_sent": 1000000,
    "total_packets_received": 950000,
    "retransmissions": 50,
    "connection_success_rate": 0.995
  },
  "resources": {
    "memory_rss_bytes": 268435456,
    "memory_vms_bytes": 536870912,
    "cpu_percent": 15.2,
    "open_file_descriptors": 128,
    "thread_count": 16,
    "network_bytes_sent": 1073741824,
    "network_bytes_received": 2147483648
  },
  "topology": {
    "total_nodes_known": 500,
    "reachable_nodes": 450,
    "current_region": "us-west",
    "available_regions": ["us-west", "eu-central", "ap-southeast"]
  }
}
```

**Errors**: None (always succeeds with current state)

---

#### 2. GetHealth

**Purpose**: Health check for monitoring systems (Prometheus, Kubernetes liveness probe).

**Request**: `HealthRequest`

```json
{
  "include_details": true
}
```

**Response**: `HealthResponse`

```json
{
  "status": "healthy",
  "checks": [
    {
      "name": "transport",
      "status": "healthy",
      "message": "QUIC transport operational",
      "response_time_ms": 1.2
    },
    {
      "name": "mix_network",
      "status": "healthy",
      "message": "12 peers connected",
      "response_time_ms": 0.8
    },
    {
      "name": "crypto",
      "status": "healthy",
      "message": "Handshake subsystem ok",
      "response_time_ms": 0.3
    }
  ],
  "checked_at": {
    "seconds": 1728345600,
    "nanos": 0
  }
}
```

**Status Values**:
- `healthy`: All systems operational
- `degraded`: Partially functional (some peers down, high latency)
- `unhealthy`: Critical failure (no peers, crypto error)

**Errors**: None (status field indicates health)

---

#### 3. OpenStream

**Purpose**: Establish a new anonymous stream through the mix network.

**Request**: `OpenRequest`

```json
{
  "stream_name": "web_browsing",
  "target_address": "example.com:443",
  "options": {
    "buffer_size": 65536,
    "timeout_ms": 30000,
    "multipath": true,
    "max_paths": 2,
    "path_strategy": "latency_weighted",
    "auto_reconnect": true,
    "max_retry_attempts": 3,
    "compression": false,
    "cipher_suite": "chacha20poly1305"
  }
}
```

**Path Strategies**:
- `latency_weighted`: Select paths by weighted latency distribution
- `random`: Uniform random selection (maximum anonymity)
- `lowest_latency`: Always use fastest path (minimum latency)
- `load_balance`: Distribute traffic evenly across paths

**Response**: `StreamResponse`

```json
{
  "stream_id": 42,
  "status": "open",
  "target_address": "example.com:443",
  "initial_stats": {
    "stream_id": 42,
    "state": "open",
    "bytes_sent": 0,
    "bytes_received": 0,
    "created_at": {"seconds": 1728345600, "nanos": 0}
  },
  "success": true,
  "message": "Stream opened successfully"
}
```

**Errors**:
- `UNAVAILABLE` (14): No mix nodes available
- `DEADLINE_EXCEEDED` (4): Handshake timeout (> 30s)
- `INVALID_ARGUMENT` (3): Invalid target address format
- `RESOURCE_EXHAUSTED` (8): Too many streams (rate limit)

---

#### 4. CloseStream

**Purpose**: Gracefully close a stream.

**Request**: `StreamId`

```json
{
  "id": 42
}
```

**Response**: `Empty` (success)

**Errors**:
- `NOT_FOUND` (5): Stream ID does not exist
- `FAILED_PRECONDITION` (9): Stream already closed

---

#### 5. GetStreamStats

**Purpose**: Retrieve detailed statistics for a stream.

**Request**: `StreamId`

```json
{
  "id": 42
}
```

**Response**: `StreamStats`

```json
{
  "stream_id": 42,
  "target_address": "example.com:443",
  "state": "open",
  "created_at": {"seconds": 1728345600, "nanos": 0},
  "last_activity": {"seconds": 1728345660, "nanos": 0},
  "bytes_sent": 1048576,
  "bytes_received": 2097152,
  "packets_sent": 2048,
  "packets_received": 4096,
  "retransmissions": 10,
  "avg_rtt_ms": 125.5,
  "min_rtt_ms": 80.0,
  "max_rtt_ms": 250.0,
  "bandwidth_mbps": 8.5,
  "packet_loss_rate": 0.005,
  "paths": [
    {
      "path_id": 1,
      "status": "active",
      "rtt_ms": 120.0,
      "bandwidth_mbps": 10.0,
      "bytes_sent": 524288,
      "bytes_received": 1048576,
      "packet_count": 1024,
      "success_rate": 0.995
    },
    {
      "path_id": 2,
      "status": "backup",
      "rtt_ms": 180.0,
      "bandwidth_mbps": 5.0,
      "bytes_sent": 524288,
      "bytes_received": 1048576,
      "packet_count": 1024,
      "success_rate": 0.990
    }
  ],
  "connection_errors": 0,
  "timeout_errors": 0,
  "last_error": "",
  "timestamp": {"seconds": 1728345660, "nanos": 0}
}
```

**Stream States**:
- `idle`: Created but not yet connected
- `open`: Fully established bidirectional stream
- `half_closed_local`: Local endpoint sent FIN
- `half_closed_remote`: Remote endpoint sent FIN
- `closed`: Fully closed

**Errors**:
- `NOT_FOUND` (5): Stream ID does not exist

---

#### 6. ListStreams

**Purpose**: Enumerate all active streams.

**Request**: `Empty`

**Response**: Server-streaming `StreamStats` (one per stream)

**Example** (pseudo-stream):

```
→ StreamStats { stream_id: 1, target_address: "example.com:443", ... }
→ StreamStats { stream_id: 2, target_address: "api.service.org:8080", ... }
→ StreamStats { stream_id: 3, target_address: "10.0.0.5:22", ... }
(end of stream)
```

**Errors**: None (empty stream if no active streams)

---

#### 7. SendData

**Purpose**: Send data through a stream.

**Request**: `DataRequest`

```json
{
  "stream_id": "42",
  "data": "SGVsbG8gV29ybGQ="  // base64: "Hello World"
}
```

**Response**: `DataResponse`

```json
{
  "success": true,
  "error": "",
  "bytes_sent": 11
}
```

**Errors**:
- `NOT_FOUND` (5): Stream ID does not exist
- `FAILED_PRECONDITION` (9): Stream closed
- `RESOURCE_EXHAUSTED` (8): Send buffer full (backpressure)

---

#### 8. ReceiveData

**Purpose**: Receive data from a stream.

**Request**: `StreamId`

```json
{
  "id": 42
}
```

**Response**: `ReceiveResponse`

```json
{
  "success": true,
  "error": "",
  "data": "SGVsbG8gV29ybGQ=",  // base64
  "bytes_received": 11,
  "more_data_available": false
}
```

**Errors**:
- `NOT_FOUND` (5): Stream ID does not exist
- `DEADLINE_EXCEEDED` (4): No data received within timeout

---

#### 9. SubscribeEvents

**Purpose**: Real-time event stream for monitoring.

**Request**: `EventFilter`

```json
{
  "types": ["stream", "connection", "error"],
  "stream_ids": [42],
  "severity": "info"
}
```

**Response**: Server-streaming `Event`

**Example Events**:

```json
{
  "type": "stream",
  "detail": "Stream opened",
  "timestamp": {"seconds": 1728345600, "nanos": 0},
  "severity": "info",
  "attributes": {"stream_id": "42", "target": "example.com:443"},
  "stream_event": {
    "stream_id": 42,
    "action": "opened",
    "target_address": "example.com:443",
    "event_type": "lifecycle"
  }
}
```

```json
{
  "type": "error",
  "detail": "Connection timeout",
  "timestamp": {"seconds": 1728345700, "nanos": 0},
  "severity": "error",
  "attributes": {"stream_id": "42", "error_code": "TIMEOUT"},
  "stream_event": {
    "stream_id": 42,
    "action": "error",
    "target_address": "example.com:443"
  }
}
```

**Event Types**:
- `stream`: Stream lifecycle events (open, close, data transfer)
- `connection`: Peer connection events
- `error`: Error conditions
- `performance`: Performance alerts (latency spike, packet loss)
- `system`: System-level events (config reload, daemon startup)

**Severity Levels**: `debug`, `info`, `warn`, `error`

---

#### 10. SubscribeStats

**Purpose**: Real-time statistics stream (for dashboards, monitoring).

**Request**: `StatsRequest`

```json
{
  "interval_ms": 1000,
  "metrics": ["bandwidth", "latency", "packet_loss"]
}
```

**Response**: Server-streaming `StatsUpdate` (every `interval_ms`)

```json
{
  "timestamp": {"seconds": 1728345600, "nanos": 0},
  "node_info": { /* NodeInfo */ },
  "stream_stats": [ /* array of StreamStats */ ],
  "custom_metrics": {
    "cover_traffic_pps": 5.0,
    "crypto_ops_per_sec": 1000.0,
    "memory_pool_utilization": 0.75
  }
}
```

---

#### 11. UpdateConfig

**Purpose**: Update daemon configuration dynamically (hot reload).

**Request**: `ConfigUpdate`

```json
{
  "settings": {
    "cover_traffic.rate": "10.0",
    "transport.max_streams": "100"
  },
  "restart_required": false
}
```

**Response**: `ConfigResponse`

```json
{
  "success": true,
  "message": "Configuration updated successfully",
  "validation_errors": []
}
```

**Errors**:
- `INVALID_ARGUMENT` (3): Invalid setting name or value
- `FAILED_PRECONDITION` (9): Restart required for this setting

---

#### 12. ReloadConfig

**Purpose**: Reload configuration from disk (`nyx.toml`).

**Request**: `Empty`

**Response**: `ConfigResponse`

```json
{
  "success": true,
  "message": "Configuration reloaded from nyx.toml",
  "validation_errors": []
}
```

**Errors**:
- `INVALID_ARGUMENT` (3): Invalid TOML syntax
- `NOT_FOUND` (5): Config file not found

---

#### 13. BuildPath

**Purpose**: Compute optimal path through mix network.

**Request**: `PathRequest`

```json
{
  "target": "example.com:443",
  "hops": 3,
  "strategy": "latency_optimized"
}
```

**Strategies**:
- `latency_optimized`: Minimize total latency (default)
- `bandwidth_optimized`: Maximize bottleneck bandwidth
- `reliability_optimized`: Prefer stable, high-uptime nodes

**Response**: `PathResponse`

```json
{
  "path": ["node1_id", "node2_id", "node3_id", "exit_node_id"],
  "estimated_latency_ms": 150.0,
  "estimated_bandwidth_mbps": 10.0,
  "reliability_score": 0.99
}
```

**Errors**:
- `UNAVAILABLE` (14): Insufficient nodes for path
- `INVALID_ARGUMENT` (3): Invalid hop count (must be ≥ 3)

---

#### 14. GetPaths

**Purpose**: List all known paths.

**Request**: `Empty`

**Response**: Server-streaming `PathInfo`

```json
{
  "path_id": 1,
  "hops": ["node1_id", "node2_id", "node3_id"],
  "total_latency_ms": 145.5,
  "min_bandwidth_mbps": 12.0,
  "status": "active",
  "packet_count": 10000,
  "success_rate": 0.995,
  "created_at": {"seconds": 1728345000, "nanos": 0}
}
```

---

#### 15. GetTopology

**Purpose**: Retrieve network topology snapshot.

**Request**: `Empty`

**Response**: `NetworkTopology`

```json
{
  "peers": [ /* array of PeerInfo */ ],
  "paths": [ /* array of PathInfo */ ],
  "total_nodes_known": 500,
  "reachable_nodes": 450,
  "current_region": "us-west",
  "available_regions": ["us-west", "eu-central", "ap-southeast"]
}
```

---

#### 16. GetPeers

**Purpose**: List all connected peers.

**Request**: `Empty`

**Response**: Server-streaming `PeerInfo`

```json
{
  "node_id": "0xabcd1234...",
  "address": "192.0.2.1:50051",
  "latency_ms": 25.5,
  "bandwidth_mbps": 100.0,
  "status": "connected",
  "last_seen": {"seconds": 1728345600, "nanos": 0},
  "connection_count": 1,
  "region": "us-west"
}
```

---

### Service: `SessionService`

#### 1. GetSessionStatus

**Purpose**: Query status of a specific crypto session.

**Request**: `SessionStatusRequest`

```json
{
  "session_id": 1
}
```

**Response**: `SessionStatusResponse`

```json
{
  "session_id": 1,
  "role": "client",
  "state": "established",
  "age_ms": 60000,
  "idle_time_ms": 5000,
  "has_traffic_keys": true,
  "metrics": {
    "bytes_tx": 1048576,
    "bytes_rx": 2097152,
    "frames_tx": 2048,
    "frames_rx": 4096,
    "handshake_duration_ms": 250,
    "established_at_ms": 1728345000000
  }
}
```

**Session States**:
- `idle`: Created, no handshake started
- `client_handshaking`: Client performing handshake
- `server_handshaking`: Server performing handshake
- `established`: Handshake complete, traffic keys derived
- `closing`: Graceful shutdown in progress
- `closed`: Session terminated
- `failed`: Handshake or protocol error

---

#### 2. ListSessions

**Purpose**: Enumerate all active crypto sessions.

**Request**: `ListSessionsRequest`

```json
{
  "state_filter": "established",
  "role_filter": "client"
}
```

**Response**: `ListSessionsResponse`

```json
{
  "sessions": [ /* array of SessionStatusResponse */ ],
  "total_count": 10
}
```

---

#### 3. CloseSession

**Purpose**: Forcefully terminate a session.

**Request**: `SessionStatusRequest`

```json
{
  "session_id": 1
}
```

**Response**: `Empty`

**Errors**:
- `NOT_FOUND` (5): Session ID does not exist

---

## JSON-RPC 2.0 API (Daemon Control)

### Connection Information

**Endpoint**:
- **Linux/macOS**: `/tmp/nyx.sock` (Unix domain socket)
- **Windows**: `\\.\pipe\nyx-daemon` (Named Pipe)

**Protocol**: JSON-RPC 2.0 over IPC

**Authentication**: Optional static token (configured in `nyx.toml`)

### Request Format

```json
{
  "jsonrpc": "2.0",
  "id": "request-1",
  "method": "get_info",
  "params": {}
}
```

**Optional Auth**:

```json
{
  "jsonrpc": "2.0",
  "id": "request-2",
  "auth": "your-static-token",
  "method": "reload_config",
  "params": {}
}
```

### Response Format

**Success**:

```json
{
  "jsonrpc": "2.0",
  "id": "request-1",
  "result": {
    "node_id": "0x1a2b3c4d...",
    "version": "1.0.0",
    "uptime_sec": 86400
  }
}
```

**Error**:

```json
{
  "jsonrpc": "2.0",
  "id": "request-2",
  "error": {
    "code": -32600,
    "message": "Invalid request",
    "data": "Missing required field: target_address"
  }
}
```

### Error Codes

| Code | Meaning | Description |
|------|---------|-------------|
| -32700 | Parse error | Invalid JSON |
| -32600 | Invalid request | Malformed JSON-RPC request |
| -32601 | Method not found | Unknown method name |
| -32602 | Invalid params | Invalid or missing parameters |
| -32603 | Internal error | Internal daemon error |
| -32000 | Authentication failed | Invalid or missing auth token |
| -32001 | Rate limit exceeded | Too many requests |
| -32002 | Resource not found | Stream ID or config key not found |

### Methods

#### get_info

**Purpose**: Get daemon information.

**Request**:

```json
{
  "jsonrpc": "2.0",
  "id": "1",
  "method": "get_info",
  "params": {}
}
```

**Response**:

```json
{
  "jsonrpc": "2.0",
  "id": "1",
  "result": {
    "node_id": "0x1a2b3c4d...",
    "version": "1.0.0",
    "uptime_sec": 86400
  }
}
```

---

#### reload_config

**Purpose**: Reload `nyx.toml` configuration.

**Request**:

```json
{
  "jsonrpc": "2.0",
  "id": "2",
  "auth": "your-token",
  "method": "reload_config",
  "params": {}
}
```

**Response**:

```json
{
  "jsonrpc": "2.0",
  "id": "2",
  "result": {
    "success": true,
    "message": "Configuration reloaded"
  }
}
```

---

#### update_config

**Purpose**: Update specific configuration settings.

**Request**:

```json
{
  "jsonrpc": "2.0",
  "id": "3",
  "auth": "your-token",
  "method": "update_config",
  "params": {
    "settings": {
      "cover_traffic.rate": 10.0,
      "transport.max_streams": 100
    }
  }
}
```

**Response**:

```json
{
  "jsonrpc": "2.0",
  "id": "3",
  "result": {
    "success": true,
    "message": "Configuration updated",
    "validation_errors": []
  }
}
```

---

#### subscribe_events

**Purpose**: Subscribe to event stream (long-lived connection).

**Request**:

```json
{
  "jsonrpc": "2.0",
  "id": "4",
  "method": "subscribe_events",
  "params": {
    "types": ["stream", "error"]
  }
}
```

**Response**: Stream of events (newline-delimited JSON)

```json
{"type":"stream","detail":"Stream 42 opened","timestamp":1728345600}
{"type":"error","detail":"Connection timeout on stream 42","timestamp":1728345700}
```

---

#### health

**Purpose**: Health check endpoint.

**Request**:

```json
{
  "jsonrpc": "2.0",
  "id": "5",
  "method": "health",
  "params": {}
}
```

**Response**:

```json
{
  "jsonrpc": "2.0",
  "id": "5",
  "result": {
    "healthy": true,
    "timestamp": "2025-10-07T12:00:00Z",
    "components": {
      "transport": "healthy",
      "mix_network": "healthy",
      "crypto": "healthy"
    }
  }
}
```

---

#### get_system_info

**Purpose**: Detailed system resource usage.

**Request**:

```json
{
  "jsonrpc": "2.0",
  "id": "6",
  "method": "get_system_info",
  "params": {}
}
```

**Response**:

```json
{
  "jsonrpc": "2.0",
  "id": "6",
  "result": {
    "uptime": 86400,
    "version": "1.0.0",
    "build_time": "2025-10-01T00:00:00Z",
    "memory_usage": 268435456
  }
}
```

---

## SOCKS5 Proxy API

### Connection Information

**Endpoint**: `127.0.0.1:1080` (default, configurable in `nyx.toml`)  
**Protocol**: SOCKS5 (RFC 1928)

**Authentication**: No authentication (method 0x00)

### Supported Commands

- `CONNECT` (0x01): Establish TCP connection
- `BIND` (0x02): Not supported (returns error 0x07)
- `UDP ASSOCIATE` (0x03): Not supported (returns error 0x07)

### Connection Flow

#### 1. Client Greeting

```
+----+----------+----------+
|VER | NMETHODS | METHODS  |
+----+----------+----------+
| 1  |    1     | 1 to 255 |
+----+----------+----------+

VER: 0x05 (SOCKS5)
NMETHODS: 0x01
METHODS: 0x00 (No authentication)
```

#### 2. Server Choice

```
+----+--------+
|VER | METHOD |
+----+--------+
| 1  |   1    |
+----+--------+

VER: 0x05
METHOD: 0x00 (No authentication)
```

#### 3. Client Connection Request

```
+----+-----+-------+------+----------+----------+
|VER | CMD |  RSV  | ATYP | DST.ADDR | DST.PORT |
+----+-----+-------+------+----------+----------+
| 1  |  1  | 0x00  |  1   | Variable |    2     |
+----+-----+-------+------+----------+----------+

VER: 0x05
CMD: 0x01 (CONNECT)
RSV: 0x00 (Reserved)
ATYP: 0x01 (IPv4), 0x03 (Domain), 0x04 (IPv6)
DST.ADDR: Target address
DST.PORT: Target port (network byte order)
```

**Example** (Connect to `example.com:443`):

```
05 01 00 03 0b 65 78 61 6d 70 6c 65 2e 63 6f 6d 01 bb
```

#### 4. Server Response

```
+----+-----+-------+------+----------+----------+
|VER | REP |  RSV  | ATYP | BND.ADDR | BND.PORT |
+----+-----+-------+------+----------+----------+
| 1  |  1  | 0x00  |  1   | Variable |    2     |
+----+-----+-------+------+----------+----------+

VER: 0x05
REP: 0x00 (Success), 0x01-0x08 (Errors)
```

**Reply Codes**:
- `0x00`: Succeeded
- `0x01`: General SOCKS server failure
- `0x02`: Connection not allowed by ruleset
- `0x03`: Network unreachable
- `0x04`: Host unreachable
- `0x05`: Connection refused
- `0x06`: TTL expired
- `0x07`: Command not supported
- `0x08`: Address type not supported

#### 5. Data Transfer

After successful reply (0x00), client and server exchange raw TCP data bidirectionally. All traffic is routed through NyxNet's mix network transparently.

---

## HTTP CONNECT Proxy API

### Connection Information

**Endpoint**: `127.0.0.1:8080` (default, configurable)  
**Protocol**: HTTP/1.1 CONNECT method

**Note**: Implemented in Go (`nyx-http-proxy/main.go`), zero C/C++ dependencies.

### Connection Flow

#### 1. Client Request

```http
CONNECT example.com:443 HTTP/1.1
Host: example.com:443
Proxy-Connection: Keep-Alive
```

#### 2. Server Response (Success)

```http
HTTP/1.1 200 Connection Established
```

#### 3. Server Response (Error)

```http
HTTP/1.1 502 Bad Gateway
Content-Type: text/plain

Connection failed: timeout
```

**Status Codes**:
- `200 Connection Established`: Success
- `400 Bad Request`: Malformed request
- `502 Bad Gateway`: Upstream connection failed
- `503 Service Unavailable`: No mix nodes available
- `504 Gateway Timeout`: Connection timeout

#### 4. Data Transfer

After `200` response, tunnel is established. Client sends TLS ClientHello (or other protocol data) directly through the tunnel.

---

## Rate Limiting

### Global Limits

| Resource | Limit | Window |
|----------|-------|--------|
| New streams per second | 10 | 1s |
| Total active streams | 100 | N/A |
| API requests per second (gRPC) | 100 | 1s |
| API requests per second (JSON-RPC) | 50 | 1s |
| Event subscriptions | 5 | N/A |

**Note**: Limits are configurable in `nyx.toml` under `[rate_limits]`.

### Rate Limit Headers (HTTP Proxy)

```http
X-RateLimit-Limit: 100
X-RateLimit-Remaining: 85
X-RateLimit-Reset: 1728345660
```

### Rate Limit Error (gRPC)

```
Status: RESOURCE_EXHAUSTED (8)
Message: "Rate limit exceeded: 10 streams/sec"
Details: retry_after_ms=1000
```

---

## Versioning and Compatibility

### API Version

Current: **v1.0**

**Version Negotiation**:
- gRPC: Custom metadata `x-nyx-api-version: v1.0`
- JSON-RPC: Include `api_version` in params
- SOCKS5/HTTP: No versioning (stable protocol)

### Backward Compatibility

- **Stable APIs**: gRPC `NyxControl` service, SOCKS5, HTTP CONNECT (no breaking changes)
- **Unstable APIs**: `SessionService` (may change in future releases)

### Deprecation Policy

1. **Announce**: Deprecation notice in release notes (6 months before removal)
2. **Warn**: Log warnings when deprecated API is used
3. **Remove**: Remove in next major version (e.g., v2.0)

---

## Client Libraries

### Official SDKs

- **Rust**: `nyx-sdk` crate (statically typed, async/await)
- **WASM**: `nyx-sdk-wasm` (for browsers, WebAssembly)

**Example** (Rust):

```rust
use nyx_sdk::NyxClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = NyxClient::connect("http://127.0.0.1:50051").await?;
    
    let info = client.get_info().await?;
    println!("Node ID: {}", info.node_id);
    
    let stream = client.open_stream("example.com:443").await?;
    stream.send(b"GET / HTTP/1.1\r\n\r\n").await?;
    let data = stream.receive().await?;
    println!("Received: {:?}", data);
    
    Ok(())
}
```

### Third-Party Integration

For languages without official SDK, use:
- **gRPC**: Generate clients from `control.proto` (supports 10+ languages)
- **JSON-RPC**: Standard HTTP client with JSON serialization
- **SOCKS5**: Standard SOCKS5 library (available in all major languages)

---

## Disclaimer: Inferred Content

The following information is reasonably inferred from code and typical patterns:

- **Rate limits**: Estimated reasonable defaults (actual values may differ)
- **Error messages**: Typical error strings (actual may vary)
- **Performance characteristics**: Based on similar systems

For precise specifications, consult the source code in `nyx-sdk/proto/control.proto` and `nyx-daemon/src/main.rs`.
