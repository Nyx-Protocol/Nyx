# Nyx API Reference

Nyx daemon exposes two control plane APIs:
1. **gRPC API** (recommended) - High-performance, strongly-typed, bidirectional streaming
2. **JSON IPC** (legacy) - Simple newline-delimited JSON over Unix socket/named pipe

---

## gRPC API (Recommended)

### Overview

The gRPC API provides comprehensive control over the Nyx daemon with:
- **Strong typing** via Protocol Buffers
- **Streaming support** for real-time events and statistics
- **TLS/mTLS support** via rustls (Pure Rust, zero C/C++ dependencies)
- **Automatic reconnection** and exponential backoff in SDK clients

### Connection

**Default endpoint**: `127.0.0.1:50051`

Configure via:
- Environment: `NYX_GRPC_ADDR=0.0.0.0:50051`
- Config file: `nyx.toml` → `[daemon]` → `grpc_addr`

### Authentication

**Optional TLS/mTLS**:
- Set `enable_tls = true` in daemon config
- Provide `tls_cert_path` and `tls_key_path` (PEM format)
- For mTLS: Set `enable_mtls = true` and `client_ca_path`

**Token-based auth** (planned):
- Include `authorization` metadata in gRPC requests
- Token discovery same as JSON IPC (see below)

### Services

#### NyxControl Service

Main control plane service with 20 RPCs.

##### Node Information

**`GetInfo()`**
- Request: `Empty`
- Response: `NodeInfo`
- Description: Get daemon status, version, uptime, traffic stats, performance metrics
- Example response fields:
  - `node_id`: Unique node identifier
  - `version`: Daemon version
  - `uptime_sec`: Seconds since daemon start
  - `bytes_in/bytes_out`: Total traffic counters
  - `active_streams`: Current active stream count
  - `connected_peers`: Peer connection count
  - `performance`: CPU, memory, latency, packet loss metrics
  - `resources`: RSS/VMS memory, FD count, thread count
  - `topology`: Peer list, path info, network regions

**`GetHealth(check: string)`**
- Request: `HealthRequest { check: "readiness" | "liveness" }`
- Response: `HealthResponse { status: "healthy" | "degraded" | "unhealthy", message: string }`
- Description: Health check probe for Kubernetes/monitoring
- Use cases:
  - Readiness: Check if daemon can accept new connections
  - Liveness: Check if daemon is responsive (watchdog reset)

##### Stream Management

**`OpenStream(target: string, options: StreamOptions)`**
- Request: `OpenRequest { target: string, options: { priority, timeout_ms, multipath_enabled, ... } }`
- Response: `StreamResponse { stream_id: uint64, assigned_paths: [path_id] }`
- Description: Open new bidirectional stream to target node
- Notes: Returns stream_id for subsequent data operations

**`CloseStream(stream_id: uint64)`**
- Request: `StreamId { stream_id }`
- Response: `Empty`
- Description: Gracefully close stream and release resources

**`GetStreamStats(stream_id: uint64)`**
- Request: `StreamId { stream_id }`
- Response: `StreamStats { stream_id, state, bytes_tx/rx, packets_tx/rx, rtt_ms, loss_rate, ... }`
- Description: Get real-time statistics for specific stream

**`ListStreams()`** (streaming RPC)
- Request: `Empty`
- Response: `stream StreamStats`
- Description: Stream all active streams (emits one StreamStats per stream)
- Pattern: Server-side streaming

**`SendData(stream_id: uint64, data: bytes, sequence: uint64)`**
- Request: `DataRequest { stream_id, data (max 1MB), sequence }`
- Response: `DataResponse { acknowledged_seq, bytes_sent }`
- Description: Send data on established stream

**`ReceiveData(stream_id: uint64)`**
- Request: `StreamId { stream_id }`
- Response: `ReceiveResponse { data: bytes, sequence, more_data }`
- Description: Receive buffered data from stream (non-blocking)

##### Event Subscription

**`SubscribeEvents(filter: EventFilter)`** (streaming RPC)
- Request: `EventFilter { types: [string], stream_ids: [uint64], ... }`
- Response: `stream Event`
- Description: Subscribe to daemon events (connection, handshake, error, etc.)
- Event types:
  - `connection_established`: New peer connection
  - `connection_closed`: Peer disconnected
  - `handshake_success/failure`: Handshake outcome
  - `path_added/removed`: Multipath topology change
  - `cover_traffic_update`: Cover traffic rate adaptation
- Pattern: Server-side streaming, long-lived connection

##### Statistics Subscription

**`SubscribeStats(interval_ms: uint32, metrics: [string])`** (streaming RPC)
- Request: `StatsRequest { interval_ms (default 5000), metrics: ["bandwidth", "latency", ...] }`
- Response: `stream StatsUpdate`
- Description: Real-time performance metrics feed
- Metrics: bandwidth, latency, packet_loss, cpu_usage, memory_usage, cover_traffic_rate
- Pattern: Server-side streaming, periodic updates

##### Configuration Management

**`UpdateConfig(updates: map<string, string>)`**
- Request: `ConfigUpdate { updates: {"max_paths": "8", "cover_traffic_ratio": "0.3"} }`
- Response: `ConfigResponse { applied: [string], errors: [string] }`
- Description: Hot-reload specific config keys without restart
- Atomic: All updates applied or none

**`ReloadConfig()`**
- Request: `Empty`
- Response: `ConfigResponse { applied: [string], errors: [string] }`
- Description: Reload full `nyx.toml` from disk
- Warning: May disconnect active sessions if breaking changes

##### Path Management

**`BuildPath(target: string, constraints: PathConstraints)`**
- Request: `PathRequest { target_node_id, constraints: { max_latency_ms, min_bandwidth_mbps, mix_hops } }`
- Response: `PathResponse { path_id, hops: [node_id], estimated_latency_ms }`
- Description: Request daemon to build custom path with constraints

**`GetPaths()`** (streaming RPC)
- Request: `Empty`
- Response: `stream PathInfo`
- Description: Get all active network paths
- PathInfo fields: path_id, hops, latency, bandwidth, status, packet_count, success_rate

##### Network Topology

**`GetTopology()`**
- Request: `Empty`
- Response: `NetworkTopology { peers: [PeerInfo], paths: [PathInfo], total_nodes_known, reachable_nodes, current_region, available_regions }`
- Description: Get full network topology snapshot

**`GetPeers()`** (streaming RPC)
- Request: `Empty`
- Response: `stream PeerInfo`
- Description: Stream all connected peers
- PeerInfo fields: node_id, address, latency_ms, bandwidth_mbps, status, last_seen, region

#### SessionService

Session lifecycle management (3 RPCs).

**`GetSessionStatus(session_id: uint32)`**
- Request: `SessionStatusRequest { session_id }`
- Response: `SessionStatusResponse { session_id, role, state, age_ms, idle_time_ms, has_traffic_keys, metrics }`
- Description: Get detailed status of specific session
- States: idle, client_handshaking, server_handshaking, established, closing, closed, failed

**`ListSessions(state_filter?: string, role_filter?: string)`**
- Request: `ListSessionsRequest { state_filter: "established", role_filter: "client" }`
- Response: `ListSessionsResponse { sessions: [SessionStatusResponse], total_count }`
- Description: List all sessions with optional filters

**`CloseSession(session_id: uint32)`**
- Request: `SessionStatusRequest { session_id }`
- Response: `Empty`
- Description: Force close specific session

### Error Handling

gRPC status codes:
- `OK (0)`: Success
- `INVALID_ARGUMENT (3)`: Malformed request (e.g., invalid stream_id)
- `NOT_FOUND (5)`: Resource not found (e.g., stream_id doesn't exist)
- `ALREADY_EXISTS (6)`: Duplicate resource (e.g., stream already open)
- `PERMISSION_DENIED (7)`: Authentication failure
- `RESOURCE_EXHAUSTED (8)`: Rate limit or quota exceeded
- `FAILED_PRECONDITION (9)`: Operation not allowed in current state
- `UNAVAILABLE (14)`: Daemon not ready or shutting down
- `INTERNAL (13)`: Internal daemon error

Error details in status message field.

### SDK Usage Example

```rust
use nyx_sdk::grpc_client::GrpcClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Connect to daemon
    let mut client = GrpcClient::connect("http://127.0.0.1:50051").await?;
    
    // Get node info
    let info = client.get_info().await?;
    println!("Daemon version: {}", info.version);
    println!("Active streams: {}", info.active_streams);
    
    // Open stream to peer
    let stream = client.open_stream("peer_node_id_abc123", Default::default()).await?;
    println!("Stream opened: ID = {}", stream.stream_id);
    
    // Send data
    client.send_data(stream.stream_id, b"Hello, Nyx!".to_vec(), 1).await?;
    
    // Subscribe to events
    let mut events = client.subscribe_events(vec!["connection_established".to_string()]).await?;
    while let Some(event) = events.next().await {
        println!("Event: {:?}", event?);
    }
    
    Ok(())
}
```

### Migration from JSON IPC

| JSON IPC Operation | gRPC Equivalent | Notes |
|--------------------|-----------------|-------|
| `get_info` | `GetInfo()` | Richer response with metrics/topology |
| `reload_config` | `ReloadConfig()` | Same semantics |
| `update_config` | `UpdateConfig()` | Structured updates, atomic apply |
| `subscribe_events` | `SubscribeEvents()` | True streaming, no polling |
| N/A | `OpenStream()`, `SendData()`, etc. | New stream APIs |

**Recommended migration path**:
1. Run both APIs in parallel (daemon supports both simultaneously)
2. Migrate monitoring/control clients to gRPC first (simpler use case)
3. Migrate data-plane clients (stream operations)
4. Deprecate JSON IPC in future version (or keep for compatibility)

---

## JSON IPC API (Legacy)

### Overview

Newline-delimited JSON over Unix socket (Unix) or named pipe (Windows). Simple but limited:
- No streaming (polling required)
- No strong typing
- No built-in authentication (token-based)

**Recommended for**: Simple scripts, legacy integrations

### Endpoints

- Unix: `/tmp/nyx.sock`
- Windows: `\\.\\pipe\\nyx-daemon`

### Authentication

Token discovery order:

1. `NYX_DAEMON_TOKEN` environment variable
2. `NYX_DAEMON_COOKIE` file path (or the default path below)
   - Windows: `%APPDATA%/nyx/control.authcookie`
   - Unix: `$HOME/.nyx/control.authcookie`
3. If none is found, a token is generated at boot.

Set `NYX_DAEMON_STRICT_AUTH=1` to require a valid token for privileged operations.

### Request Format

```json
{ "op": "get_info" }
```

Privileged operations must include a `token` field:

```json
{ "op": "reload_config", "token": "<secret>", "path": "nyx.toml" }
```

### Operations

- `get_info`: Return runtime information (equivalent to gRPC `GetInfo`)
- `reload_config` (auth): Reload configuration file (equivalent to gRPC `ReloadConfig`)
- `update_config` (auth): Patch configuration (equivalent to gRPC `UpdateConfig`)
- `list_config_versions` (auth): List config versions (snapshot management)
- `rollback_config` (auth): Rollback to a specific version
- `create_config_snapshot` (auth): Create a snapshot
- `subscribe_events` (auth): Switch the connection to event-stream mode (polling-based)

### Response Format

Success:

```json
{ "ok": true, "data": { "version": "1.0.0", "pid": 12345 } }
```

Error:

```json
{ "ok": false, "error": { "code": "InvalidToken", "message": "token mismatch" } }
```

---

## Metrics Endpoint

If `NYX_PROMETHEUS_ADDR` is set (e.g., `0.0.0.0:9091`), an embedded HTTP server exposes Prometheus metrics at `/metrics`.

**Metrics available**:
- Handshake success/failure/duration
- Path quality (RTT, loss rate, bandwidth per path_id)
- Cover traffic utilization and bytes sent
- cMix batch processing metrics
- Rekey events and failures
- Standard Rust runtime metrics (memory, CPU, GC)

**Example scrape config** (prometheus.yml):
```yaml
scrape_configs:
  - job_name: 'nyx-daemon'
    static_configs:
      - targets: ['localhost:9091']
```

---

## See Also

- **Protobuf definitions**: `nyx-daemon/proto/control.proto`
- **gRPC server implementation**: `nyx-daemon/src/grpc_server.rs`
- **SDK client**: `nyx-sdk/src/grpc_client.rs`
- **Configuration**: `docs/configuration.md`
- **Architecture**: `docs/architecture.md`