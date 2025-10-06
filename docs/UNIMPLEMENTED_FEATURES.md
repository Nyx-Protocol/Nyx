# Unimplemented Features Tracking

This document tracks features that have placeholder implementations or TODO markers in the codebase.

## 🚨 High Priority - Core Functionality

### 1. gRPC Control API Stream Management (nyx-daemon)

**Location**: `nyx-daemon/src/grpc_server.rs`

**Status**: Stub implementations returning mock data

**TODO Items**:
- Line 289: `OpenStream` - Implement actual stream opening logic with connection manager
- Line 314: `CloseStream` - Implement efficient stream_id → connection_id mapping
- Line 371: `ListStreams` - Add `StreamManager::iter_all_streams()` method
- Line 396: `SendData` - Implement actual data sending via StreamManager
- Line 415: `ReceiveData` - Implement actual data reception from StreamManager buffer
- Line 452: `StreamEvents` - Connect to actual event system for stream state changes

**Impact**: Control API clients (nyx-cli, mobile apps) cannot manage streams programmatically

**Workaround**: Stream management currently works through low-level daemon APIs

**Tracking Issue**: #TBD

---

### 2. gRPC Control API Path Management (nyx-daemon)

**Location**: `nyx-daemon/src/grpc_server.rs`

**Status**: Stub implementations returning mock data

**TODO Items**:
- Line 624: `BuildPath` - Integrate with actual PathBuilder for Sphinx circuit construction
- Line 649: `ListPaths` - Integrate with PathBuilder to get actual onion paths
- Line 673: `GetNetworkTopology` - Integrate with DHT/P2P layer for actual mix node topology
- Line 696: `ListPeers` - Integrate with DHT/P2P layer for actual peer list

**Impact**: Cannot build custom Sphinx onion paths or inspect network topology

**Workaround**: Daemon auto-constructs default paths internally

**Tracking Issue**: #TBD

---

### 3. gRPC Control API Session Management (nyx-daemon)

**Location**: `nyx-daemon/src/grpc_server.rs`

**Status**: Partial implementation with missing metrics

**TODO Items**:
- Line 859: Track actual session age (currently returns 0)
- Line 860: Track actual idle time (currently returns 0)
- Line 862: Collect session metrics (bytes transferred, latency, packet loss)
- Line 879: Implement actual session iteration with filters
- Line 899: Implement session closing logic

**Impact**: Session monitoring and debugging capabilities limited

**Workaround**: Use telemetry/metrics backend for aggregate statistics

**Tracking Issue**: #TBD

---

### 4. Config Hot Reload (nyx-daemon)

**Location**: `nyx-daemon/src/grpc_server.rs:600`

**Status**: Stub implementation

**TODO**: Implement actual config file reloading from `nyx.toml` without daemon restart

**Impact**: Configuration changes require daemon restart

**Workaround**: Use `systemctl restart nyx-daemon` or equivalent

**Tracking Issue**: #TBD

---

## 🔶 Medium Priority - Enhanced Features

### 5. HTTP Proxy Anonymous Routing (nyx-daemon)

**Location**: `nyx-daemon/src/http_proxy.rs:167`

**Status**: Direct proxy without onion routing

**TODO**: Integrate with nyx-mix layer for anonymous routing through Sphinx circuits

**Impact**: HTTP proxy traffic is not anonymized (currently a performance-oriented SOCKS5 proxy)

**Workaround**: Use Tor Browser or dedicated anonymization software

**Tracking Issue**: #TBD

---

### 6. Session API Filtering (nyx-daemon)

**Location**: `nyx-daemon/src/session_api.rs:130`

**Status**: Returns all sessions

**TODO**: Implement actual filtering once SessionManager supports listing with predicates

**Impact**: Cannot filter sessions by state/protocol/peer in API calls

**Workaround**: Filter results client-side

**Tracking Issue**: #TBD

---

### 7. DHT Bucket Maintenance (nyx-daemon)

**Location**: `nyx-daemon/src/pure_rust_dht.rs:1009`

**Status**: Basic Kademlia implementation

**TODO**: Refresh stale buckets, ping questionable nodes for improved DHT health

**Impact**: DHT may accumulate stale entries over long uptimes

**Workaround**: Restart daemon periodically in long-running deployments

**Tracking Issue**: #TBD

---

### 8. Plugin Capability Negotiation (nyx-stream)

**Location**: `nyx-stream/src/plugin_dispatch.rs:586`

**Status**: Manual capability registration

**TODO**: Implement plugin manifest parsing to determine required capabilities automatically

**Impact**: Plugin developers must manually register capabilities in code

**Workaround**: Use explicit `register_capability()` calls

**Tracking Issue**: #TBD

---

## 🟢 Low Priority - Future Enhancements

### 9. BIKE KEM Post-Quantum Cryptography (nyx-crypto)

**Location**: `nyx-crypto/src/bike.rs` (entire module)

**Status**: Placeholder returning `Error::NotImplemented`

**TODO**: Implement when a mature Pure Rust BIKE KEM library becomes available

**Impact**: None - ML-KEM-768 (Kyber) is used for post-quantum security

**Alternative**: Use `kyber::*` functions (NIST FIPS 203 standardized)

**Deprecated Since**: v0.1.0

**Tracking Issue**: #TBD

---

### 10. Kademlia RPC Processing (nyx-control)

**Location**: `nyx-control/src/kademlia.rs:346`

**Status**: RPC receiver loop exists, processing not implemented

**TODO**: Process RPC messages and send responses in event loop

**Impact**: Kademlia DHT operations may timeout or fail

**Workaround**: Use alternative peer discovery mechanisms

**Tracking Issue**: #TBD

---

### 11. TLS Configuration for gRPC (nyx-daemon)

**Location**: `nyx-daemon/src/grpc_server.rs:167`

**Status**: Unix domain sockets for local IPC (no TLS needed)

**TODO**: Add TLS configuration when remote gRPC access is needed

**Impact**: None for local control API usage

**Future Use Case**: Remote daemon management over network

**Tracking Issue**: #TBD

---

## 📝 Contributing

When implementing any of these features:

1. Update this document with implementation status
2. Remove corresponding TODO comments from code
3. Add comprehensive tests for new functionality
4. Update API documentation and examples
5. Close or link related tracking issues

## 🔗 Related Documentation

- [Architecture](./architecture.md) - System design overview
- [API Documentation](./api.md) - gRPC and HTTP API reference
- [Configuration](./configuration.md) - Config file options
- [Contributing](../CONTRIBUTING.md) - Development guidelines
