#![deny(unsafe_code)]
#![cfg_attr(feature = "low_power", allow(unsafe_code))]

// Public module_s for daemon runtime (pure Rust only; no ring/openssl).
pub mod config_manager;
// Re-export commonly used config types
pub use config_manager::LowPowerConfig;
pub mod cmix_integration; // cMix batch processing integration
pub mod config_gossip; // Configuration gossip protocol (§5.4)
pub mod connection_api; // REST API for connection management
pub mod connection_manager; // Connection-level state (congestion control, RTT, rate limiting)
pub mod errors; // Error types for daemon
pub mod event_system;
pub mod grpc_proto; // Generated gRPC protobuf code (Pure Rust via tonic-build)
pub mod grpc_server; // gRPC control server implementation (Pure Rust via tonic)
pub mod http_proxy;
pub mod larmix_feedback; // LARMix++ feedback loop for dynamic hop adjustment
#[cfg(feature = "low_power")]
pub mod low_power;
pub mod metrics;
pub mod multipath_integration; // Multipath scheduling integration
pub mod packet_processor; // Extended packet format processing
pub mod path_builder; // Path builder implementation
pub mod path_performance_test; // Performance testing for paths
pub mod path_recovery; // Path recovery and diagnostics
pub mod prometheus_exporter;
pub mod proof_api; // REST API for proof distribution
pub mod proof_distributor; // RSA accumulator proof distribution system
pub mod proto;
pub mod pure_rust_dht; // Pure Rust DHT for peer discovery and data storage
pub mod pure_rust_p2p;
pub mod push; // Push notification relay implementation
pub mod screen_off_detection;
pub mod session_api; // REST API for session management
pub mod session_manager; // Session and handshake orchestration
pub mod stream_manager; // Stream multiplexing and management
pub mod telemetry_bridge; // OTLP/Prometheus bridge for nyx-stream telemetry // HTTP/SOCKS5 proxy IPC bridge for Mix Network routing

// Re-export with shorter prefixe_s used in main.r_s
pub use config_manager as nyx_daemon_config;
pub use event_system as nyx_daemon_event_s;
#[cfg(feature = "low_power")]
pub use low_power as nyx_daemon_low_power;
