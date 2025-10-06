// Integration test module for Nyx end-to-end tests
//
// This module provides test infrastructure for multi-node simulations,
// handshake validation, multipath data transfer, and cover traffic measurement.
//
// Reference: spec/testing/*.md, TODO.md §9.1
//
// ## Test Infrastructure Components
//
// ### 1. Multi-Node Simulations
// - Daemon orchestration with configurable network topology
// - Client connection management across multiple nodes
// - Automatic resource cleanup and graceful shutdown
//
// ### 2. Handshake Validation
// - Hybrid (X25519-Kyber768) handshake verification
// - Forward secrecy property testing
// - Protocol version negotiation testing
//
// ### 3. Multipath Data Transfer
// - Multiple concurrent path establishment
// - Path quality assessment and selection
// - Failover and recovery testing
//
// ### 4. Cover Traffic Measurement
// - Traffic pattern analysis utilities
// - Timing attack resistance verification
// - Bandwidth overhead measurement
//
// ## Usage Example
//
// ```rust
// use nyx_tests::*;
//
// #[tokio::test]
// async fn test_basic_handshake() -> TestResult<()> {
//     let harness = TestHarness::new().await?;
//     let daemon = harness.spawn_daemon("node1", DaemonConfig::default()).await?;
//     let client = harness.connect_client(daemon.address()).await?;
//
//     // Verify handshake completed successfully
//     assert!(client.is_connected());
//     Ok(())
// }
// ```

pub mod test_harness;

// Integration test modules
pub mod integration;

// Re-export common utilities for integration tests
pub use test_harness::{
    ClientHandle, DaemonConfig, DaemonHandle, NetworkConfig, TestHarness, TestNetwork, TestResult,
};
