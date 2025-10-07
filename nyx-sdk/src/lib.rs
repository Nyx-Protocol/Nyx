#![forbid(unsafe_code)]
#![doc = include_str!("../README.md")]

//! # Nyx SDK
//!
//! Production-ready SDK for building applications that integrate with the Nyx anonymity network.
//!
//! ## Features
//!
//! - **Pure Rust**: Zero C/C++ dependencies, fully memory-safe
//! - **Async/Await**: Built on Tokio for high-performance async I/O
//! - **Type-Safe**: Strong type system prevents common errors
//! - **Rich Errors**: Comprehensive error handling with context and categorization
//! - **Stream API**: High-level stream abstraction with statistics and metadata
//! - **Daemon Client**: JSON-RPC client for daemon control
//! - **Connection Management**: Connection pooling, health checks, and auto-reconnection
//! - **Middleware System**: Pluggable request/response interceptors
//! - **Rate Limiting**: Token bucket rate limiter with configurable policies
//! - **Retry Logic**: Automatic retry with exponential backoff
//! - **Configuration**: Environment-based and profile-based configuration
//! - **Telemetry**: Built-in metrics collection and structured logging
//! - **Cross-Platform**: Works on Unix and Windows
//!
//! ## Quick Start
//!
//! ```no_run
//! use nyx_sdk::{NyxStream, Result};
//! use bytes::Bytes;
//!
//! # async fn example() -> Result<()> {
//! // Create a pair of connected streams
//! let (mut sender, mut receiver) = NyxStream::pair(1024);
//!
//! // Send data
//! sender.send(Bytes::from("Hello, Nyx!")).await?;
//!
//! // Receive data
//! if let Some(data) = receiver.recv().await? {
//!     println!("Received: {:?}", data);
//! }
//!
//! // Check statistics
//! let stats = sender.stats();
//! println!("Sent {} bytes", stats.bytes_sent);
//! # Ok(())
//! # }
//! ```
//!
//! ## Daemon Client
//!
//! ```no_run
//! use nyx_sdk::{DaemonClient, SdkConfig, Result};
//!
//! # async fn example() -> Result<()> {
//! let config = SdkConfig::default();
//! let client = DaemonClient::new_with_auto_token(config).await;
//!
//! let info = client.get_info().await?;
//! println!("Daemon info: {:?}", info);
//! # Ok(())
//! # }
//! ```
//!
//! ## Error Handling
//!
//! ```no_run
//! use nyx_sdk::{Error, Result};
//!
//! # async fn operation() -> Result<String> { Ok("result".into()) }
//! # async fn example() -> Result<()> {
//! match operation().await {
//!     Ok(result) => println!("Success: {}", result),
//!     Err(e) if e.is_retryable() => {
//!         println!("Retryable error: {}", e);
//!         // Implement retry logic
//!     }
//!     Err(e) => println!("Fatal error: {}", e),
//! }
//! # Ok(())
//! # }
//! ```
//!
//! ## Documentation
//!
//! - [`GUIDE.md`](https://github.com/SeleniaProject/NyxNet/blob/main/nyx-sdk/GUIDE.md) - Complete guide with examples
//! - [`GUIDE-ja.md`](https://github.com/SeleniaProject/NyxNet/blob/main/nyx-sdk/GUIDE-ja.md) - 日本語ガイド
//!
//! ## Core Types
//!
//! - [`SdkConfig`] - SDK configuration with builder pattern
//! - [`NyxStream`] - High-level stream abstraction
//! - [`DaemonClient`] - Daemon JSON-RPC client
//! - [`Error`] - Rich error type with context
//! - [`Result<T>`] - Convenience type alias for `Result<T, Error>`

pub mod config;
pub mod daemon;
pub mod error;
pub mod events;
pub mod grpc_client;
pub mod grpc_proto;
pub mod proto;
pub mod reconnect;
pub mod retry;
pub mod stream;

pub use config::SdkConfig;
pub use daemon::DaemonClient;
pub use error::{Error, Result};
pub use events::Event;
pub use grpc_client::{GrpcClientConfig, GrpcClientError, NyxGrpcClient};
pub use proto as api;
pub use stream::NyxStream;
