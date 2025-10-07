# Nyx SDK

[![License: MIT OR Apache-2.0](https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue.svg)](LICENSE)
[![Rust](https://img.shields.io/badge/rust-2021-orange.svg)](https://www.rust-lang.org)

高性能な匿名化ネットワークプロトコル Nyx 用の包括的な Rust SDK。

## 📚 Documentation

- **[Complete Guide (English)](GUIDE.md)** - Comprehensive documentation with examples
- **[完全ガイド (日本語)](GUIDE-ja.md)** - 日本語の完全なドキュメント
- **[API Documentation](https://docs.rs/nyx-sdk)** - API reference (coming soon)

## ✨ Features

### Core Capabilities
- **Pure Rust Implementation**: Zero C/C++ dependencies for maximum security and reliability
- **Async/Await Support**: Built on Tokio for high-performance async I/O
- **Type-Safe APIs**: Strong type system prevents common errors at compile time
- **Cross-Platform**: Works seamlessly on Unix (Linux, macOS) and Windows

### Stream Management
- Lightweight async stream adapter over `nyx-stream`
- Automatic statistics collection (bytes/messages sent/received)
- Rich metadata support with custom key-value pairs
- Configurable timeouts and buffer sizes
- Connection lifecycle management

### Daemon Integration
- JSON-RPC client for daemon control over Unix Domain Sockets / Named Pipes
- Automatic token discovery (environment variables or cookie files)
- Configuration management (update, reload, version control)
- Event subscription with filtering
- Health monitoring and compliance reporting

### Error Handling
- Rich error types with contextual information
- Error categorization for metrics and logging
- Retryability detection for automatic retry logic
- Fatal error identification

## 🚀 Quick Start

Add to your `Cargo.toml`:

```toml
[dependencies]
nyx-sdk = { path = "../nyx-sdk" }
tokio = { version = "1.37", features = ["full"] }
bytes = "1.5"
```

### Basic Stream Usage

```rust
use nyx_sdk::{NyxStream, Result};
use bytes::Bytes;

#[tokio::main]
async fn main() -> Result<()> {
    // Create a pair of connected streams
    let (mut sender, mut receiver) = NyxStream::pair(1024);

    // Send data
    sender.send(Bytes::from("Hello, Nyx!")).await?;

    // Receive data with timeout
    if let Some(data) = receiver.recv_with_timeout(5000).await? {
        println!("Received: {:?}", data);
    }

    // Check statistics
    let stats = sender.stats();
    println!("Sent {} bytes in {} messages", stats.bytes_sent, stats.messages_sent);

    Ok(())
}
```

### Daemon Client Usage

```rust
use nyx_sdk::{DaemonClient, SdkConfig, Result};

#[tokio::main]
async fn main() -> Result<()> {
    // Create configuration with builder pattern
    let config = SdkConfig::builder()
        .request_timeout_ms(15000)
        .auto_reconnect(true)
        .build()?;

    // Create client with auto-discovered token
    // Checks: NYX_CONTROL_TOKEN → NYX_TOKEN → cookie file
    let client = DaemonClient::new_with_auto_token(config).await;

    // Get daemon information
    let info = client.get_info().await?;
    println!("Daemon info: {:?}", info);

    // Update configuration
    use serde_json::json;
    let mut settings = serde_json::Map::new();
    settings.insert("log_level".into(), json!("debug"));
    
    let response = client.update_config(settings).await?;
    println!("Config updated: {}", response.success);

    Ok(())
}
```

### Event Subscription

```rust
use nyx_sdk::{DaemonClient, SdkConfig, Result};

#[tokio::main]
async fn main() -> Result<()> {
    let config = SdkConfig::default();
    let client = DaemonClient::new_with_auto_token(config).await;

    // Subscribe to specific event types
    let mut events = client.subscribe_events(
        Some(vec!["connection".into(), "error".into()])
    ).await?;

    // Process events
    while let Ok(event) = events.recv().await {
        println!("[{}] {}", event.event_type, event.detail);
    }

    Ok(())
}
```

## 📖 Examples

Comprehensive examples are available in the `examples/` directory:

- **`basic_stream.rs`** - Basic stream operations with statistics
- **`daemon_client.rs`** - Daemon client operations and configuration
- **`event_subscription.rs`** - Event handling and filtering
- **`error_handling.rs`** - Error handling patterns and retry logic
- **`stream_metadata.rs`** - Stream metadata and monitoring

Run an example:
```bash
cargo run --example basic_stream
cargo run --example daemon_client
```

## 🔧 Configuration

### Builder Pattern (Recommended)

```rust,no_run
use nyx_sdk::{SdkConfig, Result};

# async fn example() -> Result<()> {
let config = SdkConfig::builder()
    .daemon_endpoint("/var/run/nyx.sock")
    .request_timeout_ms(15000)
    .auto_reconnect(true)
    .max_reconnect_attempts(3)
    .enable_logging(true)
    .build()?;
# Ok(())
# }
```

### From TOML File

```rust,no_run
use nyx_sdk::{SdkConfig, Result};

# async fn example() -> Result<()> {
let config = SdkConfig::from_file("config.toml").await?;
# Ok(())
# }
```

### Configuration Options

| Option | Type | Default | Description |
|--------|------|---------|-------------|
| `daemon_endpoint` | String | Platform-specific | Socket path or named pipe |
| `request_timeout_ms` | u64 | 10000 | Request timeout in milliseconds |
| `max_request_size` | usize | 1MB | Maximum request size |
| `max_response_size` | usize | 10MB | Maximum response size |
| `auto_reconnect` | bool | true | Enable automatic reconnection |
| `max_reconnect_attempts` | u32 | 5 | Maximum reconnection attempts |
| `reconnect_delay_ms` | u64 | 1000 | Initial reconnection delay |
| `enable_logging` | bool | false | Enable request/response logging |

## 🛡️ Error Handling

The SDK provides rich error types with context:

```rust,no_run
use nyx_sdk::{Error, Result};

# async fn operation() -> Result<String> { Ok("test".into()) }
# async fn example() -> Result<()> {
match operation().await {
    Ok(result) => println!("Success: {:?}", result),
    Err(Error::Timeout { duration_ms }) => {
        println!("Timed out after {}ms", duration_ms);
    }
    Err(Error::AuthenticationFailed(msg)) => {
        println!("Auth failed: {}", msg);
    }
    Err(e) if e.is_retryable() => {
        println!("Retryable error: {}", e);
        // Implement retry logic
    }
    Err(e) => println!("Fatal error: {}", e),
}
# Ok(())
# }
```

## 🎯 Best Practices

1. **Use Builder Pattern** for configuration
2. **Handle Errors Appropriately** - check retryability
3. **Use Timeouts** for network operations
4. **Close Resources Explicitly** - don't rely on Drop
5. **Monitor Stream Health** - check statistics and idle time
6. **Use Auto-Discovery** for tokens when possible

See the [complete guide](GUIDE.md) for detailed best practices.

## 🔌 Features

- `reconnect` - Enable backoff policy utilities
- `metrics` - Integrate with `nyx-core/telemetry`
- `grpc-backup` - Legacy gRPC compatibility (intentionally disabled in favor of pure Rust JSON-RPC)

## Architecture

The SDK provides a layered architecture:
- Application Code uses the Nyx SDK
- Nyx SDK contains Config, Stream, Client, and Error modules
- Nyx SDK communicates with Nyx Daemon via JSON-RPC API

## 🤝 Contributing

Contributions are welcome! Please read the [contributing guidelines](../CONTRIBUTING.md) first.

## 📝 License

This project is licensed under either of:

- MIT License ([LICENSE-MIT](../LICENSE-MIT) or http://opensource.org/licenses/MIT)
- Apache License, Version 2.0 ([LICENSE-APACHE](../LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)

at your option.

## 🔗 Related Projects

- **[nyx-core](../nyx-core)** - Core Nyx protocol implementation
- **[nyx-stream](../nyx-stream)** - Low-level stream primitives
- **[nyx-daemon](../nyx-daemon)** - Nyx network daemon
- **[nyx-sdk-wasm](../nyx-sdk-wasm)** - WebAssembly SDK for browsers
- **[nyx-mobile-ffi](../nyx-mobile-ffi)** - Mobile platform FFI (iOS/Android)

## 📞 Support

- **Documentation**: See [GUIDE.md](GUIDE.md) for comprehensive documentation
- **Issues**: Report bugs on [GitHub Issues](https://github.com/SeleniaProject/NyxNet/issues)
- **Security**: See [SECURITY.md](../SECURITY.md) for security policy
