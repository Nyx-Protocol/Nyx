# Nyx SDK Complete Guide

## Table of Contents

1. [Introduction](#introduction)
2. [Installation](#installation)
3. [Quick Start](#quick-start)
4. [Core Concepts](#core-concepts)
5. [Configuration](#configuration)
6. [Stream API](#stream-api)
7. [Daemon Client](#daemon-client)
8. [Error Handling](#error-handling)
9. [Advanced Usage](#advanced-usage)
10. [Best Practices](#best-practices)
11. [Troubleshooting](#troubleshooting)
12. [API Reference](#api-reference)

## Introduction

The Nyx SDK provides a Rust-native API for building applications that integrate with the Nyx anonymity network. It offers:

- **Pure Rust Implementation**: Zero C/C++ dependencies, fully memory-safe
- **Async/Await Support**: Built on Tokio for high-performance async I/O
- **Type-Safe APIs**: Strong type system prevents common errors
- **Comprehensive Error Handling**: Rich error types with context
- **Stream Abstraction**: High-level stream API with statistics and metadata
- **Daemon Integration**: JSON-RPC client for daemon control
- **Cross-Platform**: Works on Unix (Linux, macOS) and Windows

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
nyx-sdk = { path = "../nyx-sdk" }
tokio = { version = "1.37", features = ["full"] }
bytes = "1.5"
```

## Quick Start

### Basic Stream Usage

```rust
use nyx_sdk::{NyxStream, Result};
use bytes::Bytes;

#[tokio::main]
async fn main() -> Result<()> {
    // Create a pair of connected streams for testing
    let (mut sender, mut receiver) = NyxStream::pair(1024);

    // Send data
    sender.send(Bytes::from("Hello, Nyx!")).await?;

    // Receive data
    if let Some(data) = receiver.recv().await? {
        println!("Received: {:?}", data);
    }

    // Close streams
    sender.close().await?;
    receiver.close().await?;

    Ok(())
}
```

### Daemon Client Usage

```rust
use nyx_sdk::{DaemonClient, SdkConfig, Result};

#[tokio::main]
async fn main() -> Result<()> {
    // Create configuration
    let config = SdkConfig::default();

    // Create client with auto-discovered token
    let client = DaemonClient::new_with_auto_token(config).await;

    // Get daemon information
    let info = client.get_info().await?;
    println!("Daemon info: {:?}", info);

    // Reload configuration
    let result = client.reload_config().await?;
    println!("Config reloaded: {:?}", result);

    Ok(())
}
```

## Core Concepts

### Configuration

The SDK uses `SdkConfig` for all configuration needs. It supports:

- Daemon endpoint configuration (Unix socket or Windows named pipe)
- Timeout settings
- Size limits
- Reconnection policies
- Logging options

### Streams

`NyxStream` provides a high-level abstraction over the underlying network streams with:

- Async send/receive operations
- Automatic statistics collection
- Metadata support
- Timeout handling
- Lifecycle management

### Error Handling

All operations return `Result<T, Error>` where `Error` is a rich enum with:

- Contextual information
- Error categorization
- Retryability indicators
- Fatal error detection

## Configuration

### Using the Builder Pattern

```rust
use nyx_sdk::SdkConfig;

let config = SdkConfig::builder()
    .daemon_endpoint("/var/run/nyx.sock")
    .request_timeout_ms(15000)
    .auto_reconnect(true)
    .max_reconnect_attempts(3)
    .enable_logging(true)
    .build()?;
```

### Loading from File

```rust
let config = SdkConfig::from_file("config.toml").await?;
```

### Saving to File

```rust
let config = SdkConfig::default();
config.save_to_file("config.toml").await?;
```

### Configuration Options

| Option | Type | Default | Description |
|--------|------|---------|-------------|
| `daemon_endpoint` | String | Platform-specific | Socket path or named pipe |
| `request_timeout_ms` | u64 | 10000 | Request timeout in milliseconds |
| `max_request_size` | usize | 1MB | Maximum request size |
| `max_response_size` | usize | 10MB | Maximum response size |
| `auto_reconnect` | bool | true | Enable automatic reconnection |
| `max_reconnect_attempts` | u32 | 5 | Max reconnection attempts |
| `reconnect_delay_ms` | u64 | 1000 | Initial reconnection delay |
| `enable_logging` | bool | false | Enable request/response logging |

## Stream API

### Creating Streams

```rust
// Default configuration
let stream = NyxStream::new();

// Custom configuration
use nyx_stream::AsyncStreamConfig;
let config = AsyncStreamConfig {
    stream_id: 42,
    ..Default::default()
};
let stream = NyxStream::with_config(config);

// Connected pair for testing
let (stream_a, stream_b) = NyxStream::pair(4096);
```

### Sending Data

```rust
// Basic send
stream.send(Bytes::from("data")).await?;

// Send with timeout
stream.send_with_timeout(Bytes::from("data"), 5000).await?;
```

### Receiving Data

```rust
// Basic receive
if let Some(data) = stream.recv().await? {
    println!("Received {} bytes", data.len());
}

// Receive with timeout
match stream.recv_with_timeout(5000).await? {
    Some(data) => println!("Received: {:?}", data),
    None => println!("Stream closed"),
}
```

### Stream Statistics

```rust
let stats = stream.stats();
println!("Bytes sent: {}", stats.bytes_sent);
println!("Bytes received: {}", stats.bytes_received);
println!("Messages sent: {}", stats.messages_sent);
println!("Messages received: {}", stats.messages_received);
println!("Errors: {}", stats.errors);

// Uptime and idle time
if let Some(uptime) = stream.uptime() {
    println!("Stream uptime: {:?}", uptime);
}
if let Some(idle) = stream.idle_time() {
    println!("Time since last activity: {:?}", idle);
}
```

### Stream Metadata

```rust
// Set target
stream.set_target("example.com").await;

// Add custom metadata
stream.add_user_data("key", "value").await;

// Retrieve metadata
let metadata = stream.metadata().await;
println!("Stream ID: {}", metadata.stream_id);
println!("Target: {:?}", metadata.target);
println!("User data: {:?}", metadata.user_data);
```

## Daemon Client

### Authentication

The daemon client supports multiple authentication methods:

```rust
// Auto-discovery (recommended)
// Checks: NYX_CONTROL_TOKEN → NYX_TOKEN → cookie file
let client = DaemonClient::new_with_auto_token(config).await;

// Manual token
let client = DaemonClient::new(config)
    .with_token("your-secret-token");

// Programmatic auto-discovery
let client = DaemonClient::new(config).with_auto_token().await;
```

### Token Discovery Priority

1. `NYX_CONTROL_TOKEN` environment variable
2. `NYX_TOKEN` environment variable  
3. Cookie file at `$NYX_DAEMON_COOKIE` or default path
   - Windows: `%APPDATA%\nyx\control.authcookie`
   - Unix: `~/.nyx/control.authcookie`

### Daemon Operations

#### Get Daemon Info

```rust
let info = client.get_info().await?;
```

#### Reload Configuration

```rust
let result = client.reload_config().await?;
```

#### Update Configuration

```rust
use serde_json::json;

let mut settings = serde_json::Map::new();
settings.insert("log_level".into(), json!("debug"));
settings.insert("max_connections".into(), json!(100));

let response = client.update_config(settings).await?;
if response.success {
    println!("Config updated: {}", response.message);
} else {
    println!("Config update failed: {}", response.message);
    for error in response.validation_errors {
        println!("  - {}", error);
    }
}
```

#### Configuration Versioning

```rust
// List versions
let versions = client.list_versions().await?;

// Create snapshot
let snapshot = client.create_config_snapshot(
    Some("Before major update".to_string())
).await?;

// Rollback to version
let result = client.rollback_config(version_number).await?;
```

#### Event Subscription

```rust
use tokio_stream::StreamExt;

// Subscribe to all events
let mut events = client.subscribe_events(None).await?;

// Subscribe to specific event types
let mut events = client.subscribe_events(
    Some(vec!["connection".into(), "error".into()])
).await?;

// Process events
while let Ok(event) = events.recv().await {
    println!("Event type: {}", event.event_type);
    println!("Details: {}", event.detail);
}
```

#### Compliance Reporting

```rust
let report = client.get_compliance_report().await?;
println!("Compliance report: {:?}", report);
```

## Error Handling

### Error Types

```rust
use nyx_sdk::Error;

match operation().await {
    Ok(result) => println!("Success: {:?}", result),
    Err(Error::Timeout { duration_ms }) => {
        println!("Operation timed out after {}ms", duration_ms);
    }
    Err(Error::Disconnected { reason }) => {
        println!("Disconnected: {}", reason);
    }
    Err(Error::AuthenticationFailed(msg)) => {
        println!("Auth failed: {}", msg);
    }
    Err(e) => println!("Other error: {}", e),
}
```

### Error Categories

```rust
let error = operation().await.unwrap_err();

// Check error properties
if error.is_retryable() {
    println!("This error can be retried");
}

if error.is_fatal() {
    println!("This is a fatal error, should not retry");
}

// Get error category for metrics
let category = error.category();
println!("Error category: {}", category);
```

### Retry Logic

```rust
use tokio::time::{sleep, Duration};

async fn retry_operation<F, T>(mut op: F, max_attempts: u32) -> Result<T>
where
    F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T>>>>,
{
    let mut attempt = 0;
    loop {
        match op().await {
            Ok(result) => return Ok(result),
            Err(e) if e.is_retryable() && attempt < max_attempts => {
                attempt += 1;
                let delay = Duration::from_millis(100 * 2u64.pow(attempt));
                println!("Attempt {} failed, retrying in {:?}", attempt, delay);
                sleep(delay).await;
            }
            Err(e) => return Err(e),
        }
    }
}
```

## Advanced Usage

### Connection Pooling

```rust
use std::sync::Arc;
use tokio::sync::Mutex;

struct ConnectionPool {
    streams: Arc<Mutex<Vec<NyxStream>>>,
    config: AsyncStreamConfig,
}

impl ConnectionPool {
    fn new(size: usize, config: AsyncStreamConfig) -> Self {
        let streams = (0..size)
            .map(|_| NyxStream::with_config(config.clone()))
            .collect();
        
        Self {
            streams: Arc::new(Mutex::new(streams)),
            config,
        }
    }

    async fn get(&self) -> Result<NyxStream> {
        let mut streams = self.streams.lock().await;
        streams.pop()
            .ok_or_else(|| Error::resource_exhausted("No streams available"))
    }

    async fn return_stream(&self, stream: NyxStream) {
        let mut streams = self.streams.lock().await;
        streams.push(stream);
    }
}
```

### Custom Event Handler

```rust
use nyx_sdk::Event;
use std::sync::Arc;

trait EventHandler: Send + Sync {
    async fn handle_event(&self, event: Event);
}

struct LoggingHandler;

impl EventHandler for LoggingHandler {
    async fn handle_event(&self, event: Event) {
        println!("[{}] {}", event.event_type, event.detail);
    }
}

async fn subscribe_with_handler<H: EventHandler + 'static>(
    client: &DaemonClient,
    handler: Arc<H>,
) -> Result<()> {
    let mut events = client.subscribe_events(None).await?;
    
    tokio::spawn(async move {
        while let Ok(event) = events.recv().await {
            handler.handle_event(event).await;
        }
    });
    
    Ok(())
}
```

### Stream Metrics Collection

```rust
use std::time::Duration;
use tokio::time::interval;

async fn collect_metrics(stream: NyxStream) {
    let mut ticker = interval(Duration::from_secs(60));
    
    loop {
        ticker.tick().await;
        
        let stats = stream.stats();
        let metadata = stream.metadata().await;
        
        // Send to metrics system
        metrics::gauge!("stream.bytes_sent", stats.bytes_sent as f64);
        metrics::gauge!("stream.bytes_received", stats.bytes_received as f64);
        metrics::gauge!("stream.messages_sent", stats.messages_sent as f64);
        metrics::gauge!("stream.messages_received", stats.messages_received as f64);
        
        if let Some(uptime) = stream.uptime() {
            metrics::gauge!("stream.uptime_seconds", uptime.as_secs() as f64);
        }
    }
}
```

## Best Practices

### 1. Use Builder Pattern for Configuration

```rust
// Good
let config = SdkConfig::builder()
    .request_timeout_ms(5000)
    .auto_reconnect(true)
    .build()?;

// Avoid
let mut config = SdkConfig::default();
config.request_timeout_ms = 5000;
config.auto_reconnect = true;
// No validation!
```

### 2. Handle Errors Appropriately

```rust
// Good
match client.get_info().await {
    Ok(info) => process(info),
    Err(e) if e.is_retryable() => retry_later(),
    Err(e) => log_fatal_error(e),
}

// Avoid
let info = client.get_info().await.unwrap(); // Panic on error
```

### 3. Use Timeouts for Network Operations

```rust
// Good
stream.send_with_timeout(data, 5000).await?;

// Risky
stream.send(data).await?; // May hang indefinitely
```

### 4. Close Resources Explicitly

```rust
// Good
{
    let mut stream = NyxStream::new();
    // Use stream
    stream.close().await?;
}

// Avoid relying on Drop
let mut stream = NyxStream::new();
// Use stream
// Stream might not close properly
```

### 5. Monitor Stream Health

```rust
async fn monitor_stream(stream: &NyxStream) {
    if let Some(idle) = stream.idle_time() {
        if idle > Duration::from_secs(300) {
            println!("Warning: Stream idle for {:?}", idle);
        }
    }
    
    let stats = stream.stats();
    if stats.errors > 10 {
        println!("Warning: {} errors detected", stats.errors);
    }
}
```

### 6. Use Auto-Discovery for Tokens

```rust
// Good - Works across environments
let client = DaemonClient::new_with_auto_token(config).await;

// Less flexible
let client = DaemonClient::new(config)
    .with_token("hardcoded-token");
```

## Troubleshooting

### Common Issues

#### 1. Connection Refused

```
Error: Io(Os { code: 111, kind: ConnectionRefused, message: "Connection refused" })
```

**Solution**: Ensure the Nyx daemon is running and listening on the correct socket.

```bash
# Check if daemon is running
ps aux | grep nyx-daemon

# Check socket exists
ls -l /tmp/nyx.sock  # Unix
```

#### 2. Timeout Errors

```
Error: Timeout { duration_ms: 10000 }
```

**Solutions**:
- Increase timeout: `config.request_timeout_ms = 30000;`
- Check network connectivity
- Verify daemon is responsive

#### 3. Authentication Failed

```
Error: AuthenticationFailed("Invalid token")
```

**Solutions**:
- Verify token is correct
- Check environment variables: `echo $NYX_TOKEN`
- Verify cookie file exists and is readable
- Regenerate daemon token if needed

#### 4. Stream Closed Unexpectedly

```
Error: Disconnected { reason: "peer closed connection" }
```

**Solutions**:
- Enable auto-reconnect in configuration
- Implement retry logic
- Check daemon logs for errors

#### 5. Serialization Errors

```
Error: Serde(Error("missing field", line: 1, column: 42))
```

**Solutions**:
- Verify daemon API version compatibility
- Check request/response formats
- Update SDK to latest version

### Debug Logging

Enable debug logging to troubleshoot issues:

```rust
use tracing_subscriber;

// Initialize logging
tracing_subscriber::fmt()
    .with_max_level(tracing::Level::DEBUG)
    .init();

// Enable SDK logging
let config = SdkConfig::builder()
    .enable_logging(true)
    .build()?;
```

### Performance Tuning

#### Optimize Timeouts

```rust
// For local daemon
let config = SdkConfig::builder()
    .request_timeout_ms(1000)  // 1 second
    .build()?;

// For remote daemon
let config = SdkConfig::builder()
    .request_timeout_ms(30000)  // 30 seconds
    .build()?;
```

#### Adjust Buffer Sizes

```rust
let config = SdkConfig::builder()
    .max_request_size(10 * 1024 * 1024)   // 10MB
    .max_response_size(50 * 1024 * 1024)  // 50MB
    .build()?;
```

## API Reference

### SdkConfig

Primary configuration struct for the SDK.

**Methods:**
- `default()` - Create default configuration
- `builder()` - Create configuration builder
- `validate()` - Validate configuration
- `from_file(path)` - Load from TOML file
- `save_to_file(path)` - Save to TOML file

### NyxStream

High-level stream abstraction with statistics and metadata.

**Methods:**
- `new()` - Create with default config
- `with_config(config)` - Create with custom config
- `pair(buffer_size)` - Create connected pair
- `send(data)` - Send data
- `send_with_timeout(data, timeout_ms)` - Send with timeout
- `recv()` - Receive data
- `recv_with_timeout(timeout_ms)` - Receive with timeout
- `close()` - Close stream
- `is_closed()` - Check if closed
- `stats()` - Get statistics
- `reset_stats()` - Reset statistics
- `metadata()` - Get metadata
- `set_metadata(metadata)` - Set metadata
- `set_target(target)` - Set target address
- `add_user_data(key, value)` - Add custom metadata
- `uptime()` - Get stream uptime
- `idle_time()` - Get time since last activity

### DaemonClient

Client for daemon JSON-RPC API.

**Methods:**
- `new(config)` - Create client
- `new_with_auto_token(config)` - Create with auto-discovered token
- `with_token(token)` - Set authentication token
- `with_auto_token()` - Auto-discover and set token
- `get_info()` - Get daemon information
- `reload_config()` - Reload daemon configuration
- `update_config(settings)` - Update configuration
- `list_versions()` - List configuration versions
- `rollback_config(version)` - Rollback to version
- `create_config_snapshot(description)` - Create snapshot
- `subscribe_events(types)` - Subscribe to events
- `get_compliance_report()` - Get compliance report

### Error

Rich error type with context and categorization.

**Variants:**
- `Io(Error)` - I/O errors
- `Serde(Error)` - Serialization errors
- `Config(String)` - Configuration errors
- `Protocol(String)` - Protocol errors
- `Stream(String)` - Stream errors
- `Timeout { duration_ms }` - Timeout with duration
- `Disconnected { reason }` - Disconnection with reason
- `NotFound(&str)` - Resource not found
- `AuthenticationFailed(String)` - Authentication failure
- `RateLimited(String)` - Rate limiting
- `InvalidState(String)` - Invalid state
- `ResourceExhausted(String)` - Resource exhaustion
- `UnsupportedCapability(u32)` - Unsupported capability

**Methods:**
- `is_retryable()` - Check if error is retryable
- `is_fatal()` - Check if error is fatal
- `category()` - Get error category

### ErrorCategory

Error categorization for metrics and logging.

**Variants:**
- `Network` - Network-related errors
- `Serialization` - Serialization errors
- `Configuration` - Configuration errors
- `Protocol` - Protocol errors
- `Stream` - Stream errors
- `Timeout` - Timeout errors
- `NotFound` - Not found errors
- `Authentication` - Authentication errors
- `RateLimit` - Rate limiting errors
- `State` - State errors
- `Resource` - Resource errors
- `Capability` - Capability errors

---

## Examples

See the `examples/` directory for complete examples:

- `basic_stream.rs` - Basic stream usage
- `daemon_client.rs` - Daemon client operations
- `event_subscription.rs` - Event handling
- `error_handling.rs` - Error handling patterns
- `connection_pool.rs` - Connection pooling
- `metrics_collection.rs` - Metrics collection

## License

MIT OR Apache-2.0
