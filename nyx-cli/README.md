# Nyx CLI

Command line interface for interacting with Nyx daemon and network operations.

## Features

- **Daemon Management**: Start, stop, and configure Nyx daemon instances
- **Network Operations**: Create circuits, send messages, manage streams
- **Configuration**: Load and manage configuration files
- **Monitoring**: View network status, performance metrics, and logs
- **I18n Support**: Multi-language interface support

## Installation

```bash
cargo build --release
./target/release/nyx-cli --help
```

## Usage

### Basic Commands

```bash
# Show daemon information
nyx-cli info

# Reload configuration
nyx-cli reload-config

# Update configuration with key-value pairs
nyx-cli update-config --set log_level="debug" --set max_connections=100

# Update configuration from a JSON file
nyx-cli update-config --file config.json

# List configuration versions
nyx-cli list-versions

# Rollback to a previous configuration version
nyx-cli rollback 5

# Create a configuration snapshot
nyx-cli snapshot --description "Pre-production config"

# Subscribe to daemon events (press Ctrl-C to stop)
nyx-cli events

# Subscribe to specific event types
nyx-cli events --types connection,error

# Show current frame size limit
nyx-cli frame-limit

# Set frame size limit (1024-67108864 bytes)
nyx-cli frame-limit --set 16777216

# Get compliance report
nyx-cli compliance

# Get detailed compliance report in JSON format
nyx-cli compliance --format json --detailed

# Fetch Prometheus metrics
nyx-cli prometheus-get http://localhost:9090/metrics
```

### Configuration Management

```bash
# Show effective CLI configuration
nyx-cli config show

# Write a template nyx.toml configuration file
nyx-cli config write-template

# Write template to a specific path
nyx-cli config write-template --path /path/to/nyx.toml --force

# Validate a configuration file
nyx-cli config validate

# Validate with strict checks (including connectivity)
nyx-cli config validate --path nyx.toml --strict
```

### Configuration

The CLI reads configuration from multiple sources (in order of priority):
1. Command line arguments (highest priority)
   - `--endpoint`: Override daemon endpoint
   - `--timeout-ms`: Override request timeout
   - `--token`: Override authentication token
2. Environment variables
   - `NYX_CONTROL_TOKEN` or `NYX_TOKEN`: Authentication token
   - `NYX_DAEMON_ENDPOINT`: Daemon endpoint
   - `NYX_REQUEST_TIMEOUT_MS`: Request timeout
   - `NYX_DAEMON_COOKIE`: Path to cookie file
   - `NYX_CONFIG`: Path to configuration file
3. Cookie file (Tor-style authentication)
   - Windows: `%APPDATA%\nyx\control.authcookie`
   - Unix: `~/.nyx/control.authcookie`
4. Configuration files (searched in order)
   - `$NYX_CONFIG` (if set)
   - `./nyx.toml` (current directory)
   - Windows: `%APPDATA%\nyx\nyx.toml`
   - Unix: `$XDG_CONFIG_HOME/nyx/nyx.toml` or `~/.config/nyx/nyx.toml`

### Authentication

The CLI supports multiple authentication methods:
- **Cookie file**: Tor-style authentication (recommended for local development)
  ```bash
  # Generate a cookie file
  nyx-cli gen-cookie
  
  # Generate with custom path and length
  nyx-cli gen-cookie --path /custom/path --length 64 --force
  ```
- **API tokens**: Via `--token`, `NYX_CONTROL_TOKEN`, or `NYX_TOKEN` environment variables
- **Configuration file**: Token stored in `[cli]` section of nyx.toml
- **Named pipe authentication** (Windows default): `\\.\pipe\nyx-daemon`
- **Unix socket authentication** (Unix default): `/tmp/nyx.sock` or similar

## Architecture

The CLI communicates with the Nyx daemon through:
- **gRPC** (when available, currently disabled to avoid C dependencies)
- **Pure Rust IPC** (default implementation)
- **JSON-RPC over Unix sockets/Named pipes**

## API Bindings

Previously, this crate included generated gRPC API bindings. These have been removed
to eliminate dependencies on `ring` and other C libraries. The CLI now uses a pure
Rust communication protocol with the daemon.

If gRPC support is needed in the future, the bindings can be regenerated using:
```bash
# This is currently disabled
# protoc --rust_out=src/ --grpc_out=src/ --plugin=protoc-gen-grpc=`which grpc_rust_plugin` api.proto
```

## Development

### Building

```bash
cargo build
```

### Testing

```bash
cargo test
```

### Running with specific endpoints

```bash
# Connect to specific daemon endpoint
nyx-cli --endpoint "127.0.0.1:9090" info

# Use custom timeout
nyx-cli --timeout-ms 5000 info

# Provide authentication token
nyx-cli --token "your-secret-token" info

# Combine multiple options
nyx-cli --endpoint "\\.\pipe\nyx-custom" --timeout-ms 3000 --token "token123" reload-config
```

## Platform Support

- **Linux**: Unix domain sockets, systemd integration
- **macOS**: Unix domain sockets, launchd integration  
- **Windows**: Named pipes, Windows service integration
- **FreeBSD/OpenBSD**: Unix domain sockets

## Security

The CLI implements several security measures:
- Token-based authentication
- Encrypted communication channels
- Secure configuration file handling
- Input validation and sanitization

## License

Licensed under either of:
- Apache License, Version 2.0
- MIT License

at your option.
