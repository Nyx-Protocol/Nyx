# NyxNet CLI and Daemon User Guide

This guide provides comprehensive instructions for using the NyxNet daemon and command-line interface.

## Table of Contents

- [Overview](#overview)
- [Quick Start](#quick-start)
- [Daemon Usage](#daemon-usage)
- [CLI Usage](#cli-usage)
- [Authentication](#authentication)
- [Configuration Management](#configuration-management)
- [Event Monitoring](#event-monitoring)
- [Troubleshooting](#troubleshooting)
- [Advanced Topics](#advanced-topics)

---

## Overview

NyxNet consists of two main components:

1. **nyx-daemon**: Background service that manages network connections and routing
2. **nyx-cli**: Command-line tool for managing and monitoring the daemon

### Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                      User Applications                       │
└───────────────────────────┬─────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────┐
│                         nyx-cli                              │
│   (Command-line interface for daemon management)            │
└───────────────────────────┬─────────────────────────────────┘
                            │ IPC (JSON-RPC)
                            ▼
┌─────────────────────────────────────────────────────────────┐
│                       nyx-daemon                             │
│  • Configuration management  • Event system                  │
│  • Connection management     • Metrics collection            │
│  • Stream multiplexing       • Authentication                │
└───────────────────────────┬─────────────────────────────────┘
                            │
                            ▼
                     Mix Network
```

### Communication Protocol

- **Windows**: Named Pipe (`\\.\pipe\nyx-daemon`)
- **Unix/Linux**: Unix Domain Socket (`/tmp/nyx.sock`)
- **Protocol**: JSON-RPC over line-delimited JSON

---

## Quick Start

### 1. Start the Daemon

**Windows:**
```powershell
# Start daemon in the background
Start-Process -FilePath ".\target\release\nyx-daemon.exe" -WindowStyle Hidden

# Or run in foreground for debugging
.\target\release\nyx-daemon.exe
```

**Unix/Linux:**
```bash
# Start daemon in the background
./target/release/nyx-daemon &

# Or run in foreground for debugging
./target/release/nyx-daemon
```

### 2. Verify Daemon is Running

```bash
# Check daemon information
nyx-cli info

# Expected output:
# {
#   "data": {
#     "node_id": "7b1b3fa909e07219...",
#     "uptime_sec": 42,
#     "version": "0.1.0"
#   },
#   "ok": true
# }
```

### 3. Basic Operations

```bash
# Get compliance report
nyx-cli compliance

# List configuration versions
nyx-cli list-versions

# Show current CLI configuration
nyx-cli config show
```

---

## Daemon Usage

### Starting the Daemon

#### Basic Start
```bash
# Default settings (uses platform-specific IPC)
nyx-daemon
```

#### With Configuration File
```bash
# Specify configuration file
nyx-daemon --config /path/to/nyx.toml

# Or use environment variable
export NYX_CONFIG=/path/to/nyx.toml
nyx-daemon
```

#### TCP Mode (for remote access)
```bash
# Listen on TCP socket instead of IPC
nyx-daemon --bind 127.0.0.1:9000
```

### Environment Variables

| Variable | Description | Example |
|----------|-------------|---------|
| `RUST_LOG` | Log level | `RUST_LOG=debug` |
| `NYX_CONFIG` | Configuration file path | `/etc/nyx/nyx.toml` |
| `NYX_PROMETHEUS_ADDR` | Metrics endpoint | `0.0.0.0:9100` |
| `NYX_OTLP` | Enable OTLP tracing | `NYX_OTLP=1` |
| `NYX_DAEMON_TOKEN` | Auth token | `<secret>` |
| `NYX_DAEMON_COOKIE` | Cookie file path | `~/.nyx/control.authcookie` |
| `NYX_DAEMON_DISABLE_AUTH` | Disable auth (debug only) | `NYX_DAEMON_DISABLE_AUTH=1` |

### Monitoring

#### Prometheus Metrics
```bash
# Start daemon with Prometheus exporter
NYX_PROMETHEUS_ADDR=0.0.0.0:9100 nyx-daemon

# Access metrics
curl http://localhost:9100/metrics
```

#### OpenTelemetry Tracing
```bash
# Enable OTLP tracing to Jaeger/Tempo
NYX_OTLP=1 \
OTEL_EXPORTER_OTLP_TRACES_ENDPOINT=http://localhost:4318/v1/traces \
NYX_SERVICE_NAME=nyx-node-1 \
nyx-daemon
```

---

## CLI Usage

### Connection Options

```bash
# Connect to default daemon endpoint
nyx-cli info

# Connect to custom endpoint
nyx-cli --endpoint "\\.\pipe\custom-pipe" info

# Connect with custom timeout (milliseconds)
nyx-cli --timeout-ms 5000 info

# Connect with authentication token
nyx-cli --token "your-secret-token" info
```

### Available Commands

#### Information Commands

```bash
# Show daemon information
nyx-cli info

# Get compliance report (human-readable)
nyx-cli compliance

# Get compliance report (JSON format)
nyx-cli compliance --format json --detailed

# Show effective CLI configuration
nyx-cli config show
```

#### Configuration Commands

```bash
# Reload configuration from file
nyx-cli reload-config

# Update configuration with inline values
nyx-cli update-config --set 'log_level="debug"' --set 'max_connections=100'

# Update configuration from JSON file
nyx-cli update-config --file config.json

# List configuration versions
nyx-cli list-versions

# Rollback to a specific version
nyx-cli rollback 5

# Create a configuration snapshot
nyx-cli snapshot --description "Pre-production config"
```

#### Event Monitoring

```bash
# Subscribe to all events (press Ctrl-C to stop)
nyx-cli events

# Subscribe to specific event types
nyx-cli events --types connection,error,system
```

#### Frame Size Management

```bash
# Show current frame size limit
nyx-cli frame-limit

# Set frame size limit (1024-67108864 bytes)
nyx-cli frame-limit --set 16777216
```

#### Configuration File Management

```bash
# Write a template nyx.toml file
nyx-cli config write-template

# Write template to specific path
nyx-cli config write-template --path /path/to/nyx.toml --force

# Validate a configuration file
nyx-cli config validate --path nyx.toml

# Validate with strict checks
nyx-cli config validate --path nyx.toml --strict
```

#### Metrics

```bash
# Fetch Prometheus metrics from a URL
nyx-cli prometheus-get http://localhost:9100/metrics
```

---

## Authentication

### Authentication Methods

NyxNet supports multiple authentication methods, checked in order:

1. **Environment Variable**: `NYX_DAEMON_TOKEN`
2. **Cookie File**: Auto-generated or user-provided
3. **CLI Argument**: `--token` flag

### Cookie-Based Authentication (Tor-style)

The daemon automatically generates a secure cookie file on first start:

**Windows:** `%APPDATA%\nyx\control.authcookie`
**Unix/Linux:** `~/.nyx/control.authcookie`

```bash
# View cookie location
nyx-cli config show

# Output shows:
# {
#   "daemon_endpoint": "\\.\pipe\nyx-daemon",
#   "request_timeout_ms": 10000,
#   "token_present": true
# }
```

### Manual Cookie Generation

```bash
# Generate a new cookie file
nyx-cli gen-cookie

# Generate with custom path
nyx-cli gen-cookie --path /path/to/custom.cookie

# Generate with custom length (bytes, hex-encoded)
nyx-cli gen-cookie --length 64 --force
```

### Using Environment Variable

```bash
# Set token via environment variable
export NYX_DAEMON_TOKEN="your-secret-token"
nyx-cli info

# Or inline
NYX_DAEMON_TOKEN="your-secret-token" nyx-cli info
```

### Security Modes

#### Debug Mode (default in debug builds)
- Authentication can be disabled with `NYX_DAEMON_DISABLE_AUTH=1`
- Useful for development and testing

#### Release Mode (always in release builds)
- Authentication always enforced
- Cannot be disabled

---

## Configuration Management

### Configuration File Format

Create a `nyx.toml` file:

```toml
# Daemon configuration
[daemon]
log_level = "info"
max_connections = 100
max_streams_per_connection = 50

# Network configuration
[network]
listen_address = "0.0.0.0:9000"
multipath_enabled = true
cover_traffic_enabled = true

# Frame codec settings
[codec]
max_frame_len_bytes = 16777216  # 16 MB
```

### Dynamic Configuration Updates

```bash
# Update single value
nyx-cli update-config --set 'log_level="debug"'

# Update multiple values
nyx-cli update-config \
  --set 'log_level="debug"' \
  --set 'max_connections=200'

# Update from JSON file
echo '{"log_level": "debug", "max_connections": 200}' > update.json
nyx-cli update-config --file update.json
```

### Version Control

```bash
# Create snapshot before changes
nyx-cli snapshot --description "Before scaling update"

# Make changes
nyx-cli update-config --set 'max_connections=200'

# List all versions
nyx-cli list-versions

# Rollback if needed
nyx-cli rollback 1
```

### Validation

```bash
# Validate configuration file syntax
nyx-cli config validate --path nyx.toml

# Strict validation (includes connectivity checks)
nyx-cli config validate --path nyx.toml --strict
```

---

## Event Monitoring

### Event Types

- `system`: System-level events (startup, shutdown, config changes)
- `connection`: Connection lifecycle events
- `stream`: Stream creation and termination
- `error`: Error conditions
- `metrics`: Performance metrics updates

### Subscribing to Events

```bash
# Subscribe to all events
nyx-cli events

# Subscribe to specific types
nyx-cli events --types system,error

# Output format (JSON per line):
# {"event_type":"system","detail":"compliance_level:Core"}
# {"event_type":"system","detail":"config_rolled_back:1"}
```

### Processing Events with Scripts

```bash
# Save events to file
nyx-cli events > events.log

# Filter specific events
nyx-cli events | grep "error"

# Parse JSON events
nyx-cli events | jq 'select(.event_type == "error")'
```

---

## Troubleshooting

### Daemon Won't Start

**Issue:** Daemon fails to start or exits immediately

**Solutions:**
```bash
# Check if port/pipe is already in use
# Windows:
netstat -an | findstr "9000"

# Unix/Linux:
lsof /tmp/nyx.sock

# Start with debug logging
RUST_LOG=debug nyx-daemon

# Check for configuration errors
nyx-cli config validate --path nyx.toml
```

### CLI Can't Connect to Daemon

**Issue:** `nyx-cli` reports connection refused or timeout

**Solutions:**
```bash
# Verify daemon is running
# Windows:
Get-Process nyx-daemon

# Unix/Linux:
ps aux | grep nyx-daemon

# Check endpoint configuration
nyx-cli config show

# Try with explicit endpoint
nyx-cli --endpoint "\\.\pipe\nyx-daemon" info

# Increase timeout for slow connections
nyx-cli --timeout-ms 30000 info
```

### Authentication Failures

**Issue:** "unauthorized" error when running commands

**Solutions:**
```bash
# Check if cookie exists
# Windows:
Test-Path "$env:APPDATA\nyx\control.authcookie"

# Unix/Linux:
ls -la ~/.nyx/control.authcookie

# Regenerate cookie
nyx-cli gen-cookie --force

# Restart daemon to read new cookie
```

### Configuration Updates Not Applied

**Issue:** Configuration changes don't take effect

**Solutions:**
```bash
# Verify update was successful
nyx-cli update-config --set 'log_level="debug"'

# Check current configuration
nyx-cli config show

# Try explicit reload
nyx-cli reload-config

# Check validation errors
nyx-cli update-config --set 'invalid_key="value"'
# Returns: "unknown setting: invalid_key"
```

---

## Advanced Topics

### Remote Daemon Access

For testing or multi-node setups, you can access daemon over TCP:

```bash
# Start daemon in TCP mode
nyx-daemon --bind 0.0.0.0:9000

# Connect from remote host
nyx-cli --endpoint "http://daemon-host:9000" info
```

**Security Warning:** Only use TCP mode in trusted networks or with proper firewall rules.

### Integration with Monitoring Systems

#### Prometheus + Grafana

```bash
# Start daemon with Prometheus exporter
NYX_PROMETHEUS_ADDR=0.0.0.0:9100 nyx-daemon

# Prometheus configuration (prometheus.yml)
scrape_configs:
  - job_name: 'nyx'
    static_configs:
      - targets: ['localhost:9100']
```

#### OpenTelemetry + Jaeger

```bash
# Start Jaeger all-in-one
docker run -d --name jaeger \
  -p 4318:4318 \
  jaegertracing/all-in-one:latest

# Start daemon with OTLP tracing
NYX_OTLP=1 \
OTEL_EXPORTER_OTLP_TRACES_ENDPOINT=http://localhost:4318/v1/traces \
nyx-daemon
```

### Automation with Scripts

```bash
#!/bin/bash
# health-check.sh

# Check daemon health
if ! nyx-cli info > /dev/null 2>&1; then
    echo "Daemon not responding, restarting..."
    pkill nyx-daemon
    nyx-daemon &
    sleep 2
fi

# Create daily snapshot
nyx-cli snapshot --description "Daily backup $(date +%Y-%m-%d)"

# Cleanup old versions (keep last 7)
versions=$(nyx-cli list-versions | jq -r '.data | length')
if [ $versions -gt 7 ]; then
    echo "Cleaning up old configuration versions..."
    # Implement cleanup logic
fi
```

### Performance Tuning

```bash
# Increase frame size for high-throughput scenarios
nyx-cli frame-limit --set 67108864  # 64 MB

# Update connection limits
nyx-cli update-config --set 'max_connections=500'

# Enable multipath for reliability
nyx-cli update-config --set 'multipath_enabled=true'
```

---

## See Also

- [nyx-daemon README](../nyx-daemon/README.md)
- [nyx-cli README](../nyx-cli/README.md)
- [API Reference](04_API_REFERENCE.md)
- [Development Setup](05_DEVELOPMENT_SETUP.md)

---

## Support

For issues, questions, or contributions:
- GitHub Issues: https://github.com/SeleniaProject/NyxNet/issues
- Documentation: https://github.com/SeleniaProject/NyxNet/tree/main/docs
