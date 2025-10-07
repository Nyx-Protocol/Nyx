# NyxNet Development Setup Guide

**Last Updated**: October 7, 2025  
**Target Version**: v1.0

[日本語版](./05_DEVELOPMENT_SETUP.md)

---

## Overview

This guide covers complete development environment setup for NyxNet across all supported platforms. NyxNet requires **Rust 1.70+** and **Go 1.21+** with zero C/C++ dependencies (pure Rust + pure Go stack).

**Prerequisites Summary**:
- Rust: stable channel (defined in `rust-toolchain.toml`)
- Go: 1.24.0+ (for HTTP proxy only)
- Protocol Buffers compiler: protoc 3.x
- Optional: Docker, Kubernetes (for container/orchestration development)

---

## Platform-Specific Setup

### Windows (Native + WSL)

#### Option 1: Windows Native Development

**1. Install Rust**

```powershell
# Download and run rustup-init.exe from https://rustup.rs/
# Or use winget (Windows 11+)
winget install Rustlang.Rustup

# Verify installation
rustc --version
cargo --version
```

**2. Install Go**

```powershell
# Download from https://go.dev/dl/
# Or use winget
winget install GoLang.Go

# Verify installation
go version
```

**3. Install Protocol Buffers Compiler**

```powershell
# Using Chocolatey
choco install protoc

# Verify installation
protoc --version
```

**4. Install Build Tools (if not already present)**

```powershell
# Visual Studio Build Tools (required for some Rust crates)
# Download from: https://visualstudio.microsoft.com/downloads/
# Select "Desktop development with C++" workload
```

**5. Clone Repository**

```powershell
git clone https://github.com/SeleniaProject/NyxNet.git
cd NyxNet
```

**6. Build Project**

```powershell
# Build all workspace crates
cargo build --workspace

# Build with release optimizations (recommended for testing)
cargo build --workspace --release

# Build specific crate (e.g., nyx-daemon)
cargo build -p nyx-daemon --release
```

**7. Run Tests**

```powershell
# Run all tests
cargo test --workspace

# Run tests with release profile (faster execution)
cargo test --workspace --release

# Run specific test package
cargo test -p nyx-crypto --features hybrid

# Run compliance tests
cargo test -p nyx-conformance --features hybrid,multipath,telemetry
```

---

#### Option 2: WSL (Windows Subsystem for Linux)

**Recommended for development** due to better Unix tool support.

**1. Install WSL 2**

```powershell
# Enable WSL (requires administrator privileges)
wsl --install

# Set WSL 2 as default
wsl --set-default-version 2

# Install Ubuntu (or preferred distro)
wsl --install -d Ubuntu-24.04
```

**2. Enter WSL Environment**

```powershell
wsl
```

From this point, follow the **Linux** instructions below inside WSL.

---

### Linux (Ubuntu/Debian)

**1. Install System Dependencies**

```bash
set -euo pipefail

# Update package lists
sudo apt update

# Install build essentials
sudo apt install -y build-essential pkg-config libssl-dev

# Install protobuf compiler
sudo apt install -y protobuf-compiler

# Verify protoc installation
protoc --version
```

**2. Install Rust**

```bash
# Install rustup (Rust toolchain manager)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

# Add Rust to PATH (for current session)
source "$HOME/.cargo/env"

# Verify installation
rustc --version
cargo --version
```

**3. Install Go**

```bash
# Download Go 1.24.0 (or latest)
wget https://go.dev/dl/go1.24.0.linux-amd64.tar.gz

# Extract to /usr/local
sudo rm -rf /usr/local/go
sudo tar -C /usr/local -xzf go1.24.0.linux-amd64.tar.gz

# Add Go to PATH
echo 'export PATH=$PATH:/usr/local/go/bin' >> ~/.bashrc
source ~/.bashrc

# Verify installation
go version
```

**4. Clone Repository**

```bash
git clone https://github.com/SeleniaProject/NyxNet.git
cd NyxNet
```

**5. Build Project**

```bash
# Build all workspace crates
cargo build --workspace

# Build with release optimizations
cargo build --workspace --release

# Build HTTP proxy (Go)
cd nyx-http-proxy
go build -o nyx-http-proxy main.go
cd ..
```

**6. Run Tests**

```bash
# Run all Rust tests
cargo test --workspace

# Run with release profile (recommended)
cargo test --workspace --release

# Run compliance gate (mandatory CI check)
make compliance-check

# Run full compliance test suite
make compliance-full

# Run hybrid handshake tests
make hybrid-tests
```

---

### macOS

**1. Install Homebrew** (if not already installed)

```bash
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
```

**2. Install System Dependencies**

```bash
set -euo pipefail

# Install protobuf compiler
brew install protobuf

# Verify installation
protoc --version
```

**3. Install Rust**

```bash
# Install rustup
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

# Add Rust to PATH
source "$HOME/.cargo/env"

# Verify installation
rustc --version
cargo --version
```

**4. Install Go**

```bash
# Install via Homebrew
brew install go

# Verify installation
go version
```

**5. Clone Repository**

```bash
git clone https://github.com/SeleniaProject/NyxNet.git
cd NyxNet
```

**6. Build and Test**

```bash
# Build all crates
cargo build --workspace --release

# Run tests
cargo test --workspace --release

# Run compliance checks
make compliance-check
```

---

## IDE Setup

### Visual Studio Code (Recommended)

**1. Install VS Code**

- Download from https://code.visualstudio.com/

**2. Install Extensions**

```json
{
  "recommendations": [
    "rust-lang.rust-analyzer",
    "tamasfe.even-better-toml",
    "serayuzgur.crates",
    "vadimcn.vscode-lldb",
    "golang.go"
  ]
}
```

**3. Configure Settings** (`.vscode/settings.json`)

```json
{
  "rust-analyzer.checkOnSave.command": "clippy",
  "rust-analyzer.checkOnSave.allFeatures": true,
  "rust-analyzer.cargo.features": ["hybrid", "multipath", "telemetry"],
  "[rust]": {
    "editor.formatOnSave": true,
    "editor.defaultFormatter": "rust-lang.rust-analyzer"
  },
  "go.formatTool": "gofmt",
  "go.lintTool": "golangci-lint"
}
```

**4. Configure Tasks** (`.vscode/tasks.json`)

```json
{
  "version": "2.0.0",
  "tasks": [
    {
      "label": "cargo build",
      "type": "shell",
      "command": "cargo",
      "args": ["build", "--workspace"],
      "group": {
        "kind": "build",
        "isDefault": true
      }
    },
    {
      "label": "cargo test",
      "type": "shell",
      "command": "cargo",
      "args": ["test", "--workspace"],
      "group": "test"
    },
    {
      "label": "compliance check",
      "type": "shell",
      "command": "make",
      "args": ["compliance-check"]
    }
  ]
}
```

**5. Configure Launch** (`.vscode/launch.json`)

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug nyx-daemon",
      "cargo": {
        "args": ["build", "-p", "nyx-daemon"],
        "filter": {
          "name": "nyx-daemon",
          "kind": "bin"
        }
      },
      "args": [],
      "cwd": "${workspaceFolder}"
    }
  ]
}
```

---

### CLion / IntelliJ IDEA

**1. Install Rust Plugin**

- Settings → Plugins → Search "Rust" → Install

**2. Configure Toolchain**

- Settings → Languages & Frameworks → Rust
- Set Toolchain location: `~/.cargo/bin/cargo`
- Enable external linter: Clippy

**3. Configure Run Configurations**

- Run → Edit Configurations
- Add "Cargo Command": `build --workspace`
- Add "Cargo Command": `test --workspace`

---

## Building from Source

### Full Build Process

```bash
# WSL / Linux / macOS
set -euo pipefail

# 1. Clean previous build artifacts
cargo clean

# 2. Build all workspace crates with release profile
cargo build --workspace --release

# 3. Build HTTP proxy (Go)
cd nyx-http-proxy
go build -o nyx-http-proxy main.go
cd ..

# 4. Run compliance gate (mandatory)
make compliance-check

# 5. Run full test suite
cargo test --workspace --release

# Build outputs are in:
# - ./target/release/nyx-daemon
# - ./target/release/nyx-cli
# - ./nyx-http-proxy/nyx-http-proxy
```

**Windows PowerShell**:

```powershell
# 1. Clean previous build artifacts
cargo clean

# 2. Build all workspace crates
cargo build --workspace --release

# 3. Build HTTP proxy
cd nyx-http-proxy
go build -o nyx-http-proxy.exe main.go
cd ..

# 4. Run tests
cargo test --workspace --release

# Build outputs:
# - .\target\release\nyx-daemon.exe
# - .\target\release\nyx-cli.exe
# - .\nyx-http-proxy\nyx-http-proxy.exe
```

---

### Feature Flags

NyxNet uses Cargo feature flags to control optional functionality:

| Feature | Description | Default |
|---------|-------------|---------|
| `hybrid` | Hybrid post-quantum handshake (ML-KEM-768 + X25519) | ✅ |
| `multipath` | Multipath QUIC transport | ❌ |
| `telemetry` | Prometheus metrics + OpenTelemetry tracing | ❌ |
| `plugin` | Plugin framework (CBOR-based protocol extension) | ❌ |
| `quic` | QUIC transport layer | ❌ |
| `low_power` | Low power mode for mobile devices | ❌ |

**Build with specific features**:

```bash
# Linux / macOS / WSL
cargo build --features hybrid,multipath,telemetry

# Windows PowerShell
cargo build --features hybrid,multipath,telemetry
```

**Build all features**:

```bash
# Linux / macOS / WSL
cargo build --all-features

# Windows PowerShell
cargo build --all-features
```

---

## Running the Daemon

### Development Mode (Debug Build)

**Linux / macOS / WSL**:

```bash
# Build and run daemon
cargo run -p nyx-daemon

# Run with custom config
cargo run -p nyx-daemon -- --config ./examples/full_config.toml

# Run with verbose logging
RUST_LOG=debug cargo run -p nyx-daemon
```

**Windows PowerShell**:

```powershell
# Build and run daemon
cargo run -p nyx-daemon

# Run with custom config
cargo run -p nyx-daemon -- --config .\examples\full_config.toml

# Run with verbose logging
$env:RUST_LOG="debug"
cargo run -p nyx-daemon
```

---

### Production Mode (Release Build)

**Linux / macOS / WSL**:

```bash
# Build release binary
cargo build -p nyx-daemon --release

# Run daemon
./target/release/nyx-daemon --config nyx.toml

# Run as background service (systemd)
sudo cp ./target/release/nyx-daemon /usr/local/bin/
sudo systemctl start nyx-daemon
```

**Windows PowerShell**:

```powershell
# Build release binary
cargo build -p nyx-daemon --release

# Run daemon
.\target\release\nyx-daemon.exe --config nyx.toml

# Run as Windows Service (requires NSSM or similar)
nssm install NyxDaemon "C:\path\to\nyx-daemon.exe" "--config C:\path\to\nyx.toml"
nssm start NyxDaemon
```

---

## Testing

### Unit Tests

**Run all unit tests**:

```bash
# Linux / macOS / WSL
cargo test --workspace --lib

# Windows PowerShell
cargo test --workspace --lib
```

**Run specific test**:

```bash
# Linux / macOS / WSL
cargo test -p nyx-crypto hybrid_handshake_roundtrip

# Windows PowerShell
cargo test -p nyx-crypto hybrid_handshake_roundtrip
```

---

### Integration Tests

**Run all integration tests**:

```bash
# Linux / macOS / WSL
cargo test --workspace --test '*'

# Windows PowerShell
cargo test --workspace --test '*'
```

**Run specific integration test**:

```bash
# Linux / macOS / WSL
cargo test -p tests stream_establishment_flow

# Windows PowerShell
cargo test -p tests stream_establishment_flow
```

---

### Compliance Tests

NyxNet includes compliance tests to ensure protocol correctness. These are **mandatory** for CI/CD pipelines.

**Run compliance gate** (Core level):

```bash
# Linux / macOS / WSL
make compliance-check

# Or directly:
cargo test -p nyx-conformance ci_compliance_gate_main --features hybrid -- --nocapture
```

**Windows PowerShell**:

```powershell
# Compliance tests use Makefile (requires Make for Windows or WSL)
# Alternative: Run directly
cargo test -p nyx-conformance ci_compliance_gate_main --features hybrid -- --nocapture
```

**Generate compliance reports**:

```bash
# Linux / macOS / WSL
make compliance-report

# Output: ./compliance-reports/
```

---

### Property-Based Tests

**Run proptest tests**:

```bash
# Linux / macOS / WSL
cargo test -p nyx-crypto --features hybrid -- --nocapture

# With specific seed for reproducibility
PROPTEST_RNG_SEED=42 cargo test -p nyx-crypto
```

**Windows PowerShell**:

```powershell
cargo test -p nyx-crypto --features hybrid -- --nocapture

# With seed
$env:PROPTEST_RNG_SEED="42"
cargo test -p nyx-crypto
```

---

### Benchmarks

**Run criterion benchmarks**:

```bash
# Linux / macOS / WSL
cargo bench -p nyx-crypto

# Generate HTML reports (output: target/criterion/)
cargo bench --features html_reports

# Run specific benchmark
cargo bench -p nyx-crypto hybrid_handshake_benchmark
```

**Windows PowerShell**:

```powershell
cargo bench -p nyx-crypto

# Benchmark results: .\target\criterion\
```

---

## Linting and Formatting

### Format Code

**Check formatting** (CI mode):

```bash
# Linux / macOS / WSL
cargo fmt --all -- --check

# Windows PowerShell
cargo fmt --all -- --check
```

**Auto-format code**:

```bash
# Linux / macOS / WSL
cargo fmt --all

# Windows PowerShell
cargo fmt --all
```

---

### Run Clippy (Linter)

**Check all lints**:

```bash
# Linux / macOS / WSL
cargo clippy --workspace --all-targets --all-features -- -D warnings

# Windows PowerShell
cargo clippy --workspace --all-targets --all-features -- -D warnings
```

**Fix auto-fixable lints**:

```bash
# Linux / macOS / WSL
cargo clippy --fix --allow-dirty --allow-staged

# Windows PowerShell
cargo clippy --fix --allow-dirty --allow-staged
```

---

## Docker Development

### Build Docker Image

**Linux / macOS / WSL**:

```bash
# Build production image
docker build -t nyxnet:latest -f Dockerfile .

# Build benchmark image
docker build -t nyxnet-bench:latest -f Dockerfile.benchmark .

# Run daemon in container
docker run -d \
  --name nyx-daemon \
  -p 50051:50051 \
  -p 1080:1080 \
  -v $(pwd)/nyx.toml:/etc/nyx/nyx.toml:ro \
  nyxnet:latest
```

**Windows PowerShell**:

```powershell
# Build production image
docker build -t nyxnet:latest -f Dockerfile .

# Run daemon in container
docker run -d `
  --name nyx-daemon `
  -p 50051:50051 `
  -p 1080:1080 `
  -v ${PWD}\nyx.toml:/etc/nyx/nyx.toml:ro `
  nyxnet:latest
```

---

### Docker Compose

**Start multi-node network** (3 nodes):

```bash
# Linux / macOS / WSL
docker-compose up -d

# View logs
docker-compose logs -f

# Stop network
docker-compose down
```

**Windows PowerShell**:

```powershell
docker-compose up -d
docker-compose logs -f
docker-compose down
```

---

## Kubernetes Development

### Deploy to Local Cluster

**Using kind (Kubernetes in Docker)**:

```bash
# Linux / macOS / WSL
set -euo pipefail

# Create kind cluster
kind create cluster --config kind-config.yaml

# Build and load image into kind
docker build -t nyxnet:latest .
kind load docker-image nyxnet:latest

# Deploy using Helm
helm install nyx ./charts/nyx

# Check deployment status
kubectl get pods -l app=nyx

# Port-forward to access gRPC API
kubectl port-forward svc/nyx-control 50051:50051
```

---

## Troubleshooting

### Common Issues

#### 1. Protobuf Compiler Not Found

**Error**:
```
error: failed to run custom build command for `build-protoc`
protoc not found in PATH
```

**Solution**:

```bash
# Linux / macOS / WSL
sudo apt install protobuf-compiler  # Ubuntu/Debian
brew install protobuf               # macOS
```

```powershell
# Windows
choco install protoc
```

---

#### 2. Rust Toolchain Version Mismatch

**Error**:
```
error: package requires `rustc 1.70` or newer
```

**Solution**:

```bash
# Linux / macOS / WSL / Windows
rustup update stable
rustc --version
```

---

#### 3. OpenSSL Not Found (Linux)

**Error**:
```
error: failed to run custom build command for `openssl-sys`
```

**Solution**:

```bash
# Ubuntu/Debian
sudo apt install libssl-dev pkg-config

# Fedora/CentOS
sudo dnf install openssl-devel
```

---

#### 4. Go Module Download Failures

**Error**:
```
go: downloading golang.org/x/net failed: connection timeout
```

**Solution**:

```bash
# Set Go proxy (China users)
go env -w GOPROXY=https://goproxy.cn,direct

# Or use Google proxy
go env -w GOPROXY=https://proxy.golang.org,direct
```

```powershell
# Windows
go env -w GOPROXY=https://goproxy.cn,direct
```

---

#### 5. Cargo Build Hangs

**Solution**:

```bash
# Linux / macOS / WSL
# Increase verbosity to see what's happening
cargo build -vv

# Check if network is blocking crates.io
curl -I https://crates.io

# Use mirror (China users)
echo '[source.crates-io]
replace-with = "ustc"

[source.ustc]
registry = "git://mirrors.ustc.edu.cn/crates.io-index"' > ~/.cargo/config.toml
```

```powershell
# Windows
# Add to %USERPROFILE%\.cargo\config.toml
```

---

#### 6. Test Failures Due to Port Conflicts

**Error**:
```
thread 'test_daemon_startup' panicked at 'Address already in use'
```

**Solution**:

```bash
# Linux / macOS / WSL
# Find process using port 50051
sudo lsof -i :50051
sudo kill -9 <PID>

# Or use different port in test config
```

```powershell
# Windows
# Find process using port
netstat -ano | findstr :50051
taskkill /PID <PID> /F
```

---

#### 7. Permission Denied (Unix Socket)

**Error**:
```
Error: Permission denied (os error 13) when accessing /tmp/nyx.sock
```

**Solution**:

```bash
# Linux / macOS / WSL
sudo chmod 666 /tmp/nyx.sock

# Or run daemon with current user permissions
cargo run -p nyx-daemon
```

---

#### 8. Windows Defender Blocking Execution

**Solution**:

```powershell
# Add exclusion for project directory
Add-MpPreference -ExclusionPath "C:\path\to\NyxNet"

# Or temporarily disable real-time protection (not recommended)
```

---

## Performance Tuning

### Development Builds

**Speed up incremental builds**:

```bash
# Enable parallel compilation (default in Rust 1.70+)
export CARGO_BUILD_JOBS=8

# Use mold linker (Linux, much faster than ld)
sudo apt install mold
export RUSTFLAGS="-C link-arg=-fuse-ld=mold"
```

Add to `.cargo/config.toml`:

```toml
[build]
jobs = 8

[target.x86_64-unknown-linux-gnu]
linker = "clang"
rustflags = ["-C", "link-arg=-fuse-ld=mold"]
```

---

### Release Builds

**Optimize for size**:

```toml
# Cargo.toml
[profile.release]
opt-level = "z"     # Optimize for size
lto = true
codegen-units = 1
strip = true
```

**Optimize for performance**:

```toml
# Cargo.toml (already configured in workspace)
[profile.release]
opt-level = 3       # Maximum optimization
lto = "fat"
codegen-units = 1
panic = "abort"
```

---

## Contributing Workflow

**1. Fork and clone**

```bash
git clone https://github.com/YOUR_USERNAME/NyxNet.git
cd NyxNet
git remote add upstream https://github.com/SeleniaProject/NyxNet.git
```

**2. Create feature branch**

```bash
git checkout -b feature/my-feature
```

**3. Make changes and test**

```bash
# Format code
cargo fmt --all

# Run linter
cargo clippy --workspace --all-features -- -D warnings

# Run tests
cargo test --workspace

# Run compliance gate
make compliance-check
```

**4. Commit and push**

```bash
git add .
git commit -m "feat: add new feature"
git push origin feature/my-feature
```

**5. Open Pull Request**

- Go to GitHub and create PR
- Ensure CI passes (all 18 workflows must be green)

---

## Continuous Integration

### GitHub Actions Workflows

NyxNet uses 18 CI/CD workflows:

1. **main.yml**: Lint, format, test, build (all platforms)
2. **security.yml**: Security audits, CVE scanning
3. **compliance.yml**: Protocol compliance verification
4. **benchmarks.yml**: Performance regression testing
5. **docker.yml**: Container image builds
6. Others: Fuzzing, formal verification, dependency updates

**Check CI status**:

```bash
# View workflow runs
gh run list --workflow=main.yml

# View logs for specific run
gh run view <run-id>
```

---

## Disclaimer: Inferred Content

The following information is reasonably inferred from typical development workflows:

- **Port numbers**: Default ports (50051, 1080, 8080) are standard but configurable
- **Performance tuning**: Compiler flags are based on common Rust optimization practices
- **Troubleshooting**: Common errors derived from typical Rust/Go development issues

For precise build requirements, always refer to `Cargo.toml`, `go.mod`, and `.github/workflows/` configurations.
