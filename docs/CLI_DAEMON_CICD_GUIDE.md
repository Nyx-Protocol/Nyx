# CLI and Daemon CI/CD Usage Guide

This guide explains how to use the automated CI/CD pipelines for nyx-cli and nyx-daemon.

## Table of Contents

- [Overview](#overview)
- [Automated CI Checks](#automated-ci-checks)
- [Creating Releases](#creating-releases)
- [Docker Images](#docker-images)
- [Manual Workflows](#manual-workflows)
- [Troubleshooting](#troubleshooting)

---

## Overview

The NyxNet project includes specialized CI/CD pipelines for the CLI and Daemon components:

1. **cli-daemon-ci.yml**: Automated testing and validation on every push/PR
2. **cli-daemon-release.yml**: Automated binary releases for multiple platforms
3. **docker.yml**: Docker image builds and publishing to GHCR

---

## Automated CI Checks

### When CI Runs

The CLI/Daemon CI pipeline automatically runs when you:
- Push to `main` or `develop` branches
- Create a pull request to `main` or `develop`
- Modify files in these directories:
  - `nyx-cli/`
  - `nyx-daemon/`
  - `nyx-sdk/`
  - `nyx-stream/`
  - `nyx-core/`

### CI Pipeline Stages

#### 1. Build and Test (45 minutes)
Runs on Linux, Windows, and macOS:
```bash
cargo build --package nyx-daemon --release
cargo build --package nyx-cli --release
cargo test --package nyx-daemon --lib -- --test-threads=1
cargo test --package nyx-cli --bins --tests
cargo test --package nyx-sdk --lib
```

**Artifacts**: Platform-specific binaries (retained for 7 days)

#### 2. Integration Tests (30 minutes)
Real-world testing of daemon + CLI:
- Starts daemon on platform-specific IPC (Named Pipe/Unix Socket)
- Executes all CLI commands
- Validates responses
- Tests configuration management

Example test sequence:
```bash
./nyx-daemon &
./nyx-cli info
./nyx-cli compliance
./nyx-cli config show
./nyx-cli snapshot --description "CI Test"
./nyx-cli update-config --set 'log_level="debug"'
./nyx-cli rollback 1
```

#### 3. Performance Benchmarks (45 minutes)
Runs performance benchmarks and posts results as PR comment:
- Daemon performance metrics
- CLI command latency
- Configuration management overhead

**Artifacts**: Benchmark results (retained for 30 days)

#### 4. Static Analysis (20 minutes)
Code quality checks:
```bash
cargo clippy --package nyx-daemon --all-features -- -D warnings
cargo clippy --package nyx-cli --all-features -- -D warnings
```

#### 5. Security Audit (15 minutes)
Security validation:
- `cargo audit --deny warnings`
- Checks for unsafe code in daemon and CLI
- Dependency vulnerability scanning

#### 6. Code Coverage (30 minutes)
Test coverage measurement:
```bash
cargo tarpaulin --package nyx-daemon --out Xml
cargo tarpaulin --package nyx-cli --out Xml
```

Results uploaded to Codecov with `daemon-cli` flag.

#### 7. Documentation Build (20 minutes)
Validates documentation builds correctly:
```bash
cargo doc --package nyx-daemon --no-deps
cargo doc --package nyx-cli --no-deps
```

**Artifacts**: Documentation HTML (retained for 30 days)

### Viewing CI Results

1. **Pull Request Checks**: All checks appear at the bottom of your PR
2. **Actions Tab**: Visit https://github.com/SeleniaProject/NyxNet/actions
3. **Artifacts**: Download from workflow run summary page

---

## Creating Releases

### Automated Release Process

Releases are automatically created when you push a version tag:

#### CLI Release
```bash
git tag cli-v1.0.0
git push origin cli-v1.0.0
```

#### Daemon Release
```bash
git tag daemon-v1.0.0
git push origin daemon-v1.0.0
```

### Release Workflow

1. **Prepare**: Extracts version and component from tag
2. **Build**: Compiles binaries for all supported platforms:
   - Linux x86_64 (`x86_64-unknown-linux-gnu`)
   - Linux aarch64 (`aarch64-unknown-linux-gnu`)
   - Windows x86_64 (`x86_64-pc-windows-msvc`)
   - macOS x86_64 (`x86_64-apple-darwin`)
   - macOS aarch64 (`aarch64-apple-darwin` - Apple Silicon)

3. **Package**: Creates platform-specific archives:
   - Unix/Linux: `.tar.gz`
   - Windows: `.zip`
   - Includes README, LICENSE files

4. **Checksum**: Generates SHA256 checksums for all archives

5. **Publish**: Creates GitHub Release with:
   - Auto-generated release notes
   - All binary archives
   - Checksum files
   - Installation instructions

### Manual Release Trigger

You can also trigger releases manually:

1. Go to: https://github.com/SeleniaProject/NyxNet/actions/workflows/cli-daemon-release.yml
2. Click "Run workflow"
3. Select:
   - **Component**: `cli`, `daemon`, or `both`
   - **Version**: e.g., `1.0.0`
   - **Pre-release**: Check if this is a pre-release

### Release Artifacts

Each release includes:
```
nyx-cli-1.0.0-x86_64-unknown-linux-gnu.tar.gz
nyx-cli-1.0.0-x86_64-unknown-linux-gnu.tar.gz.sha256
nyx-cli-1.0.0-aarch64-unknown-linux-gnu.tar.gz
nyx-cli-1.0.0-aarch64-unknown-linux-gnu.tar.gz.sha256
nyx-cli-1.0.0-x86_64-pc-windows-msvc.zip
nyx-cli-1.0.0-x86_64-pc-windows-msvc.zip.sha256
nyx-cli-1.0.0-x86_64-apple-darwin.tar.gz
nyx-cli-1.0.0-x86_64-apple-darwin.tar.gz.sha256
nyx-cli-1.0.0-aarch64-apple-darwin.tar.gz
nyx-cli-1.0.0-aarch64-apple-darwin.tar.gz.sha256
```

### Verifying Downloads

Users can verify downloaded binaries:
```bash
sha256sum -c nyx-cli-1.0.0-x86_64-unknown-linux-gnu.tar.gz.sha256
```

### Version Naming

Follow semantic versioning:
- **Major.Minor.Patch**: `1.0.0`
- **Pre-release**: `1.0.0-alpha.1`, `1.0.0-beta.2`, `1.0.0-rc.1`

Pre-releases are automatically detected and marked accordingly.

---

## Docker Images

### Automated Docker Builds

Docker images are automatically built and published to GitHub Container Registry (GHCR) when:
- You push to `main` branch
- A release is published
- Docker-related files are modified

### Image Tags

Images are published with multiple tags:
```
ghcr.io/seleniaproject/nyxnet/nyx-daemon:latest          # Latest from main branch
ghcr.io/seleniaproject/nyxnet/nyx-daemon:main            # Main branch
ghcr.io/seleniaproject/nyxnet/nyx-daemon:1.0.0           # Specific version
ghcr.io/seleniaproject/nyxnet/nyx-daemon:1.0             # Major.minor
ghcr.io/seleniaproject/nyxnet/nyx-daemon:1               # Major
ghcr.io/seleniaproject/nyxnet/nyx-daemon:sha-abc1234     # Git SHA
```

### Multi-Architecture Support

Images are built for:
- `linux/amd64` (x86_64)
- `linux/arm64` (aarch64)

Docker will automatically pull the correct architecture for your platform.

### Using Docker Images

#### Pull Latest Image
```bash
docker pull ghcr.io/seleniaproject/nyxnet/nyx-daemon:latest
```

#### Run Daemon Container
```bash
docker run -d --name nyx-daemon \
  -e RUST_LOG=info \
  -e NYX_PROMETHEUS_ADDR=0.0.0.0:9100 \
  -p 9100:9100 \
  ghcr.io/seleniaproject/nyxnet/nyx-daemon:latest
```

#### With Configuration File
```bash
docker run -d --name nyx-daemon \
  -v $(pwd)/nyx.toml:/etc/nyx/nyx.toml \
  -e NYX_CONFIG=/etc/nyx/nyx.toml \
  ghcr.io/seleniaproject/nyxnet/nyx-daemon:latest
```

#### Docker Compose
```yaml
version: '3.8'
services:
  nyx-daemon:
    image: ghcr.io/seleniaproject/nyxnet/nyx-daemon:latest
    environment:
      - RUST_LOG=info
      - NYX_PROMETHEUS_ADDR=0.0.0.0:9100
    ports:
      - "9100:9100"
    volumes:
      - ./nyx.toml:/etc/nyx/nyx.toml
    restart: unless-stopped
```

### Security Scanning

All Docker images are automatically scanned for vulnerabilities using Trivy:
- Results uploaded to GitHub Security tab
- SARIF format for integration with code scanning
- Fails build on critical vulnerabilities

---

## Manual Workflows

### Manually Trigger CI

You can manually trigger any workflow:

1. Go to Actions tab: https://github.com/SeleniaProject/NyxNet/actions
2. Select workflow from left sidebar
3. Click "Run workflow" button
4. Configure options if available

### Skip Benchmarks

To skip performance benchmarks (saves ~45 minutes):

1. Trigger "CLI and Daemon CI/CD" workflow manually
2. Check "Skip performance benchmarks"

This is useful for quick validation of fixes.

---

## Troubleshooting

### CI Failures

#### Build Failures
**Symptom**: Compilation errors in build-and-test job

**Solutions**:
```bash
# Test locally first
cargo build --package nyx-daemon --release
cargo build --package nyx-cli --release

# Check all features compile
cargo check --package nyx-daemon --all-features
cargo check --package nyx-cli --all-features
```

#### Test Failures
**Symptom**: Unit or integration tests fail

**Solutions**:
```bash
# Run tests locally
cargo test --package nyx-daemon --lib -- --test-threads=1
cargo test --package nyx-cli

# Run specific test
cargo test --package nyx-daemon --lib specific_test_name
```

#### Integration Test Failures
**Symptom**: Daemon doesn't start or CLI can't connect

**Common causes**:
- Port/socket already in use
- Insufficient permissions
- Timeout too short

**Solutions**:
```bash
# Check if daemon is already running
ps aux | grep nyx-daemon  # Unix
Get-Process nyx-daemon    # Windows

# Test daemon startup locally
./target/release/nyx-daemon &
sleep 3
./target/release/nyx-cli info

# Check logs
RUST_LOG=debug ./target/release/nyx-daemon
```

#### Clippy Failures
**Symptom**: Clippy warnings treated as errors

**Solutions**:
```bash
# Run Clippy locally
cargo clippy --package nyx-daemon --all-features -- -D warnings
cargo clippy --package nyx-cli --all-features -- -D warnings

# Fix automatically when possible
cargo clippy --fix --package nyx-daemon
```

#### Security Audit Failures
**Symptom**: Vulnerable dependencies detected

**Solutions**:
```bash
# Run audit locally
cargo audit

# Update dependencies
cargo update

# Check specific advisory
cargo audit --db ~/.cargo/advisory-db RUSTSEC-YYYY-NNNN
```

### Release Issues

#### Tag Push Failed
**Symptom**: Release not triggered after pushing tag

**Solutions**:
```bash
# Verify tag exists
git tag -l "cli-v*" "daemon-v*"

# Verify tag pushed to remote
git ls-remote --tags origin

# Re-push tag
git push origin cli-v1.0.0 --force
```

#### Build Artifacts Missing
**Symptom**: Some platform binaries missing from release

**Check**:
1. Go to Actions tab
2. Find the release workflow run
3. Check if any matrix job failed
4. Review logs for specific platform

**Common Issues**:
- Cross-compilation tools not installed
- Target not available on runner
- Build timeout

#### Invalid Version Format
**Symptom**: Release fails with "Invalid version format" error

**Solution**:
Use valid semantic version:
- ✅ Good: `1.0.0`, `1.0.0-alpha.1`, `2.3.1-rc.2`
- ❌ Bad: `v1.0`, `1.0`, `release-1.0.0`

### Docker Issues

#### Image Pull Failures
**Symptom**: Cannot pull image from GHCR

**Solutions**:
```bash
# Authenticate with GHCR
echo $GITHUB_TOKEN | docker login ghcr.io -u USERNAME --password-stdin

# Pull specific tag
docker pull ghcr.io/seleniaproject/nyxnet/nyx-daemon:main

# Check if image exists
docker search ghcr.io/seleniaproject/nyxnet/nyx-daemon
```

#### Container Startup Failures
**Symptom**: Container exits immediately after start

**Solutions**:
```bash
# Check container logs
docker logs nyx-daemon

# Run interactively for debugging
docker run -it --entrypoint /bin/sh ghcr.io/seleniaproject/nyxnet/nyx-daemon:latest

# Check process status
docker exec nyx-daemon ps aux
```

### Performance Regression

#### Benchmarks Slower Than Expected
**Symptom**: Benchmark results show significant slowdown

**Investigation**:
```bash
# Run benchmarks locally
cargo bench --package nyx-daemon --bench '*'
cargo bench --package nyx-cli --bench '*'

# Compare with baseline
# Download previous benchmark artifacts from Actions

# Profile with flamegraph
cargo flamegraph --bench daemon_benchmark
```

---

## Best Practices

### Development Workflow

1. **Create Feature Branch**
   ```bash
   git checkout -b feature/improve-daemon
   ```

2. **Make Changes and Test Locally**
   ```bash
   cargo build --package nyx-daemon
   cargo test --package nyx-daemon
   cargo clippy --package nyx-daemon -- -D warnings
   ```

3. **Create Pull Request**
   - CI runs automatically
   - Fix any failures before requesting review

4. **After Merge to Main**
   - Docker images built automatically
   - Benchmarks run and archived

5. **Create Release**
   ```bash
   git tag daemon-v1.0.0
   git push origin daemon-v1.0.0
   ```

### Versioning Strategy

- **Patch** (1.0.X): Bug fixes, minor improvements
- **Minor** (1.X.0): New features, backward compatible
- **Major** (X.0.0): Breaking changes

### Pre-releases

Use pre-release versions for:
- **Alpha**: Early testing, unstable features
- **Beta**: Feature complete, testing for bugs
- **RC**: Release candidate, final testing

Example: `1.0.0-alpha.1` → `1.0.0-beta.1` → `1.0.0-rc.1` → `1.0.0`

---

## Monitoring CI/CD Health

### GitHub Actions Dashboard

View all workflow runs:
- https://github.com/SeleniaProject/NyxNet/actions

### Success Rate

Track CI success rate over time:
- https://github.com/SeleniaProject/NyxNet/actions/workflows/cli-daemon-ci.yml

### Artifacts

Download build artifacts:
- Navigate to specific workflow run
- Scroll to "Artifacts" section
- Download binaries, benchmarks, documentation

### Notifications

Enable notifications for workflow failures:
1. Repository Settings → Notifications
2. Enable "Actions" notifications

---

## Support

For CI/CD issues:
- Check workflow logs in Actions tab
- Review this troubleshooting guide
- Open issue: https://github.com/SeleniaProject/NyxNet/issues
- Tag with `ci-cd` label
