# NyxNet Documentation Index

**Last Updated**: October 7, 2025  
**Version**: v1.0  
**Status**: ✅ Complete (Full codebase compliance)

[日本語版はこちら / Japanese Version](./00_INDEX.md)

---

## Documentation Overview

This documentation set provides comprehensive technical documentation for the NyxNet project. It analyzes the codebase exhaustively and provides technically accurate, reproducible information.

**Compliant with World-Class Documentation Generation Prompt v2**:
- Full consistency with codebase
- WSL/PowerShell command notation standards
- Confidential information protection
- Clear indication of inferred content
- Idempotent and reproducible

---

## Essential Documents (Recommended Reading Order)

### Core Documentation

1. **[Project Overview](./01_PROJECT_OVERVIEW_EN.md)** ([日本語](./01_PROJECT_OVERVIEW.md))
   - Project objectives and problems solved
   - Feature matrix
   - Technology stack overview
   - Directory structure

2. **[System Architecture](./02_SYSTEM_ARCHITECTURE_EN.md)** ([日本語](./02_SYSTEM_ARCHITECTURE.md))
   - Architecture diagrams (text representation)
   - Major components and responsibilities
   - Data flow and interactions
   - Design patterns and rationale
   - External integration points

3. **[Major Features](./03_MAJOR_FEATURES_EN.md)** ([日本語](./03_MAJOR_FEATURES.md))
   - Feature 1: Hybrid Post-Quantum Handshake
   - Feature 2: Sphinx Onion Routing
   - Feature 3: Multipath QUIC Transport
   - Purpose, implementation details, and tests for each feature

4. **[API Reference](./04_API_REFERENCE_EN.md)** ([日本語](./04_API_REFERENCE.md))
   - gRPC API specification
   - JSON-RPC 2.0 API specification
   - SOCKS5/HTTP CONNECT Proxy specification
   - Error formats and rate limiting

5. **[Development Setup Guide](./05_DEVELOPMENT_SETUP_EN.md)** ([日本語](./05_DEVELOPMENT_SETUP.md))
   - Prerequisites and tools
   - OS-specific setup (Windows/WSL/Linux/macOS)
   - Test execution
   - Troubleshooting

### Extended Documentation

6. **[Test Strategy](./06_TEST_STRATEGY_EN.md)** ([日本語](./06_TEST_STRATEGY.md)) ★NEW
   - Test pyramid (unit, integration, E2E)
   - Property-based testing
   - Benchmarking and fuzzing
   - Formal verification (TLA+)
   - CI/CD integration
   - Coverage measurement

7. **[Security Guide](./07_SECURITY_GUIDE_EN.md)** ([日本語](./07_SECURITY_GUIDE.md)) ★NEW
   - Security principles
   - Threat model
   - Cryptographic architecture
   - Key management
   - Vulnerability management
   - Best practices

8. **[Glossary](./08_GLOSSARY_EN.md)** ([日本語](./08_GLOSSARY.md)) ★NEW
   - Technical term definitions
   - Acronym list
   - Security level definitions
   - Compliance level definitions

---

## Additional Documentation (Existing)

### Implementation & Design

- **[CLI/Daemon CI/CD Guide](./CLI_DAEMON_CICD_GUIDE.md)**: CLI and daemon CI/CD integration
- **[CLI/Daemon User Guide](./CLI_DAEMON_GUIDE.md)**: Usage guide for CLI and daemon
- **[CI/CD Integration](./CI_CD_INTEGRATION.md)**: Detailed CI/CD workflow documentation

### Comparison & Benchmarks

- **[Tor Comparison Guide](./TOR_COMPARISON_GUIDE.md)**: Comparison with Tor network
- **[Actual Tor Comparison](./ACTUAL_TOR_COMPARISON.md)**: Real-world benchmark comparisons

### Quick Start

- **[Quick Start (Multi-VM)](./QUICK_START_MULTI_VM.md)**: Multi-VM environment setup guide

### Testing

- **[Testing Documentation](./testing/)**: Detailed test specifications and results

---

## Quick Navigation by Role

### For Application Developers

1. [Development Setup Guide](./05_DEVELOPMENT_SETUP_EN.md) - Environment setup
2. [API Reference](./04_API_REFERENCE_EN.md) - API usage
3. SDK Documentation:
   - Rust: `nyx-sdk/GUIDE.md`
   - WASM: `nyx-sdk-wasm/README.md`
   - Mobile: `nyx-mobile-ffi/README.md`

### For System Administrators

1. [Development Setup Guide](./05_DEVELOPMENT_SETUP_EN.md) - Deployment
2. [Security Guide](./07_SECURITY_GUIDE_EN.md) - Security configuration
3. Kubernetes: `charts/nyx/README.md`

### For Contributors

1. [Project Overview](./01_PROJECT_OVERVIEW_EN.md) - Architecture understanding
2. [System Architecture](./02_SYSTEM_ARCHITECTURE_EN.md) - Component details
3. [Test Strategy](./06_TEST_STRATEGY_EN.md) - Testing guidelines
4. `CONTRIBUTING.md` - Contribution guidelines

### For Security Researchers

1. [Security Guide](./07_SECURITY_GUIDE_EN.md) - Security architecture
2. [Major Features](./03_MAJOR_FEATURES_EN.md) - Cryptographic implementation
3. `SECURITY.md` - Vulnerability reporting
4. Formal verification: `formal/` directory

---

## Documentation Standards

### Command Notation

All commands follow platform-specific notation:

#### Windows PowerShell
```powershell
# Single command per line
$env:VARIABLE="value"
command1; command2  # Use ; for command chaining
```

#### WSL/Linux/macOS (bash)
```bash
# Single command per line
set -euo pipefail
export VARIABLE="value"
command1
command2
```

### Code Examples

- All code snippets include language tags
- Minimal, accurate examples only
- Comments for prerequisites and warnings

### Information Sources

Priority order:
1. Code
2. Configuration files
3. Tests
4. CI/CD workflows
5. Existing documentation

All facts are verified against actual code where possible.

---

## Project Statistics

| Metric | Value |
|--------|-------|
| **Total Lines of Code** | ~50,000 (Rust) + ~3,000 (Go) |
| **Crates** | 16 |
| **Test Cases** | 400+ |
| **CI/CD Workflows** | 18 |
| **Supported Platforms** | Linux, Windows, macOS, iOS, Android, WASM |
| **Documentation Pages** | 15+ |

---

## Technology Stack Summary

### Languages
- **Rust** 1.70+ (core network stack)
- **Go** 1.21+ (HTTP proxy with Pure Go TLS)
- **TLA+** (formal verification)

### Key Dependencies
- `tokio` 1.37: Async runtime
- `ml-kem` 0.2: Post-quantum cryptography
- `tonic` 0.11: gRPC framework (Pure Rust)
- `criterion` 0.5: Statistical benchmarking

### Infrastructure
- Docker & Kubernetes
- GitHub Actions (CI/CD)
- Prometheus & OpenTelemetry
- Grafana & Jaeger

---

## Quality Assurance

### Test Coverage

| Category | Count | Description |
|----------|-------|-------------|
| Unit Tests | 300+ | Per-module function tests |
| Integration Tests | 50+ | Cross-crate interaction tests |
| Property Tests | 30+ | Randomized testing with proptest |
| Benchmarks | 15+ | Statistical benchmarks with Criterion |
| Fuzz Targets | 10+ | Continuous fuzzing with libFuzzer |
| E2E Tests | 20+ | Real-world Kubernetes tests |
| Formal Specs | 15+ | TLA+ protocol verification |

**Total**: 400+ tests

### Security Measures

- `#![forbid(unsafe_code)]` in all crates
- Zero C/C++ dependencies (Pure Rust/Go)
- Daily security audits (`cargo audit`)
- Automated vulnerability scanning
- Post-quantum cryptography (ML-KEM-768)

---

## License

**Dual License**: MIT OR Apache-2.0

Choose either license for your use case.

---

## Community

- **GitHub**: [SeleniaProject/Nyx](https://github.com/SeleniaProject/Nyx)
- **Issue Tracker**: GitHub Issues
- **Contributing**: See `CONTRIBUTING.md`
- **Code of Conduct**: See `CODE_OF_CONDUCT.md`
- **Security**: See `SECURITY.md`

---

## Versioning

This documentation corresponds to:
- **NyxNet Version**: v1.0
- **Protocol Version**: 1.0
- **API Version**: v1

---

## Disclaimer: Inferred Content

The following information is reasonably inferred from existing documents and code:

- **GitHub repository URL**: Inferred from README badge links
- **Community links**: Standard OSS project structure assumption
- **Some statistics**: Estimated from codebase analysis

For precise information, refer to actual code and configuration files.

---

## Need Help?

- 🐛 **Found a bug?** → [Open an issue](https://github.com/SeleniaProject/Nyx/issues)
- 📖 **Documentation unclear?** → [Open a documentation issue](https://github.com/SeleniaProject/Nyx/issues)
- 💡 **Have a feature idea?** → [Start a discussion](https://github.com/SeleniaProject/Nyx/discussions)
- 🔒 **Security concern?** → See `SECURITY.md` for responsible disclosure

---

**Happy Coding! 🚀**
