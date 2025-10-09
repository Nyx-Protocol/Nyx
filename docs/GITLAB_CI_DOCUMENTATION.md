# GitLab CI/CD Pipeline Documentation

## Overview

This document describes the comprehensive GitLab CI/CD pipeline for the Nyx Protocol project. The pipeline is designed with world-class DevOps practices, following strict constraints and automation principles.

## Key Principles

### 1. Zero C/C++ Dependencies
**Strict Constraint**: All CI/CD tools and processes must avoid C/C++ dependencies.

**Replacements implemented**:
- `hadolint` → `dockerfilelint` (Node.js-based Dockerfile linter)
- Traditional compilers → Pure Rust/Go toolchains
- Native tools → Cross-platform alternatives

### 2. Maximum Automation
- Parallel job execution within stages
- Automatic dependency caching
- Self-healing build processes
- Automated security scanning

### 3. Comprehensive Quality Gates
- Code formatting validation
- Compilation checks
- Unit and integration tests
- Security vulnerability scanning
- License compliance verification
- Performance benchmarking

## Pipeline Architecture

### Stage Overview

```
prepare       → dependency resolution, validation
    ↓
build         → Rust/Go compilation, WASM builds
    ↓
test          → unit tests, integration tests
    ↓
quality       → linting, formatting, clippy
    ↓
security      → SAST, vulnerability scanning
    ↓
verify        → Docker validation, K8s checks
    ↓
coverage      → code coverage analysis
    ↓
package       → Docker image builds
    ↓
release       → deployment to staging/production
```

### Modular Configuration Files

The pipeline is split into modular configuration files for maintainability:

#### `.gitlab-ci.yml` (Main Configuration)
- Base templates and cache definitions
- Rust build and test jobs
- Go build and test jobs
- WASM compilation
- Docker and Kubernetes validation
- Coverage reporting

#### `.gitlab-ci-mr.yml` (Merge Request Optimizations)
- Fast feedback for MR changes
- Path-based job triggering
- Component-specific testing
- Commit message validation
- Quick security checks

#### `.gitlab-ci-security.yml` (Enhanced Security)
- Advanced SAST with Semgrep
- Dependency vulnerability scanning (cargo-audit, govulncheck)
- Container image scanning (Trivy)
- License compliance checks
- Supply chain security validation

#### `.gitlab-ci-perf.yml` (Performance Testing)
- Rust benchmarks with Criterion
- Go benchmark suite
- Performance regression detection
- Memory profiling
- Binary size analysis

#### `.gitlab-ci-deploy.yml` (Deployment Automation)
- Docker image building and publishing
- Helm chart packaging
- Staging environment deployment
- Production deployment with manual approval
- Automated rollback capabilities
- Deployment verification checks

## Job Catalog

### Prepare Stage

#### `validate:toolchain`
**Purpose**: Verify Rust and Go toolchains are correctly configured
**Runs**: On all pipelines
**Key Checks**:
- Rust version and components
- Go version
- Protobuf compiler availability

#### `validate:config`
**Purpose**: Validate TOML, YAML, and JSON configuration files
**Tools**: taplo (Rust), yamllint (Python), jq (C-free)

### Build Stage

#### `rust:build`
**Purpose**: Build all Rust workspace crates
**Artifacts**: Compiled binaries, build logs
**Cache**: Cargo registry and build artifacts

#### `rust:build-wasm`
**Purpose**: Compile nyx-sdk-wasm for WebAssembly target
**Target**: wasm32-unknown-unknown
**Tools**: wasm-pack, wasm-bindgen

#### `go:build`
**Purpose**: Build nyx-http-proxy Go component
**Artifacts**: HTTP proxy binary

### Test Stage

#### `rust:test`
**Purpose**: Run all Rust unit and integration tests
**Coverage**: Workspace-wide test execution
**Timeout**: 30 minutes

#### `go:test`
**Purpose**: Run Go tests for HTTP proxy
**Coverage**: Full package test suite

#### `rust:test-integration`
**Purpose**: Run integration tests requiring external services
**Services**: Redis for state management
**Network**: Custom test network setup

### Quality Stage

#### `rust:fmt`
**Purpose**: Verify Rust code formatting with rustfmt
**Enforcement**: Strict formatting compliance

#### `rust:clippy`
**Purpose**: Run Clippy linter for Rust code quality
**Settings**: All warnings treated as errors

#### `go:lint`
**Purpose**: Lint Go code with golangci-lint
**Checks**: Multiple linter configurations

### Security Stage

#### `security:semgrep`
**Purpose**: Static analysis with Semgrep
**Rulesets**: p/default, p/security-audit, p/rust, p/golang

#### `security:cargo-audit`
**Purpose**: Check Rust dependencies for known vulnerabilities
**Database**: RustSec Advisory Database

#### `security:govulncheck`
**Purpose**: Check Go dependencies for vulnerabilities
**Database**: Go Vulnerability Database

#### `security:trivy`
**Purpose**: Scan container images for vulnerabilities
**Scope**: OS packages and dependencies

#### `security:license-compliance`
**Purpose**: Verify license compatibility
**Tools**: cargo-license, go-licenses

### Verify Stage

#### `verify:docker`
**Purpose**: Validate Dockerfile syntax and best practices
**Tool**: dockerfilelint (Node.js, no C/C++)
**Replacement**: Chosen instead of hadolint (Haskell/C dependency)

#### `verify:kubernetes`
**Purpose**: Validate Kubernetes manifests
**Tool**: kubeconform (Go-based)
**Files**: All YAML manifests in k8s-*.yaml

#### `verify:helm`
**Purpose**: Lint Helm chart
**Tool**: helm lint
**Chart**: charts/nyx/

### Coverage Stage

#### `coverage:rust`
**Purpose**: Generate code coverage report for Rust
**Tool**: cargo-tarpaulin
**Output**: Cobertura XML, HTML report

#### `coverage:go`
**Purpose**: Generate code coverage for Go
**Tool**: go test -cover
**Output**: Coverage profile and HTML

### Package Stage

#### `docker:build-daemon`
**Purpose**: Build and publish nyx-daemon Docker image
**Registry**: GitLab Container Registry
**Tags**: commit SHA, latest

#### `docker:build-cli`
**Purpose**: Build and publish nyx-cli Docker image

#### `docker:build-http-proxy`
**Purpose**: Build and publish nyx-http-proxy Docker image

#### `helm:package`
**Purpose**: Package Helm chart for deployment
**Versioning**: Git commit SHA, semantic version tags

### Release Stage

#### `deploy:staging`
**Purpose**: Deploy to staging Kubernetes environment
**Trigger**: Manual on main branch
**Environment**: staging namespace

#### `verify:staging`
**Purpose**: Verify staging deployment health
**Checks**: Pod readiness, health endpoints

#### `deploy:production`
**Purpose**: Deploy to production environment
**Trigger**: Manual on version tags
**Requirements**: Passed all quality gates

#### `verify:production`
**Purpose**: Verify production deployment
**Checks**: Pod health, smoke tests

#### `rollback:staging` / `rollback:production`
**Purpose**: Rollback to previous deployment
**Trigger**: Manual intervention

## Caching Strategy

### Rust Cache
**Key**: `${CI_COMMIT_REF_SLUG}-rust`
**Paths**:
- `.cargo/` - Cargo registry and git checkouts
- `target/` - Build artifacts and incremental compilation

**Policy**: Pull-push (download on start, upload on success)

### Go Cache
**Key**: `${CI_COMMIT_REF_SLUG}-go`
**Paths**:
- `.go/` - Go modules
- `.gocache/` - Build cache

### Node.js Cache (for dockerfilelint)
**Key**: `${CI_COMMIT_REF_SLUG}-node`
**Paths**:
- `.npm/` - npm package cache

## Artifacts

### Build Artifacts
- Compiled binaries (1 week retention)
- WASM packages (1 week retention)

### Test Artifacts
- Test result XML (1 week retention)
- Integration test logs (1 week retention)

### Security Artifacts
- Semgrep SARIF reports (1 month retention)
- Vulnerability scan results (1 month retention)
- License compliance reports (1 month retention)

### Coverage Artifacts
- HTML coverage reports (1 month retention)
- Cobertura XML (for GitLab integration, 1 month retention)

### Performance Artifacts
- Benchmark results (1 month retention)
- Performance reports (1 month retention)

### Release Artifacts
- Docker images (permanent in registry)
- Helm charts (permanent)
- Release notes (permanent)

## Environment Variables

### Required CI/CD Variables (set in GitLab)
- `CI_REGISTRY_USER` - GitLab registry username (automatic)
- `CI_REGISTRY_PASSWORD` - GitLab registry token (automatic)
- `KUBE_CONFIG_STAGING` - Kubernetes config for staging (manual)
- `KUBE_CONFIG_PRODUCTION` - Kubernetes config for production (manual)

### Optional Variables
- `BENCH_COMPARE_THRESHOLD` - Performance regression threshold (default: 5%)
- `CARGO_NET_RETRY` - Cargo network retry count (default: 10)
- `SEMGREP_RULES` - Additional Semgrep rulesets

## Merge Request Pipeline

When a merge request is created, the pipeline automatically optimizes for fast feedback:

### Fast Path Execution
- Only affected components are tested
- Parallel execution of independent checks
- Incremental builds using cached artifacts

### Path-Based Triggering
- Rust changes → Rust jobs only
- Go changes → Go jobs only
- Config changes → Validation jobs only

### Quality Gates
- All tests must pass
- No security vulnerabilities introduced
- Code coverage maintained
- Conventional commit format enforced

## Security Best Practices

### Dependency Scanning
- **Rust**: cargo-audit checks against RustSec database
- **Go**: govulncheck uses Go Vulnerability Database
- **Containers**: Trivy scans OS and application dependencies

### Static Analysis
- **Semgrep**: Multi-language security patterns
- **Clippy**: Rust-specific linting and security checks
- **golangci-lint**: Go code quality and security

### Supply Chain Security
- Pin exact tool versions
- Verify checksums where possible
- Use official Docker images only
- Scan all container images before deployment

### License Compliance
- Automated license detection
- Compatibility verification
- Attribution generation

## Performance Monitoring

### Benchmarking
- Criterion benchmarks for Rust (statistical analysis)
- Go benchmark suite with memory profiling
- Regression detection with configurable thresholds

### Resource Profiling
- Binary size tracking (cargo-bloat)
- Memory allocation patterns
- CPU profiling for hot paths

### Integration Performance
- Real-world network operations
- Load testing under production conditions
- Latency and throughput metrics

## Deployment Strategy

### Staging Environment
- Automatic builds on main branch
- Manual deployment trigger
- 2 replicas for high availability
- Automated health checks

### Production Environment
- Triggered by semantic version tags (v1.2.3)
- Manual approval required
- 3+ replicas for redundancy
- Enhanced resource limits
- Comprehensive smoke testing

### Rollback Procedure
1. Manual trigger of rollback job
2. Helm reverts to previous release
3. Verification of pod health
4. Traffic cutover confirmation

## Troubleshooting

### Build Failures

**Symptom**: Rust build fails with dependency errors
**Solution**: Clear cache, run `cargo clean`, retry pipeline

**Symptom**: Go build fails with module errors
**Solution**: Verify go.mod/go.sum, run `go mod tidy`

### Test Failures

**Symptom**: Integration tests timeout
**Solution**: Check Redis service connectivity, increase timeout

**Symptom**: Flaky tests
**Solution**: Run tests with `--test-threads=1`, investigate race conditions

### Security Scan Failures

**Symptom**: False positive in Semgrep
**Solution**: Add `# nosemgrep` comment with justification

**Symptom**: Vulnerability in dependency
**Solution**: Upgrade dependency, or add exception with risk assessment

### Deployment Issues

**Symptom**: Pod fails to start
**Solution**: Check image pull credentials, verify resource limits

**Symptom**: Health check failures
**Solution**: Review application logs, verify service dependencies

## Optimization Tips

### Reduce Pipeline Duration
1. Enable parallel execution where possible
2. Use artifacts between jobs instead of rebuilding
3. Optimize cache keys for better hit rates
4. Consider splitting large test suites

### Reduce Resource Usage
1. Use `--release` builds only when needed
2. Clean up large artifacts after use
3. Compress artifacts before upload
4. Set appropriate retention policies

### Improve Cache Hit Rate
1. Use consistent cache keys
2. Separate fast-changing from stable dependencies
3. Use `cache:policy: pull` for read-only jobs
4. Clean cache on toolchain updates

## Maintenance

### Regular Tasks
- **Weekly**: Review failed pipelines, update dependencies
- **Monthly**: Update base Docker images, review cache efficiency
- **Quarterly**: Audit security scan results, update documentation
- **Yearly**: Major version updates, architecture review

### Monitoring
- Pipeline success rate
- Average pipeline duration
- Cache hit rate
- Security scan findings
- Deployment frequency

## Contributing

When adding new jobs or modifying the pipeline:

1. Follow the modular structure (use appropriate .gitlab-ci-*.yml file)
2. Add comprehensive comments explaining purpose
3. Use base templates (`.rust_base`, `.go_base`, etc.)
4. Test changes in a feature branch first
5. Update this documentation
6. Ensure no C/C++ dependencies introduced

## References

- [GitLab CI/CD Documentation](https://docs.gitlab.com/ee/ci/)
- [Rust CI/CD Best Practices](https://doc.rust-lang.org/cargo/guide/continuous-integration.html)
- [Go Testing Best Practices](https://go.dev/doc/tutorial/add-a-test)
- [Helm Chart Best Practices](https://helm.sh/docs/chart_best_practices/)
- [Kubernetes Security Best Practices](https://kubernetes.io/docs/concepts/security/)

---

**Last Updated**: 2025-01-23  
**Pipeline Version**: 1.0.0  
**Maintainer**: Nyx Protocol DevOps Team
