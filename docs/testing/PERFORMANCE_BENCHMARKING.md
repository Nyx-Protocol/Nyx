# NyxNet Performance Evaluation - Quick Start Guide

This guide explains how to run comprehensive performance evaluations for NyxNet.

## Overview

NyxNet includes:
- **Application-level benchmarks** (file transfer, messaging, streaming, VoIP)
- **Comparison with existing solutions** (Tor, I2P)
- **Automated report generation** with charts and analysis

## Prerequisites

### System Requirements
- Rust 1.75+ (for benchmarks)
- Python 3.8+ (for report generation)
- Tor (optional, for comparison benchmarks)

### Python Dependencies
```bash
pip install matplotlib pandas numpy
```

### Linux Dependencies (for Tor comparison)
```bash
sudo apt install tor curl bc
```

## Running Benchmarks

### 1. Application Benchmarks (NyxNet only)

Run the comprehensive application-level benchmark suite:

```bash
# Run all benchmarks
cargo bench --package nyx-benchmarks

# Run specific benchmark
cargo bench --package nyx-benchmarks -- file_transfer
cargo bench --package nyx-benchmarks -- messaging
cargo bench --package nyx-benchmarks -- video_streaming
cargo bench --package nyx-benchmarks -- voip
cargo bench --package nyx-benchmarks -- scalability
```

Results are saved to: `target/criterion/`

### 2. Comparison Benchmarks (Tor/I2P)

**Linux/macOS only:**

```bash
# Run comparison with Tor
./scripts/run-comparison-benchmarks.sh
```

**Windows (PowerShell):**

```powershell
# Manual Tor comparison (requires Tor Browser or tor.exe)
# 1. Start Tor (SOCKS proxy on port 9050)
# 2. Run measurements using curl with --socks5 127.0.0.1:9050
```

### 3. Generate Performance Report

Generate comprehensive report with charts:

```bash
python scripts/generate-performance-report.py
```

Output:
- `benchmarks/results/performance_report_<timestamp>.md` - Markdown report
- `benchmarks/results/*.png` - Performance charts

## Understanding the Results

### Key Metrics

| Metric | What it Measures | Target |
|--------|------------------|--------|
| **Throughput** | Data transfer rate (MB/s) | > 5 MB/s |
| **Latency** | Message round-trip time (ms) | < 50ms (P99) |
| **Packet Loss** | % of lost packets | < 2% |
| **MOS Score** | Voice quality (1-5) | > 3.5 |
| **Scalability** | Performance under load | Linear up to 1K connections |

### Interpreting Charts

1. **File Transfer Throughput**: Higher is better
   - NyxNet should achieve 80-85% of direct QUIC performance
   - 3-4× faster than Tor/I2P

2. **Messaging Latency**: Lower is better
   - P99 latency should be < 50ms for real-time apps
   - 10-15× faster than Tor

3. **Scalability**: Flatter curve is better
   - Linear degradation up to 1000 connections
   - Stay below 350ms latency threshold

4. **Video Streaming**: Higher bitrate, lower packet loss
   - Should sustain 2.5 Mbps for 720p
   - < 2% packet loss

## Performance Targets

### ✅ Production Ready Criteria

- File Transfer: > 8 MB/s (80% of direct)
- Messaging P99: < 50ms
- Video 720p: Sustained 2.5 Mbps
- VoIP MOS: > 3.5
- Scalability: < 350ms @ 1000 connections
- vs Tor: > 3× faster
- vs I2P: > 4× faster

### Benchmarking Best Practices

1. **Run multiple iterations** - Use criterion's default (100+ samples)
2. **Warm-up period** - First iteration is always slower
3. **Stable network** - Run on wired connection, not WiFi
4. **Minimal background load** - Close other apps
5. **Consistent hardware** - Document CPU, RAM, network specs

## Troubleshooting

### Benchmarks fail to compile

```bash
# Clean and rebuild
cargo clean
cargo build --release --package nyx-benchmarks
```

### Python script errors

```bash
# Reinstall dependencies
pip install --upgrade matplotlib pandas numpy
```

### Tor comparison fails

```bash
# Check Tor is running
curl --socks5 127.0.0.1:9050 https://check.torproject.org/

# Restart Tor
sudo systemctl restart tor
```

## Continuous Integration

Add to GitHub Actions:

```yaml
- name: Run Performance Benchmarks
  run: |
    cargo bench --package nyx-benchmarks
    python scripts/generate-performance-report.py
    
- name: Upload Performance Report
  uses: actions/upload-artifact@v3
  with:
    name: performance-report
    path: benchmarks/results/
```

## Advanced: Custom Benchmarks

Create custom application benchmarks by extending `tests/benchmarks/application_scenarios.rs`:

```rust
fn bench_my_app(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    c.bench_function("my_application", |b| {
        b.to_async(&rt).iter(|| async {
            // Your benchmark code here
        });
    });
}
```

## References

- [Criterion User Guide](https://bheisler.github.io/criterion.rs/book/)
- [Performance Evaluation Document](../docs/PERFORMANCE_EVALUATION.md)
- [Integration Testing Guide](../docs/INTEGRATION_TESTING.md)
- [Tor Performance](https://www.torproject.org/static/findoc/performance-roadmap-2009-03.pdf)

## Support

For questions about performance evaluation:
- GitHub Issues: https://github.com/SeleniaProject/Nyx/issues
- Documentation: https://github.com/SeleniaProject/Nyx/tree/main/docs

---

**Last Updated**: 2025-10-06  
**Maintainer**: Selenia Project
