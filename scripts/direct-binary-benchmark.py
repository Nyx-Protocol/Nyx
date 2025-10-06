#!/usr/bin/env python3
"""
Direct binary benchmark using pre-built nyx-daemon and nyx-cli
ビルド済みバイナリを直接使用した実測
"""

import subprocess
import time
import json
import os
import signal
from pathlib import Path

def run_daemon(port=9999):
    """Start nyx-daemon"""
    daemon_path = "/mnt/c/Users/Aqua/Programming/SeleniaProject/NyxNet/target/release/nyx-daemon.exe"
    proc = subprocess.Popen(
        [daemon_path, "--port", str(port)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )
    time.sleep(3)  # Wait for daemon to start
    return proc

def benchmark_latency(iterations=100):
    """Measure latency using nyx-cli"""
    cli_path = "/mnt/c/Users/Aqua/Programming/SeleniaProject/NyxNet/target/release/nyx-cli.exe"
    
    print(f"\n[Latency Test] Running {iterations} iterations...")
    latencies = []
    
    for i in range(iterations):
        start = time.perf_counter()
        result = subprocess.run(
            [cli_path, "info"],
            capture_output=True,
            timeout=10
        )
        end = time.perf_counter()
        
        if result.returncode == 0:
            latency_ms = (end - start) * 1000
            latencies.append(latency_ms)
            
            if (i + 1) % 20 == 0:
                print(f"  Progress: {i+1}/{iterations} - Last: {latency_ms:.3f}ms")
    
    if not latencies:
        return None
    
    return {
        "average_ms": sum(latencies) / len(latencies),
        "min_ms": min(latencies),
        "max_ms": max(latencies),
        "median_ms": sorted(latencies)[len(latencies)//2],
        "samples": len(latencies),
        "raw_data": latencies
    }

def benchmark_throughput(duration_seconds=10):
    """Measure throughput"""
    cli_path = "/mnt/c/Users/Aqua/Programming/SeleniaProject/NyxNet/target/release/nyx-cli.exe"
    
    print(f"\n[Throughput Test] Running for {duration_seconds} seconds...")
    
    operations = 0
    total_bytes = 0
    start_time = time.perf_counter()
    end_time = start_time + duration_seconds
    
    while time.perf_counter() < end_time:
        result = subprocess.run(
            [cli_path, "info"],
            capture_output=True,
            timeout=10
        )
        
        if result.returncode == 0:
            operations += 1
            total_bytes += len(result.stdout) if result.stdout else 0
        
        elapsed = time.perf_counter() - start_time
        if operations % 50 == 0:
            print(f"  Progress: {elapsed:.1f}s - {operations} operations")
    
    total_time = time.perf_counter() - start_time
    
    return {
        "operations": operations,
        "total_bytes": total_bytes,
        "duration_seconds": total_time,
        "ops_per_second": operations / total_time,
        "throughput_mbps": (total_bytes / total_time) / (1024 * 1024)
    }

def main():
    print("=" * 80)
    print("REAL NYXNET BINARY BENCHMARK")
    print("Using pre-built nyx-daemon.exe and nyx-cli.exe")
    print("=" * 80)
    
    os.chdir("/mnt/c/Users/Aqua/Programming/SeleniaProject/NyxNet")
    
    daemon = None
    try:
        # Start daemon
        print("\n[Setup] Starting nyx-daemon...")
        daemon = run_daemon()
        print("✅ Daemon started")
        
        # Run benchmarks
        latency_results = benchmark_latency(iterations=100)
        throughput_results = benchmark_throughput(duration_seconds=10)
        
        # Compile results
        results = {
            "method": "direct_binary_benchmark",
            "binaries": {
                "daemon": "target/release/nyx-daemon.exe",
                "cli": "target/release/nyx-cli.exe"
            },
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "latency": latency_results,
            "throughput": throughput_results
        }
        
        # Save results
        output_file = "benchmarks/results/direct_binary_results.json"
        Path(output_file).parent.mkdir(parents=True, exist_ok=True)
        with open(output_file, 'w') as f:
            json.dump(results, f, indent=2)
        
        # Print summary
        print("\n" + "=" * 80)
        print("BENCHMARK RESULTS:")
        print("=" * 80)
        
        if latency_results:
            print(f"\n📊 Latency:")
            print(f"  Average: {latency_results['average_ms']:.3f}ms")
            print(f"  Median:  {latency_results['median_ms']:.3f}ms")
            print(f"  Min:     {latency_results['min_ms']:.3f}ms")
            print(f"  Max:     {latency_results['max_ms']:.3f}ms")
        
        if throughput_results:
            print(f"\n📈 Throughput:")
            print(f"  Operations: {throughput_results['operations']}")
            print(f"  Ops/sec:    {throughput_results['ops_per_second']:.2f}")
            print(f"  Throughput: {throughput_results['throughput_mbps']:.2f} MB/s")
        
        print(f"\n✅ Results saved to: {output_file}")
        print("=" * 80)
        
        return results
        
    finally:
        if daemon:
            print("\n[Cleanup] Stopping daemon...")
            daemon.terminate()
            try:
                daemon.wait(timeout=5)
            except subprocess.TimeoutExpired:
                daemon.kill()
            print("✅ Daemon stopped")

if __name__ == "__main__":
    main()
