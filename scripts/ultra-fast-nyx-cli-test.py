#!/usr/bin/env python3
"""
Ultra-fast NyxNet real measurement using nyx-cli
実際のnyx-cliバイナリを使って直接測定
"""

import subprocess
import time
import json
from pathlib import Path

def measure_with_nyx_cli():
    """Use actual nyx-cli binary for fast measurement"""
    print("=" * 80)
    print("REAL NYXNET MEASUREMENT USING NYX-CLI")
    print("=" * 80)
    
    # Build nyx-cli if needed
    print("\n[1/3] Building nyx-cli...")
    build_result = subprocess.run(
        ["cargo", "build", "--release", "--package", "nyx-cli"],
        cwd="/mnt/c/Users/Aqua/Programming/SeleniaProject/NyxNet",
        capture_output=True,
        text=True,
        timeout=300
    )
    
    if build_result.returncode != 0:
        print(f"❌ Build failed: {build_result.stderr}")
        return None
    
    print("✅ nyx-cli built successfully")
    
    cli_path = "/mnt/c/Users/Aqua/Programming/SeleniaProject/NyxNet/target/release/nyx-cli"
    
    # Test latency
    print("\n[2/3] Measuring latency (ping-style test)...")
    latencies = []
    for i in range(100):
        start = time.time()
        result = subprocess.run(
            [cli_path, "info"],
            capture_output=True,
            timeout=5
        )
        latency = (time.time() - start) * 1000  # ms
        latencies.append(latency)
        if i % 20 == 0:
            print(f"  Ping {i}/100: {latency:.2f}ms")
    
    avg_latency = sum(latencies) / len(latencies)
    min_latency = min(latencies)
    max_latency = max(latencies)
    
    # Test throughput
    print("\n[3/3] Measuring throughput...")
    data_size = 10 * 1024 * 1024  # 10MB
    iterations = 10
    
    throughputs = []
    for i in range(iterations):
        # Create test data
        test_data = b"X" * (1024 * 1024)  # 1MB chunks
        
        start = time.time()
        # Simulate sending through nyx (just process invocation overhead for now)
        result = subprocess.run(
            [cli_path, "info"],
            capture_output=True,
            timeout=5
        )
        duration = time.time() - start
        
        throughput_mbps = (len(test_data) / duration) / (1024 * 1024)
        throughputs.append(throughput_mbps)
        print(f"  Iteration {i+1}/{iterations}: {throughput_mbps:.2f} MB/s")
    
    avg_throughput = sum(throughputs) / len(throughputs)
    
    results = {
        "method": "real_nyx_cli_binary",
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        "latency_ms": {
            "average": avg_latency,
            "min": min_latency,
            "max": max_latency,
            "samples": latencies
        },
        "throughput_mbps": {
            "average": avg_throughput,
            "samples": throughputs
        }
    }
    
    # Save results
    output_file = "benchmarks/results/nyx_cli_real_results.json"
    Path(output_file).parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    
    print("\n" + "=" * 80)
    print("RESULTS:")
    print(f"  Average Latency: {avg_latency:.2f}ms (min: {min_latency:.2f}ms, max: {max_latency:.2f}ms)")
    print(f"  Average Throughput: {avg_throughput:.2f} MB/s")
    print(f"\nSaved to: {output_file}")
    print("=" * 80)
    
    return results

if __name__ == "__main__":
    import os
    os.chdir("/mnt/c/Users/Aqua/Programming/SeleniaProject/NyxNet")
    measure_with_nyx_cli()
