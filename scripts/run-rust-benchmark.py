#!/usr/bin/env python3
"""
Quick Real NyxNet Benchmark using actual Rust binary
実際のRustバイナリを使用した高速ベンチマーク
"""

import subprocess
import json
import time
import re
from typing import Dict, List

def run_rust_benchmark(scenario: str = "baseline") -> Dict:
    """
    実際のRustベンチマークを実行
    """
    print(f"🚀 Running Rust benchmarks for {scenario} scenario...")
    
    cmd = [
        "cargo", "bench",
        "--package", "nyx-benchmarks",
        "--bench", "application_scenarios",
        "--",
        "--warm-up-time", "1",
        "--measurement-time", "3",
        "--sample-size", "10",
        "--noplot"
    ]
    
    try:
        result = subprocess.run(
            cmd,
            cwd="/mnt/c/Users/Aqua/Programming/SeleniaProject/NyxNet",
            capture_output=True,
            text=True,
            timeout=300
        )
        
        output = result.stdout + result.stderr
        print(output)
        
        # Parse Criterion output
        throughput_pattern = r"(\d+\.?\d*)\s*(MB/s|KB/s|GB/s)"
        latency_pattern = r"(\d+\.?\d*)\s*(µs|ms|s)"
        
        throughputs = re.findall(throughput_pattern, output)
        latencies = re.findall(latency_pattern, output)
        
        return {
            "scenario": scenario,
            "throughputs": throughputs,
            "latencies": latencies,
            "raw_output": output
        }
        
    except subprocess.TimeoutExpired:
        print("⚠️  Benchmark timed out after 5 minutes")
        return None
    except Exception as e:
        print(f"❌ Error running benchmark: {e}")
        return None

def main():
    print("=== Real NyxNet Rust Benchmarks ===\n")
    
    results = run_rust_benchmark("baseline")
    
    if results:
        output_file = "benchmarks/results/rust_benchmark_results.json"
        with open(output_file, 'w') as f:
            json.dump(results, f, indent=2)
        print(f"\n✅ Results saved to: {output_file}")
    else:
        print("\n❌ Benchmark failed")

if __name__ == "__main__":
    main()
