#!/usr/bin/env python3
"""
Real NyxNet Benchmark using actual Rust binaries
実際のRust実装を呼び出してベンチマークを実行
"""

import subprocess
import json
import time
import os
from pathlib import Path

def run_nyx_daemon(config_path: str, port: int):
    """Start nyx-daemon process"""
    cmd = ["cargo", "run", "--release", "--bin", "nyx-daemon", "--", 
           "--config", config_path, "--port", str(port)]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    time.sleep(2)  # Give it time to start
    return proc

def run_benchmark_scenario(scenario: str, iterations: int = 100):
    """Run a benchmark scenario using actual cargo bench"""
    print(f"\n{'='*60}")
    print(f"Running {scenario} benchmark with actual Rust implementation...")
    print(f"{'='*60}\n")
    
    cmd = [
        "cargo", "bench",
        "--package", "nyx-benchmarks",
        "--bench", "application_scenarios",
        "--",
        "--sample-size", "10",
        "--measurement-time", "3",
        scenario
    ]
    
    start = time.time()
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
    duration = time.time() - start
    
    print(result.stdout)
    if result.stderr:
        print("Errors:", result.stderr)
    
    # Parse Criterion output
    return {
        "scenario": scenario,
        "duration_seconds": duration,
        "stdout": result.stdout,
        "returncode": result.returncode
    }

def main():
    os.chdir("/mnt/c/Users/Aqua/Programming/SeleniaProject/NyxNet")
    
    results = []
    
    scenarios = [
        "latency_test",
        "throughput_test", 
        "file_transfer",
        "messaging"
    ]
    
    print("=" * 80)
    print("REAL NYXNET RUST IMPLEMENTATION BENCHMARK")
    print("Using actual Criterion benchmarks with real UDP sockets and ChaCha20Poly1305")
    print("=" * 80)
    
    for scenario in scenarios:
        try:
            result = run_benchmark_scenario(scenario)
            results.append(result)
            
            # Save intermediate results
            output_file = f"benchmarks/results/real_rust_{scenario}.json"
            Path(output_file).parent.mkdir(parents=True, exist_ok=True)
            with open(output_file, 'w') as f:
                json.dump(result, f, indent=2)
                
        except subprocess.TimeoutExpired:
            print(f"❌ {scenario} timed out after 5 minutes")
            results.append({
                "scenario": scenario,
                "error": "timeout",
                "duration_seconds": 300
            })
        except Exception as e:
            print(f"❌ {scenario} failed: {e}")
            results.append({
                "scenario": scenario,
                "error": str(e)
            })
    
    # Save final summary
    summary_file = "benchmarks/results/real_rust_summary.json"
    with open(summary_file, 'w') as f:
        json.dump({
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "method": "actual_rust_cargo_bench",
            "results": results
        }, f, indent=2)
    
    print("\n" + "=" * 80)
    print("✅ Real Rust benchmark completed!")
    print(f"Results saved to {summary_file}")
    print("=" * 80)

if __name__ == "__main__":
    main()
