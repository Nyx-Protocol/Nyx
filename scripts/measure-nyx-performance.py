#!/usr/bin/env python3
"""
Simple NyxNet Performance Measurement

This script runs a simplified version of NyxNet benchmarks
to get quick performance measurements.
"""

import subprocess
import time
import json
from pathlib import Path

def measure_nyx_performance():
    """Measure NyxNet performance using cargo bench"""
    
    print("=" * 60)
    print("NyxNet Performance Measurement")
    print("=" * 60)
    print()
    
    # Build the benchmarks
    print("Building benchmarks...")
    build_result = subprocess.run(
        ["cargo", "build", "--package", "nyx-benchmarks", "--release"],
        capture_output=True,
        text=True
    )
    
    if build_result.returncode != 0:
        print(f"❌ Build failed: {build_result.stderr}")
        return None
    
    print("✅ Build successful")
    print()
    
    # Run benchmarks with quick mode
    print("Running benchmarks (this may take 2-5 minutes)...")
    print()
    
    bench_result = subprocess.run(
        ["cargo", "bench", "--package", "nyx-benchmarks", "--", "--quick"],
        capture_output=True,
        text=True,
        timeout=300
    )
    
    if bench_result.returncode != 0:
        print(f"⚠️ Benchmark had issues: {bench_result.stderr}")
    
    # Parse output
    output = bench_result.stdout
    print(output)
    
    # Try to extract key metrics
    results = {
        "file_transfer": extract_throughput(output),
        "messaging": extract_latency(output),
    }
    
    return results

def extract_throughput(output):
    """Extract throughput from benchmark output"""
    import re
    
    # Look for patterns like "82.5 MB/s" or "time: [...]"
    for line in output.split('\n'):
        if 'file_transfer' in line.lower() or 'throughput' in line.lower():
            # Try to find MB/s
            match = re.search(r'(\d+\.?\d*)\s*MB/s', line)
            if match:
                return float(match.group(1))
            
            # Try to find time and calculate
            match = re.search(r'time:\s*\[[\d.]+\s+[\w]+\s+([\d.]+)\s+([\w]+)', line)
            if match:
                time_val = float(match.group(1))
                unit = match.group(2)
                
                # Convert to seconds
                if unit == 'ms':
                    time_val /= 1000
                elif unit == 'us' or unit == 'µs':
                    time_val /= 1000000
                
                # Assume 10MB transfer
                if time_val > 0:
                    mbps = (10 * 8) / time_val  # 10MB in megabits
                    return mbps
    
    return 0.0

def extract_latency(output):
    """Extract latency from benchmark output"""
    import re
    
    for line in output.split('\n'):
        if 'messaging' in line.lower() or 'latency' in line.lower():
            # Look for time in ms or µs
            match = re.search(r'([\d.]+)\s*(ms|µs|us)', line)
            if match:
                val = float(match.group(1))
                unit = match.group(2)
                
                # Convert to ms
                if unit in ['µs', 'us']:
                    val /= 1000
                
                return val
    
    return 0.0

def main():
    results = measure_nyx_performance()
    
    if results:
        print()
        print("=" * 60)
        print("✅ NyxNet Performance Results")
        print("=" * 60)
        print()
        print(f"File Transfer: {results['file_transfer']:.2f} MB/s")
        print(f"Messaging: {results['messaging']:.2f} ms")
        print()
        
        # Save results
        output_dir = Path("benchmarks/results")
        output_dir.mkdir(parents=True, exist_ok=True)
        
        with open(output_dir / "nyx_quick_results.json", 'w') as f:
            json.dump(results, f, indent=2)
        
        print(f"✅ Results saved to {output_dir / 'nyx_quick_results.json'}")

if __name__ == "__main__":
    main()
