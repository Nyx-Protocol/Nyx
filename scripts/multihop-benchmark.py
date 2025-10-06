#!/usr/bin/env python3
"""
Multi-hop Network Benchmark for NyxNet
実際のマルチホップ経路でのベンチマーク測定
"""

import socket
import time
import json
import statistics
import os
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305
from typing import List, Tuple

# Configuration
ENTRY_NODE = os.environ.get('ENTRY_NODE', '172.20.0.11:9001')
ITERATIONS = 100
THROUGHPUT_DURATION = 5

# 共有鍵 (実際は各ホップごとに異なる鍵を使用)
KEYS = [
    ChaCha20Poly1305.generate_key(),
    ChaCha20Poly1305.generate_key(),
    ChaCha20Poly1305.generate_key(),
    ChaCha20Poly1305.generate_key(),
]

def encrypt_multi_layer(plaintext: bytes) -> bytes:
    """
    マルチレイヤー暗号化 (Onion routing)
    4層の暗号化を行う (4ホップ分)
    """
    data = plaintext
    
    # 逆順で暗号化 (最後のホップから)
    for key in reversed(KEYS):
        cipher = ChaCha20Poly1305(key)
        nonce = os.urandom(12)
        encrypted = cipher.encrypt(nonce, data, None)
        data = nonce + encrypted
    
    return data

def decrypt_multi_layer(ciphertext: bytes) -> bytes:
    """
    マルチレイヤー復号化
    4層の復号化を行う
    """
    data = ciphertext
    
    # 順番に復号化
    for key in KEYS:
        cipher = ChaCha20Poly1305(key)
        nonce = data[:12]
        encrypted = data[12:]
        data = cipher.decrypt(nonce, encrypted, None)
    
    return data

def measure_multihop_latency(entry_node: str, iterations: int) -> List[float]:
    """マルチホップ経路でのレイテンシ測定"""
    host, port = entry_node.split(':')
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.settimeout(10.0)
    
    latencies = []
    message = b"PING" * 256  # 1KB
    
    print(f"📡 Measuring multi-hop latency (4 hops)")
    print(f"   Entry node: {entry_node}")
    print(f"   Iterations: {iterations}")
    
    for i in range(iterations):
        # マルチレイヤー暗号化
        encrypted = encrypt_multi_layer(message)
        
        start = time.perf_counter()
        sock.sendto(encrypted, (host, int(port)))
        
        try:
            response, _ = sock.recvfrom(65535)
            end = time.perf_counter()
            
            # マルチレイヤー復号化
            decrypted = decrypt_multi_layer(response)
            
            latency_ms = (end - start) * 1000
            latencies.append(latency_ms)
            
            if (i + 1) % 10 == 0:
                print(f"   Progress: {i+1}/{iterations} - Current: {latency_ms:.2f}ms")
                
        except socket.timeout:
            print(f"   ⚠️  Timeout at iteration {i+1}")
            continue
        except Exception as e:
            print(f"   ❌ Error at iteration {i+1}: {e}")
            continue
    
    sock.close()
    return latencies

def measure_multihop_throughput(entry_node: str, duration: int) -> float:
    """マルチホップ経路でのスループット測定"""
    host, port = entry_node.split(':')
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.settimeout(1.0)
    
    message = b"X" * 8192  # 8KB
    bytes_sent = 0
    packets_sent = 0
    
    print(f"\n📊 Measuring multi-hop throughput (4 hops)")
    print(f"   Duration: {duration} seconds")
    print(f"   Packet size: {len(message)} bytes")
    
    start_time = time.time()
    
    while time.time() - start_time < duration:
        encrypted = encrypt_multi_layer(message)
        sock.sendto(encrypted, (host, int(port)))
        bytes_sent += len(encrypted)
        packets_sent += 1
        
        # 定期的に応答を確認
        if packets_sent % 100 == 0:
            try:
                sock.recvfrom(65535)
            except socket.timeout:
                pass
            
            elapsed = time.time() - start_time
            current_mbps = (bytes_sent * 8) / (elapsed * 1_000_000)
            print(f"   Progress: {elapsed:.1f}s - {current_mbps:.2f} Mbps")
    
    elapsed = time.time() - start_time
    throughput_mbps = (bytes_sent * 8) / (elapsed * 1_000_000)
    
    sock.close()
    return throughput_mbps

def run_benchmark(scenario: str):
    """ベンチマーク実行"""
    print(f"=== NyxNet Multi-hop Benchmark ===")
    print(f"Scenario: {scenario}")
    print(f"Entry node: {ENTRY_NODE}")
    print(f"Number of hops: 4\n")
    
    # レイテンシ測定
    latencies = measure_multihop_latency(ENTRY_NODE, ITERATIONS)
    
    if not latencies:
        print("❌ No successful latency measurements")
        return None
    
    avg_latency = statistics.mean(latencies)
    min_latency = min(latencies)
    max_latency = max(latencies)
    median_latency = statistics.median(latencies)
    stdev_latency = statistics.stdev(latencies) if len(latencies) > 1 else 0
    
    print(f"\n✅ Latency Results:")
    print(f"   Average: {avg_latency:.2f} ms")
    print(f"   Median:  {median_latency:.2f} ms")
    print(f"   Min:     {min_latency:.2f} ms")
    print(f"   Max:     {max_latency:.2f} ms")
    print(f"   StdDev:  {stdev_latency:.2f} ms")
    
    # スループット測定
    throughput_mbps = measure_multihop_throughput(ENTRY_NODE, THROUGHPUT_DURATION)
    throughput_mb_per_sec = throughput_mbps / 8
    
    print(f"\n✅ Throughput Results:")
    print(f"   {throughput_mbps:.2f} Mbps")
    print(f"   {throughput_mb_per_sec:.2f} MB/s")
    
    # Torとの比較
    TOR_FILE_TRANSFER_MBPS = 39.30
    TOR_MESSAGING_MS = 1224.38
    
    throughput_speedup = throughput_mb_per_sec / TOR_FILE_TRANSFER_MBPS
    latency_improvement = TOR_MESSAGING_MS / avg_latency
    
    print(f"\n📊 Comparison with Tor:")
    print(f"   Throughput speedup: {throughput_speedup:.2f}x")
    print(f"   Latency improvement: {latency_improvement:.2f}x")
    
    # 結果を保存
    results = {
        "measurement_type": f"Multi-hop network (4 hops) - {scenario} scenario",
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        "scenario": scenario,
        "hops": 4,
        "entry_node": ENTRY_NODE,
        "latency": {
            "average_ms": avg_latency,
            "median_ms": median_latency,
            "min_ms": min_latency,
            "max_ms": max_latency,
            "stdev_ms": stdev_latency,
            "successful_iterations": len(latencies),
            "total_iterations": ITERATIONS
        },
        "throughput": {
            "mbps": throughput_mbps,
            "mb_per_sec": throughput_mb_per_sec,
            "duration_seconds": THROUGHPUT_DURATION
        },
        "comparison": {
            "tor_file_transfer_mbps": TOR_FILE_TRANSFER_MBPS,
            "tor_messaging_latency_ms": TOR_MESSAGING_MS,
            "throughput_speedup": throughput_speedup,
            "latency_improvement": latency_improvement
        }
    }
    
    return results

if __name__ == "__main__":
    import sys
    
    scenario = sys.argv[1] if len(sys.argv) > 1 else "no-delay"
    results = run_benchmark(scenario)
    
    if results:
        output_file = f"/workspace/benchmarks/results/multihop_{scenario}_results.json"
        with open(output_file, 'w') as f:
            json.dump(results, f, indent=2)
        print(f"\n💾 Results saved to: {output_file}")
