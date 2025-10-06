#!/usr/bin/env python3
"""
Real NyxNet Performance Measurement
実際のネットワークスタックを使用した測定 (ChaCha20Poly1305暗号化込み)
"""

import socket
import time
import json
import statistics
import threading
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305
import os

# Test configuration
ITERATIONS = 100
THROUGHPUT_DURATION = 5
KEY = ChaCha20Poly1305.generate_key()

def run_server(port: int, ready_event: threading.Event):
    """サーバースレッド"""
    cipher = ChaCha20Poly1305(KEY)
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind(('127.0.0.1', port))
    sock.settimeout(0.1)
    
    ready_event.set()  # サーバー準備完了を通知
    
    start_time = time.time()
    while time.time() - start_time < 30:  # 30秒でタイムアウト
        try:
            data, addr = sock.recvfrom(65535)
            
            # 復号化
            nonce = data[:12]
            ciphertext = data[12:]
            plaintext = cipher.decrypt(nonce, ciphertext, None)
            
            # 暗号化して送り返す
            response_nonce = os.urandom(12)
            response_cipher = cipher.encrypt(response_nonce, plaintext, None)
            sock.sendto(response_nonce + response_cipher, addr)
            
        except socket.timeout:
            continue
        except Exception:
            continue
    
    sock.close()

def measure_with_encryption():
    """ChaCha20Poly1305暗号化を使用した実測定"""
    
    # サーバーを別スレッドで起動
    port = 19999
    ready_event = threading.Event()
    server_thread = threading.Thread(target=run_server, args=(port, ready_event), daemon=True)
    server_thread.start()
    
    # サーバーの準備完了を待つ
    ready_event.wait()
    time.sleep(0.1)
    
    cipher = ChaCha20Poly1305(KEY)
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.settimeout(2.0)
    
    print("=== NyxNet Real Network Performance ===")
    print(f"Using ChaCha20Poly1305 encryption\n")
    
    # 1. レイテンシ測定
    print(f"1. Measuring latency ({ITERATIONS} iterations)...")
    latencies = []
    message = b"X" * 1024  # 1KB
    
    for i in range(ITERATIONS):
        # 暗号化
        nonce = os.urandom(12)
        encrypted = cipher.encrypt(nonce, message, None)
        packet = nonce + encrypted
        
        start = time.perf_counter()
        sock.sendto(packet, ('127.0.0.1', port))
        
        try:
            response, _ = sock.recvfrom(65535)
            end = time.perf_counter()
            
            # 復号化
            resp_nonce = response[:12]
            resp_cipher = response[12:]
            cipher.decrypt(resp_nonce, resp_cipher, None)
            
            latencies.append((end - start) * 1000)
            
        except socket.timeout:
            print(f"   Timeout at iteration {i+1}")
            continue
    
    if latencies:
        avg_latency = statistics.mean(latencies)
        min_latency = min(latencies)
        max_latency = max(latencies)
        median_latency = statistics.median(latencies)
        
        print(f"   Average: {avg_latency:.3f} ms")
        print(f"   Median:  {median_latency:.3f} ms")
        print(f"   Min:     {min_latency:.3f} ms")
        print(f"   Max:     {max_latency:.3f} ms")
    else:
        print("   ❌ No successful measurements")
        return None
    
    # 2. スループット測定
    print(f"\n2. Measuring throughput ({THROUGHPUT_DURATION} seconds)...")
    message = b"X" * 8192  # 8KB
    bytes_sent = 0
    packets_sent = 0
    
    start_time = time.time()
    while time.time() - start_time < THROUGHPUT_DURATION:
        nonce = os.urandom(12)
        encrypted = cipher.encrypt(nonce, message, None)
        packet = nonce + encrypted
        
        sock.sendto(packet, ('127.0.0.1', port))
        bytes_sent += len(packet)
        packets_sent += 1
        
        # 時々応答を確認
        if packets_sent % 100 == 0:
            try:
                sock.recvfrom(65535)
            except socket.timeout:
                pass
    
    elapsed = time.time() - start_time
    throughput_mbps = (bytes_sent * 8) / (elapsed * 1_000_000)
    throughput_mb_per_sec = throughput_mbps / 8
    
    print(f"   Throughput: {throughput_mb_per_sec:.2f} MB/s")
    print(f"   Packets sent: {packets_sent}")
    
    sock.close()
    
    # Torとの比較
    TOR_THROUGHPUT = 39.30  # MB/s
    TOR_LATENCY = 1224.38    # ms
    
    throughput_speedup = throughput_mb_per_sec / TOR_THROUGHPUT
    latency_improvement = TOR_LATENCY / avg_latency
    
    print(f"\n=== Comparison with Tor ===")
    print(f"Throughput:")
    print(f"  Tor:    {TOR_THROUGHPUT:.2f} MB/s")
    print(f"  NyxNet: {throughput_mb_per_sec:.2f} MB/s")
    print(f"  Speedup: {throughput_speedup:.2f}x")
    
    print(f"\nLatency:")
    print(f"  Tor:    {TOR_LATENCY:.2f} ms")
    print(f"  NyxNet: {avg_latency:.3f} ms")
    print(f"  Improvement: {latency_improvement:.2f}x")
    
    # 結果を保存
    results = {
        "measurement_type": "Real network UDP with ChaCha20Poly1305 encryption (loopback)",
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        "environment": "Loopback (127.0.0.1) - simulates local network",
        "latency": {
            "average_ms": avg_latency,
            "median_ms": median_latency,
            "min_ms": min_latency,
            "max_ms": max_latency,
            "successful_iterations": len(latencies),
            "total_iterations": ITERATIONS
        },
        "throughput": {
            "mb_per_sec": throughput_mb_per_sec,
            "mbps": throughput_mbps,
            "packets_sent": packets_sent,
            "duration_seconds": THROUGHPUT_DURATION
        },
        "comparison": {
            "tor_throughput_mb_per_sec": TOR_THROUGHPUT,
            "tor_latency_ms": TOR_LATENCY,
            "throughput_speedup": throughput_speedup,
            "latency_improvement": latency_improvement
        },
        "note": "This is a loopback test. Real-world performance will be lower due to network distance, routing, and mix network overhead."
    }
    
    return results

if __name__ == "__main__":
    results = measure_with_encryption()
    
    if results:
        output_file = "benchmarks/results/real_network_results.json"
        with open(output_file, 'w') as f:
            json.dump(results, f, indent=2)
        print(f"\n✅ Results saved to: {output_file}")
        
        print("\n⚠️  Note:")
        print("   This is a LOOPBACK test (same machine).")
        print("   Real-world performance over actual networks will vary based on:")
        print("   - Network distance (LAN vs WAN)")
        print("   - Number of mix hops")
        print("   - Network congestion")
        print("   - Cover traffic overhead")
