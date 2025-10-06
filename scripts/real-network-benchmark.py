#!/usr/bin/env python3
"""
Real Network Performance Benchmark for NyxNet
実際のネットワーク経由でのパフォーマンス測定

このスクリプトは2つのモードで動作します:
1. Server mode: メッセージを受信して応答
2. Client mode: サーバーにメッセージを送信してレイテンシ・スループットを測定
"""

import socket
import time
import json
import statistics
import argparse
import sys
from typing import List, Tuple
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.hazmat.backends import default_backend
import os

# Shared secret for encryption (本番環境では鍵交換プロトコルを使用)
SHARED_SECRET = b"nyx-benchmark-shared-secret-2025"

def derive_key(secret: bytes) -> bytes:
    """共有秘密から暗号化キーを導出"""
    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=32,
        salt=b"nyx-network-benchmark",
        iterations=100000,
        backend=default_backend()
    )
    return kdf.derive(secret)

class NyxNetworkBenchmark:
    def __init__(self, host: str, port: int):
        self.host = host
        self.port = port
        self.key = derive_key(SHARED_SECRET)
        self.cipher = ChaCha20Poly1305(self.key)
        
    def encrypt_message(self, plaintext: bytes) -> bytes:
        """メッセージを暗号化 (NyxNetの暗号化をシミュレート)"""
        nonce = os.urandom(12)
        ciphertext = self.cipher.encrypt(nonce, plaintext, None)
        return nonce + ciphertext
    
    def decrypt_message(self, encrypted: bytes) -> bytes:
        """メッセージを復号化"""
        nonce = encrypted[:12]
        ciphertext = encrypted[12:]
        return self.cipher.decrypt(nonce, ciphertext, None)
    
    def run_server(self):
        """サーバーモード: メッセージを受信して応答"""
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.bind((self.host, self.port))
        
        print(f"🚀 NyxNet Benchmark Server started on {self.host}:{self.port}")
        print("Waiting for client connections...")
        
        try:
            while True:
                data, addr = sock.recvfrom(65535)
                
                # メッセージを復号化
                try:
                    decrypted = self.decrypt_message(data)
                    
                    # エコーバック (暗号化して返信)
                    response = self.encrypt_message(decrypted)
                    sock.sendto(response, addr)
                    
                    if len(decrypted) < 100:
                        print(f"📨 Received from {addr}: {len(data)} bytes (encrypted)")
                    else:
                        print(f"📦 Large message from {addr}: {len(data)} bytes")
                        
                except Exception as e:
                    print(f"❌ Error processing message from {addr}: {e}")
                    
        except KeyboardInterrupt:
            print("\n👋 Server shutting down...")
        finally:
            sock.close()
    
    def measure_latency(self, iterations: int = 100) -> List[float]:
        """レイテンシを測定"""
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.settimeout(5.0)
        
        latencies = []
        message = b"PING" * 256  # 1KB message
        
        print(f"\n📡 Measuring latency to {self.host}:{self.port}")
        print(f"   Iterations: {iterations}")
        
        for i in range(iterations):
            encrypted_msg = self.encrypt_message(message)
            
            start = time.perf_counter()
            sock.sendto(encrypted_msg, (self.host, self.port))
            
            try:
                response, _ = sock.recvfrom(65535)
                end = time.perf_counter()
                
                # 復号化して検証
                decrypted = self.decrypt_message(response)
                
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
    
    def measure_throughput(self, duration_seconds: int = 10, packet_size: int = 8192) -> float:
        """スループットを測定"""
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.settimeout(1.0)
        
        message = b"X" * packet_size
        bytes_sent = 0
        packets_sent = 0
        
        print(f"\n📊 Measuring throughput to {self.host}:{self.port}")
        print(f"   Duration: {duration_seconds} seconds")
        print(f"   Packet size: {packet_size} bytes")
        
        start_time = time.time()
        
        while time.time() - start_time < duration_seconds:
            encrypted_msg = self.encrypt_message(message)
            sock.sendto(encrypted_msg, (self.host, self.port))
            bytes_sent += len(encrypted_msg)
            packets_sent += 1
            
            # 定期的に応答を確認
            if packets_sent % 100 == 0:
                try:
                    sock.recvfrom(65535)
                except socket.timeout:
                    pass
            
            if packets_sent % 1000 == 0:
                elapsed = time.time() - start_time
                current_mbps = (bytes_sent * 8) / (elapsed * 1_000_000)
                print(f"   Progress: {elapsed:.1f}s - {current_mbps:.2f} Mbps")
        
        elapsed = time.time() - start_time
        throughput_mbps = (bytes_sent * 8) / (elapsed * 1_000_000)
        
        sock.close()
        return throughput_mbps
    
    def run_client(self, latency_iterations: int = 100, throughput_duration: int = 10):
        """クライアントモード: 測定を実行"""
        print(f"🎯 NyxNet Benchmark Client")
        print(f"   Target: {self.host}:{self.port}")
        
        # 1. レイテンシ測定
        latencies = self.measure_latency(latency_iterations)
        
        if not latencies:
            print("❌ Failed to measure latency")
            return
        
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
        
        # 2. スループット測定
        throughput_mbps = self.measure_throughput(throughput_duration)
        throughput_mb_per_sec = throughput_mbps / 8
        
        print(f"\n✅ Throughput Results:")
        print(f"   {throughput_mbps:.2f} Mbps")
        print(f"   {throughput_mb_per_sec:.2f} MB/s")
        
        # 3. Torとの比較
        TOR_FILE_TRANSFER_MBPS = 39.30
        TOR_MESSAGING_MS = 1224.38
        
        throughput_speedup = throughput_mb_per_sec / TOR_FILE_TRANSFER_MBPS
        latency_improvement = TOR_MESSAGING_MS / avg_latency
        
        print(f"\n📊 Comparison with Tor:")
        print(f"   Throughput speedup: {throughput_speedup:.2f}x")
        print(f"   Latency improvement: {latency_improvement:.2f}x")
        
        # 4. 結果を保存
        results = {
            "measurement_type": "Real network with ChaCha20Poly1305 encryption",
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "server": f"{self.host}:{self.port}",
            "latency": {
                "average_ms": avg_latency,
                "median_ms": median_latency,
                "min_ms": min_latency,
                "max_ms": max_latency,
                "stdev_ms": stdev_latency,
                "iterations": len(latencies)
            },
            "throughput": {
                "mbps": throughput_mbps,
                "mb_per_sec": throughput_mb_per_sec,
                "duration_seconds": throughput_duration
            },
            "comparison": {
                "tor_file_transfer_mbps": TOR_FILE_TRANSFER_MBPS,
                "tor_messaging_latency_ms": TOR_MESSAGING_MS,
                "throughput_speedup": throughput_speedup,
                "latency_improvement": latency_improvement
            }
        }
        
        output_file = "benchmarks/results/real_network_results.json"
        with open(output_file, 'w') as f:
            json.dump(results, f, indent=2)
        
        print(f"\n💾 Results saved to: {output_file}")

def main():
    parser = argparse.ArgumentParser(description="NyxNet Real Network Benchmark")
    parser.add_argument("mode", choices=["server", "client"], help="Run as server or client")
    parser.add_argument("--host", default="0.0.0.0", help="Host address (default: 0.0.0.0 for server, required for client)")
    parser.add_argument("--port", type=int, default=9999, help="Port number (default: 9999)")
    parser.add_argument("--latency-iterations", type=int, default=100, help="Number of latency measurements (client only)")
    parser.add_argument("--throughput-duration", type=int, default=10, help="Throughput test duration in seconds (client only)")
    
    args = parser.parse_args()
    
    if args.mode == "client" and args.host == "0.0.0.0":
        print("❌ Error: --host is required for client mode")
        print("   Example: python real-network-benchmark.py client --host 192.168.1.100")
        sys.exit(1)
    
    benchmark = NyxNetworkBenchmark(args.host, args.port)
    
    if args.mode == "server":
        benchmark.run_server()
    else:
        benchmark.run_client(args.latency_iterations, args.throughput_duration)

if __name__ == "__main__":
    main()
