#!/usr/bin/env python3
"""
Simulated Multi-hop Network Benchmark
Docker不要で実行できる簡易版マルチホップベンチマーク
ネットワーク遅延をsleep()でシミュレート
"""

import socket
import time
import json
import statistics
import threading
import os
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305
from typing import List

# シナリオ別の遅延設定
DELAY_SCENARIOS = {
    "no-delay": {
        "name": "No Delay (Baseline)",
        "per_hop_ms": 0,
        "jitter_ms": 0
    },
    "lan": {
        "name": "LAN (Local Network)",
        "per_hop_ms": 2,
        "jitter_ms": 1
    },
    "regional": {
        "name": "Regional (Same Country)",
        "per_hop_ms": 25,
        "jitter_ms": 10
    },
    "global": {
        "name": "Global (International)",
        "per_hop_ms": 100,
        "jitter_ms": 30
    }
}

# 4つのMix node用の鍵
KEYS = [ChaCha20Poly1305.generate_key() for _ in range(4)]

class SimulatedMixNode:
    """シミュレートされたMix Node"""
    
    def __init__(self, node_id: int, next_node=None, delay_ms: float = 0, jitter_ms: float = 0):
        self.node_id = node_id
        self.next_node = next_node
        self.delay_ms = delay_ms
        self.jitter_ms = jitter_ms
        self.cipher = ChaCha20Poly1305(KEYS[node_id])
        self.port = 19000 + node_id
        self.sock = None
        self.running = False
        
    def start(self):
        """ノードを起動"""
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.bind(('127.0.0.1', self.port))
        self.sock.settimeout(0.1)
        self.running = True
        
        thread = threading.Thread(target=self._run, daemon=True)
        thread.start()
        
    def _run(self):
        """ノードのメインループ"""
        while self.running:
            try:
                data, addr = self.sock.recvfrom(65535)
                
                # ネットワーク遅延をシミュレート
                if self.delay_ms > 0:
                    import random
                    delay = (self.delay_ms + random.uniform(-self.jitter_ms, self.jitter_ms)) / 1000
                    time.sleep(max(0, delay))
                
                # 復号化
                nonce = data[:12]
                ciphertext = data[12:]
                plaintext = self.cipher.decrypt(nonce, ciphertext, None)
                
                # 次のホップに転送 or エコーバック
                if self.next_node:
                    # 次のホップに送信して応答を待つ
                    response_plaintext = self.next_node.forward(plaintext)
                    if response_plaintext:
                        # 応答を暗号化して返す
                        response_nonce = os.urandom(12)
                        response_cipher = self.cipher.encrypt(response_nonce, response_plaintext, None)
                        self.sock.sendto(response_nonce + response_cipher, addr)
                else:
                    # Exit node: エコーバックする
                    response = plaintext
                    response_nonce = os.urandom(12)
                    response_cipher = self.cipher.encrypt(response_nonce, response, None)
                    self.sock.sendto(response_nonce + response_cipher, addr)
                    
            except socket.timeout:
                continue
            except Exception as e:
                pass
                
    def forward(self, data: bytes) -> bytes:
        """このノードにデータを転送して応答を待つ"""
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.settimeout(5.0)
        
        try:
            sock.sendto(data, ('127.0.0.1', self.port))
            response, _ = sock.recvfrom(65535)
            return response
        except Exception as e:
            return None
        finally:
            sock.close()
        
    def stop(self):
        """ノードを停止"""
        self.running = False
        if self.sock:
            self.sock.close()

def measure_with_scenario(scenario_name: str, iterations: int = 100, throughput_duration: int = 5):
    """指定されたシナリオでベンチマーク測定"""
    
    scenario = DELAY_SCENARIOS.get(scenario_name, DELAY_SCENARIOS["no-delay"])
    
    print(f"\n{'='*60}")
    print(f"Scenario: {scenario['name']}")
    print(f"Per-hop delay: {scenario['per_hop_ms']}ms ± {scenario['jitter_ms']}ms")
    print(f"Expected RTT (4 hops): {scenario['per_hop_ms'] * 8}ms - {(scenario['per_hop_ms'] + scenario['jitter_ms']) * 8}ms")
    print(f"{'='*60}\n")
    
    # Mix nodeを起動
    nodes = []
    for i in range(3, -1, -1):  # 逆順で作成 (Exit -> Entry)
        next_node = nodes[0] if nodes else None
        node = SimulatedMixNode(i, next_node, scenario['per_hop_ms'], scenario['jitter_ms'])
        nodes.insert(0, node)
    
    # すべてのノードを起動
    for node in nodes:
        node.start()
    
    time.sleep(0.5)  # ノードの起動を待つ
    
    entry_node = nodes[0]
    entry_port = entry_node.port
    
    # レイテンシ測定
    print(f"📡 Measuring latency (4-hop, {iterations} iterations)...")
    latencies = []
    message = b"PING" * 256  # 1KB
    
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.settimeout(10.0)
    
    for i in range(iterations):
        # 4層暗号化
        data = message
        for key in reversed(KEYS):
            cipher = ChaCha20Poly1305(key)
            nonce = os.urandom(12)
            encrypted = cipher.encrypt(nonce, data, None)
            data = nonce + encrypted
        
        start = time.perf_counter()
        sock.sendto(data, ('127.0.0.1', entry_port))
        
        try:
            response, _ = sock.recvfrom(65535)
            end = time.perf_counter()
            
            # 4層復号化
            data = response
            for key in KEYS:
                cipher = ChaCha20Poly1305(key)
                nonce = data[:12]
                encrypted = data[12:]
                data = cipher.decrypt(nonce, encrypted, None)
            
            latency_ms = (end - start) * 1000
            latencies.append(latency_ms)
            
            if (i + 1) % 20 == 0:
                print(f"   Progress: {i+1}/{iterations} - Current: {latency_ms:.2f}ms")
                
        except socket.timeout:
            print(f"   ⚠️  Timeout at iteration {i+1}")
            continue
        except Exception as e:
            print(f"   ❌ Error at iteration {i+1}: {e}")
            continue
    
    sock.close()
    
    if not latencies:
        print("❌ No successful measurements")
        for node in nodes:
            node.stop()
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
    print(f"\n📊 Measuring throughput (4-hop, {throughput_duration} seconds)...")
    message = b"X" * 4096  # 4KB
    bytes_sent = 0
    packets_sent = 0
    
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.settimeout(1.0)
    
    start_time = time.time()
    
    while time.time() - start_time < throughput_duration:
        # 4層暗号化
        data = message
        for key in reversed(KEYS):
            cipher = ChaCha20Poly1305(key)
            nonce = os.urandom(12)
            encrypted = cipher.encrypt(nonce, data, None)
            data = nonce + encrypted
        
        sock.sendto(data, ('127.0.0.1', entry_port))
        bytes_sent += len(data)
        packets_sent += 1
        
        if packets_sent % 100 == 0:
            try:
                sock.recvfrom(65535)
            except socket.timeout:
                pass
    
    elapsed = time.time() - start_time
    throughput_mbps = (bytes_sent * 8) / (elapsed * 1_000_000)
    throughput_mb_per_sec = throughput_mbps / 8
    
    print(f"   Throughput: {throughput_mb_per_sec:.2f} MB/s ({throughput_mbps:.2f} Mbps)")
    print(f"   Packets sent: {packets_sent}")
    
    sock.close()
    
    # ノードを停止
    for node in nodes:
        node.stop()
    
    # Torとの比較
    TOR_THROUGHPUT = 39.30
    TOR_LATENCY = 1224.38
    
    throughput_speedup = throughput_mb_per_sec / TOR_THROUGHPUT
    latency_improvement = TOR_LATENCY / avg_latency
    
    print(f"\n📊 Comparison with Tor:")
    print(f"   Throughput: NyxNet {throughput_mb_per_sec:.2f} MB/s vs Tor {TOR_THROUGHPUT:.2f} MB/s")
    print(f"   Speedup: {throughput_speedup:.2f}x")
    print(f"   Latency: NyxNet {avg_latency:.2f} ms vs Tor {TOR_LATENCY:.2f} ms")
    print(f"   Improvement: {latency_improvement:.2f}x")
    
    return {
        "measurement_type": f"Simulated 4-hop network - {scenario['name']}",
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        "scenario": scenario_name,
        "scenario_config": scenario,
        "hops": 4,
        "latency": {
            "average_ms": avg_latency,
            "median_ms": median_latency,
            "min_ms": min_latency,
            "max_ms": max_latency,
            "stdev_ms": stdev_latency,
            "successful_iterations": len(latencies),
            "total_iterations": iterations
        },
        "throughput": {
            "mbps": throughput_mbps,
            "mb_per_sec": throughput_mb_per_sec,
            "packets_sent": packets_sent,
            "duration_seconds": throughput_duration
        },
        "comparison": {
            "tor_throughput_mb_per_sec": TOR_THROUGHPUT,
            "tor_latency_ms": TOR_LATENCY,
            "throughput_speedup": throughput_speedup,
            "latency_improvement": latency_improvement
        }
    }

if __name__ == "__main__":
    print("=== NyxNet Multi-hop Benchmark (Simulated) ===")
    print("4-hop network with ChaCha20Poly1305 encryption")
    print("")
    
    results_all = {}
    
    for scenario in ["no-delay", "lan", "regional", "global"]:
        result = measure_with_scenario(scenario, iterations=100, throughput_duration=5)
        if result:
            results_all[scenario] = result
            
            # 個別に保存
            output_file = f"benchmarks/results/multihop_{scenario}_results.json"
            with open(output_file, 'w') as f:
                json.dump(result, f, indent=2)
            print(f"\n💾 Results saved to: {output_file}")
        
        time.sleep(1)  # シナリオ間で少し待機
    
    # すべての結果をまとめて保存
    if results_all:
        summary_file = "benchmarks/results/multihop_all_scenarios.json"
        with open(summary_file, 'w') as f:
            json.dump(results_all, f, indent=2)
        print(f"\n💾 Summary saved to: {summary_file}")
        
        print("\n" + "="*60)
        print("✅ All benchmarks completed!")
        print("="*60)
