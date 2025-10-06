#!/usr/bin/env python3
"""
Multi-process NyxNet simulation with actual UDP sockets and network delays
実際のUDPソケットを使ったマルチプロセス・マルチノード測定
"""

import socket
import time
import json
import multiprocessing as mp
from pathlib import Path
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305
import secrets
import struct

# Network delay simulation (ms)
NETWORK_DELAYS = {
    "lan": 5,      # 5ms LAN
    "regional": 25,  # 25ms regional
    "global": 75,    # 75ms global
}

class MixNode:
    """Mix node that performs actual encryption and UDP forwarding"""
    
    def __init__(self, node_id, listen_port, next_hop=None, delay_ms=0, shared_key=None):
        self.node_id = node_id
        self.listen_port = listen_port
        self.next_hop = next_hop  # (host, port)
        self.delay_ms = delay_ms
        # Use shared key for all nodes
        self.cipher = ChaCha20Poly1305(shared_key if shared_key else secrets.token_bytes(32))
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.bind(('127.0.0.1', listen_port))
        self.packets_processed = 0
        
    def run(self):
        """Run mix node server"""
        print(f"[Mix-{self.node_id}] Listening on port {self.listen_port}, delay={self.delay_ms}ms")
        
        while True:
            try:
                data, addr = self.sock.recvfrom(65535)
                
                # Simulate network delay
                if self.delay_ms > 0:
                    time.sleep(self.delay_ms / 1000.0)
                
                # Decrypt received data
                nonce = data[:12]
                ciphertext = data[12:]
                plaintext = self.cipher.decrypt(nonce, ciphertext, None)
                
                self.packets_processed += 1
                
                # Forward to next hop if exists
                if self.next_hop:
                    # Re-encrypt for next hop
                    new_nonce = secrets.token_bytes(12)
                    new_ciphertext = self.cipher.encrypt(new_nonce, plaintext, None)
                    self.sock.sendto(new_nonce + new_ciphertext, self.next_hop)
                else:
                    # Final destination - send ACK back
                    ack = b"ACK"
                    ack_nonce = secrets.token_bytes(12)
                    ack_encrypted = self.cipher.encrypt(ack_nonce, ack, None)
                    self.sock.sendto(ack_nonce + ack_encrypted, addr)
                    
            except KeyboardInterrupt:
                break
            except Exception as e:
                print(f"[Mix-{self.node_id}] Error: {e}")
                
        self.sock.close()

def run_mix_node(node_id, listen_port, next_hop, delay_ms, shared_key):
    """Process wrapper for mix node"""
    node = MixNode(node_id, listen_port, next_hop, delay_ms, shared_key)
    node.run()

def benchmark_multihop(scenario, num_requests=100):
    """Benchmark multi-hop network with actual UDP sockets"""
    
    print(f"\n{'='*80}")
    print(f"Scenario: {scenario.upper()}")
    print(f"Network delay: {NETWORK_DELAYS[scenario]}ms per hop")
    print(f"{'='*80}\n")
    
    # Port configuration
    ports = {
        'mix1': 10001,
        'mix2': 10002,
        'mix3': 10003,
    }
    
    delay_ms = NETWORK_DELAYS[scenario]
    
    # Shared encryption key for all nodes and client
    shared_key = secrets.token_bytes(32)
    
    # Start mix nodes as separate processes
    processes = []
    
    # Mix 3 (final destination)
    p3 = mp.Process(target=run_mix_node, args=(3, ports['mix3'], None, delay_ms, shared_key))
    p3.start()
    processes.append(p3)
    time.sleep(0.5)
    
    # Mix 2 -> Mix 3
    p2 = mp.Process(target=run_mix_node, args=(2, ports['mix2'], ('127.0.0.1', ports['mix3']), delay_ms, shared_key))
    p2.start()
    processes.append(p2)
    time.sleep(0.5)
    
    # Mix 1 -> Mix 2
    p1 = mp.Process(target=run_mix_node, args=(1, ports['mix1'], ('127.0.0.1', ports['mix2']), delay_ms, shared_key))
    p1.start()
    processes.append(p1)
    time.sleep(1)
    
    print("[Client] All mix nodes started\n")
    
    # Client setup
    client_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    client_sock.settimeout(5.0)
    cipher = ChaCha20Poly1305(shared_key)
    
    latencies = []
    successful = 0
    
    print(f"[Client] Sending {num_requests} requests through 3-hop network...\n")
    
    for i in range(num_requests):
        try:
            # Create message
            message = f"Request {i}".encode()
            
            # Encrypt
            nonce = secrets.token_bytes(12)
            ciphertext = cipher.encrypt(nonce, message, None)
            packet = nonce + ciphertext
            
            # Measure round-trip time
            start = time.perf_counter()
            
            # Send to Mix 1
            client_sock.sendto(packet, ('127.0.0.1', ports['mix1']))
            
            # Wait for response
            try:
                response, _ = client_sock.recvfrom(65535)
                end = time.perf_counter()
                
                latency_ms = (end - start) * 1000
                latencies.append(latency_ms)
                successful += 1
                
                if (i + 1) % 20 == 0:
                    avg_so_far = sum(latencies) / len(latencies)
                    print(f"  Progress: {i+1}/{num_requests} - Avg: {avg_so_far:.2f}ms")
                    
            except socket.timeout:
                print(f"  Request {i} timed out")
                
        except Exception as e:
            print(f"  Error on request {i}: {e}")
    
    client_sock.close()
    
    # Stop mix nodes
    print(f"\n[Client] Stopping mix nodes...")
    for p in processes:
        p.terminate()
        p.join(timeout=2)
        if p.is_alive():
            p.kill()
    
    # Calculate statistics
    if latencies:
        results = {
            "scenario": scenario,
            "network_delay_per_hop_ms": delay_ms,
            "total_hops": 3,
            "requests_sent": num_requests,
            "requests_successful": successful,
            "success_rate": successful / num_requests,
            "latency_ms": {
                "average": sum(latencies) / len(latencies),
                "min": min(latencies),
                "max": max(latencies),
                "median": sorted(latencies)[len(latencies)//2],
                "p95": sorted(latencies)[int(len(latencies) * 0.95)],
                "p99": sorted(latencies)[int(len(latencies) * 0.99)],
            },
            "raw_latencies": latencies
        }
    else:
        results = {
            "scenario": scenario,
            "error": "No successful requests"
        }
    
    return results

def main():
    print("="*80)
    print("REAL MULTI-HOP UDP NETWORK BENCHMARK")
    print("Using actual UDP sockets + ChaCha20Poly1305 encryption")
    print("3-hop network: Client -> Mix1 -> Mix2 -> Mix3 -> Client")
    print("="*80)
    
    all_results = {}
    
    for scenario in ["lan", "regional", "global"]:
        try:
            results = benchmark_multihop(scenario, num_requests=50)
            all_results[scenario] = results
            
            # Save intermediate results
            output_file = f"benchmarks/results/multihop_{scenario}_results.json"
            Path(output_file).parent.mkdir(parents=True, exist_ok=True)
            with open(output_file, 'w') as f:
                json.dump(results, f, indent=2)
            
            # Print summary
            if 'latency_ms' in results:
                print(f"\n{'='*80}")
                print(f"RESULTS - {scenario.upper()}")
                print(f"{'='*80}")
                print(f"Success Rate:   {results['success_rate']*100:.1f}%")
                print(f"Avg Latency:    {results['latency_ms']['average']:.2f}ms")
                print(f"Median Latency: {results['latency_ms']['median']:.2f}ms")
                print(f"P95 Latency:    {results['latency_ms']['p95']:.2f}ms")
                print(f"P99 Latency:    {results['latency_ms']['p99']:.2f}ms")
            
            time.sleep(2)  # Cool down between scenarios
            
        except Exception as e:
            print(f"\n❌ Scenario {scenario} failed: {e}")
            all_results[scenario] = {"error": str(e)}
    
    # Save final summary
    summary_file = "benchmarks/results/multihop_all_scenarios.json"
    with open(summary_file, 'w') as f:
        json.dump({
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "method": "real_udp_multihop_benchmark",
            "description": "Actual UDP sockets with ChaCha20Poly1305, simulated network delays",
            "results": all_results
        }, f, indent=2)
    
    print(f"\n{'='*80}")
    print(f"✅ All scenarios completed!")
    print(f"Results saved to: {summary_file}")
    print(f"{'='*80}")

if __name__ == "__main__":
    mp.set_start_method('spawn', force=True)
    main()
