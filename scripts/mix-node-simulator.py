#!/usr/bin/env python3
"""
Simplified NyxNet Mix Node Simulator
実際のNyxNetプロトコルの簡易実装 (ベンチマーク用)
"""

import socket
import os
import sys
import threading
import time
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305

NODE_ID = os.environ.get('NODE_ID', 'unknown')
NODE_ROLE = os.environ.get('NODE_ROLE', 'intermediate')
NEXT_HOP = os.environ.get('NEXT_HOP', None)
LISTEN_PORT = int(os.environ.get('LISTEN_PORT', 9001))

KEY = ChaCha20Poly1305.generate_key()

def forward_packet(data: bytes, next_hop: str):
    """次のホップにパケットを転送"""
    if not next_hop:
        return b"RESPONSE:" + data  # Exit nodeは応答を返す
    
    host, port = next_hop.split(':')
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.settimeout(5.0)
    
    try:
        sock.sendto(data, (host, int(port)))
        response, _ = sock.recvfrom(65535)
        return response
    except Exception as e:
        print(f"[{NODE_ID}] Forward error: {e}")
        return None
    finally:
        sock.close()

def process_packet(data: bytes) -> bytes:
    """パケットを処理 (復号化、転送、暗号化)"""
    cipher = ChaCha20Poly1305(KEY)
    
    try:
        # 復号化
        nonce = data[:12]
        ciphertext = data[12:]
        plaintext = cipher.decrypt(nonce, ciphertext, None)
        
        # 次のホップに転送
        if NEXT_HOP and NODE_ROLE != 'exit':
            response = forward_packet(plaintext, NEXT_HOP)
        else:
            # Exit node: エコーバック
            response = b"RESPONSE:" + plaintext
        
        if response:
            # 応答を暗号化
            response_nonce = os.urandom(12)
            response_cipher = cipher.encrypt(response_nonce, response, None)
            return response_nonce + response_cipher
        
    except Exception as e:
        print(f"[{NODE_ID}] Processing error: {e}")
    
    return None

def run_server():
    """Mix nodeサーバーを起動"""
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind(('0.0.0.0', LISTEN_PORT))
    
    print(f"🚀 [{NODE_ID}] Mix Node started")
    print(f"   Role: {NODE_ROLE}")
    print(f"   Listening on: 0.0.0.0:{LISTEN_PORT}")
    if NEXT_HOP:
        print(f"   Next hop: {NEXT_HOP}")
    print("")
    
    packet_count = 0
    
    try:
        while True:
            data, addr = sock.recvfrom(65535)
            packet_count += 1
            
            # パケット処理
            response = process_packet(data)
            
            if response:
                sock.sendto(response, addr)
            
            if packet_count % 100 == 0:
                print(f"[{NODE_ID}] Processed {packet_count} packets")
                
    except KeyboardInterrupt:
        print(f"\n[{NODE_ID}] Shutting down...")
    finally:
        sock.close()

if __name__ == "__main__":
    print(f"=== NyxNet Mix Node Simulator ===")
    run_server()
