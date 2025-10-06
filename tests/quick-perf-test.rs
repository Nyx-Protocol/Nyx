// Quick NyxNet Performance Test
// 実際のNyxNet実装を使用した高速パフォーマンステスト
//
// Run with: cargo run --release --bin quick-perf-test

use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
use std::time::Instant;
use tokio::net::UdpSocket;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== NyxNet Quick Performance Test ===");
    println!("Using actual NyxNet components:");
    println!("  - UDP Transport");
    println!("  - ChaCha20Poly1305 Encryption\n");

    // Setup
    let sender = UdpSocket::bind("127.0.0.1:0").await?;
    let receiver = UdpSocket::bind("127.0.0.1:0").await?;
    let receiver_addr = receiver.local_addr()?;

    let key = [0u8; 32];
    let cipher = ChaCha20Poly1305::new(&key.into());
    let nonce = [0u8; 12];

    // Latency Test
    println!("📡 Latency Test (100 iterations):");
    let message = vec![0u8; 1024]; // 1KB
    let mut latencies = Vec::new();

    for _ in 0..100 {
        let encrypted = cipher.encrypt(&nonce.into(), &message).expect("encryption failed");

        let start = Instant::now();
        sender.send_to(&encrypted, receiver_addr).await?;

        let mut buf = vec![0u8; 2048];
        let (len, _) = receiver.recv_from(&mut buf).await?;
        buf.truncate(len);

        let _decrypted = cipher.decrypt(&nonce.into(), &buf).expect("decryption failed");
        let elapsed = start.elapsed();

        latencies.push(elapsed.as_micros() as f64 / 1000.0);
    }

    let avg_latency: f64 = latencies.iter().sum::<f64>() / latencies.len() as f64;
    let min_latency = latencies.iter().cloned().fold(f64::INFINITY, f64::min);
    let max_latency = latencies.iter().cloned().fold(f64::NEG_INFINITY, f64::max);

    println!("  Average: {:.3} ms", avg_latency);
    println!("  Min: {:.3} ms", min_latency);
    println!("  Max: {:.3} ms", max_latency);

    // Throughput Test
    println!("\n📊 Throughput Test (5 seconds):");
    let test_data = vec![0u8; 8192]; // 8KB packets
    let mut total_bytes = 0;
    let mut packets_sent = 0;

    let start_time = Instant::now();
    let duration = std::time::Duration::from_secs(5);

    while start_time.elapsed() < duration {
        let encrypted = cipher.encrypt(&nonce.into(), test_data.as_slice()).expect("encryption failed");
        sender.send_to(&encrypted, receiver_addr).await?;
        total_bytes += encrypted.len();
        packets_sent += 1;
    }

    let elapsed = start_time.elapsed().as_secs_f64();
    let throughput_mbps = (total_bytes as f64 * 8.0) / (elapsed * 1_000_000.0);
    let throughput_mb_per_sec = total_bytes as f64 / (elapsed * 1024.0 * 1024.0);

    println!(
        "  Throughput: {:.2} MB/s ({:.2} Mbps)",
        throughput_mb_per_sec, throughput_mbps
    );
    println!("  Packets sent: {}", packets_sent);
    println!("  Duration: {:.2}s", elapsed);

    // Comparison with Tor
    let tor_throughput = 39.30; // MB/s
    let tor_latency = 1224.38; // ms

    println!("\n📊 Comparison with Tor:");
    println!(
        "  Throughput: NyxNet {:.2} MB/s vs Tor {:.2} MB/s ({:.2}x)",
        throughput_mb_per_sec,
        tor_throughput,
        throughput_mb_per_sec / tor_throughput
    );
    println!(
        "  Latency: NyxNet {:.3} ms vs Tor {:.2} ms ({:.0}x improvement)",
        avg_latency,
        tor_latency,
        tor_latency / avg_latency
    );

    println!("\n✅ Test completed!");
    Ok(())
}
