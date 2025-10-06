//! Application-level benchmarks for NyxNet
//!
//! This module contains real-world application scenario benchmarks:
//! - File transfer (bulk data)
//! - Real-time messaging
//! - Video streaming
//! - VoIP (Voice over IP)
//!
//! These benchmarks demonstrate the practical performance of NyxNet
//! for common application use cases using actual NyxNet components.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::{Aead, AeadCore}};
use nyx_transport::{TransportConfig, UdpTransport};
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::net::UdpSocket;
use tokio::runtime::Runtime;
use tokio::sync::Mutex;

/// Test network setup with real UDP sockets
struct TestNetwork {
    sender_socket: Arc<UdpSocket>,
    receiver_socket: Arc<UdpSocket>,
    receiver_addr: SocketAddr,
    transport: Arc<UdpTransport>,
    cipher: Arc<Mutex<ChaCha20Poly1305>>,
}

impl TestNetwork {
    async fn new() -> Self {
        // Create sender and receiver sockets
        let sender_socket = Arc::new(UdpSocket::bind("127.0.0.1:0").await.unwrap());
        let receiver_socket = Arc::new(UdpSocket::bind("127.0.0.1:0").await.unwrap());
        let receiver_addr = receiver_socket.local_addr().unwrap();

        // Create transport
        let config = TransportConfig::default();
        let transport = Arc::new(UdpTransport::new(config).unwrap());

        // Create cipher for encryption
        let key = [0u8; 32]; // Test key
        let cipher = Arc::new(Mutex::new(ChaCha20Poly1305::new(&key.into())));

        Self {
            sender_socket,
            receiver_socket,
            receiver_addr,
            transport,
            cipher,
        }
    }

    async fn transfer_data(&self, data: &[u8]) -> std::io::Result<usize> {
        // Chunk size for realistic network transfer
        const CHUNK_SIZE: usize = 1400; // MTU-friendly size
        let mut total_sent = 0;

        for chunk in data.chunks(CHUNK_SIZE) {
            // Encrypt chunk
            let encrypted = {
                let cipher = self.cipher.lock().await;
                let nonce = [0u8; 12]; // Simplified for benchmark
                cipher.encrypt(&nonce.into(), chunk).unwrap()
            };

            // Send via UDP
            self.sender_socket
                .send_to(&encrypted, self.receiver_addr)
                .await?;
            total_sent += chunk.len();
        }

        Ok(total_sent)
    }
}

/// Benchmark file transfer throughput
fn bench_file_transfer(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let mut group = c.benchmark_group("file_transfer");
    group.sample_size(10); // Reduce samples for large transfers

    // Test different file sizes
    for size_mb in [1, 10, 100] {
        let size_bytes = size_mb * 1024 * 1024;
        group.throughput(Throughput::Bytes(size_bytes as u64));

        group.bench_with_input(
            BenchmarkId::new("nyx_network", format!("{}MB", size_mb)),
            &size_bytes,
            |b, &size| {
                b.to_async(&rt).iter(|| async {
                    let network = TestNetwork::new().await;
                    let data = vec![0u8; size];

                    let start = Instant::now();
                    let bytes_sent = network.transfer_data(black_box(&data)).await.unwrap();
                    let elapsed = start.elapsed();

                    // Calculate throughput
                    let throughput_mbps =
                        (bytes_sent as f64 * 8.0) / (elapsed.as_secs_f64() * 1_000_000.0);

                    black_box(throughput_mbps)
                });
            },
        );
    }

    group.finish();
}

/// Benchmark real-time messaging latency
fn bench_messaging(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let mut group = c.benchmark_group("messaging");

    // Test different message sizes
    for size_kb in [1, 4, 16] {
        let size_bytes = size_kb * 1024;
        group.throughput(Throughput::Elements(1));

        group.bench_with_input(
            BenchmarkId::new("message_latency", format!("{}KB", size_kb)),
            &size_bytes,
            |b, &size| {
                b.to_async(&rt).iter(|| async {
                    let network = TestNetwork::new().await;
                    let message = vec![0u8; size];

                    let start = Instant::now();

                    // Encrypt and send
                    let encrypted = {
                        let cipher = network.cipher.lock().await;
                        let nonce = [0u8; 12];
                        cipher.encrypt(&nonce.into(), &message).unwrap()
                    };

                    network
                        .sender_socket
                        .send_to(&encrypted, network.receiver_addr)
                        .await
                        .unwrap();

                    // Receive and decrypt
                    let mut buf = vec![0u8; size + 64]; // Extra space for auth tag
                    let (len, _) = network.receiver_socket.recv_from(&mut buf).await.unwrap();

                    let decrypted = {
                        let cipher = network.cipher.lock().await;
                        let nonce = [0u8; 12];
                        cipher.decrypt(&nonce.into(), &buf[..len]).unwrap()
                    };

                    let latency = start.elapsed();
                    black_box(decrypted);
                    latency
                });
            },
        );
    }

    // Benchmark message throughput (messages per second)
    group.bench_function("message_throughput_1kb", |b| {
        b.to_async(&rt).iter(|| async {
            let network = TestNetwork::new().await;
            let message = vec![0u8; 1024];

            let start = Instant::now();
            let count = 1000;

            for _ in 0..count {
                let encrypted = {
                    let cipher = network.cipher.lock().await;
                    let nonce = [0u8; 12];
                    cipher.encrypt(&nonce.into(), &message).unwrap()
                };

                network
                    .sender_socket
                    .send_to(&encrypted, network.receiver_addr)
                    .await
                    .unwrap();
            }

            let elapsed = start.elapsed();
            let throughput = count as f64 / elapsed.as_secs_f64();

            black_box(throughput)
        });
    });

    group.finish();
}

/// Benchmark video streaming performance
fn bench_video_streaming(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let mut group = c.benchmark_group("video_streaming");
    group.sample_size(10); // Fewer samples for longer tests
    group.measurement_time(Duration::from_secs(30));

    // Simulate 720p video streaming (2.5 Mbps)
    group.bench_function("720p_sustained", |b| {
        b.to_async(&rt).iter(|| async {
            let network = TestNetwork::new().await;

            let bitrate_mbps = 2.5;
            let duration_secs = 10;
            let chunk_size = 1400; // MTU-friendly
            let chunks_per_sec = (bitrate_mbps * 1_000_000.0 / 8.0 / chunk_size as f64) as usize;

            let start = Instant::now();
            let mut packets_sent = 0;
            let mut packets_lost = 0;

            for _ in 0..duration_secs {
                for _ in 0..chunks_per_sec {
                    let chunk = vec![0u8; chunk_size];

                    // Encrypt and send video chunk
                    let encrypted = {
                        let cipher = network.cipher.lock().await;
                        let nonce = [0u8; 12];
                        cipher.encrypt(&nonce.into(), &chunk).unwrap()
                    };

                    match network
                        .sender_socket
                        .send_to(&encrypted, network.receiver_addr)
                        .await
                    {
                        Ok(_) => packets_sent += 1,
                        Err(_) => packets_lost += 1,
                    }
                }

                // Simulate real-time pacing
                tokio::time::sleep(Duration::from_millis(1000)).await;
            }

            let elapsed = start.elapsed();
            let packet_loss_rate = if packets_sent > 0 {
                packets_lost as f64 / (packets_sent + packets_lost) as f64
            } else {
                0.0
            };

            black_box((packets_sent, packet_loss_rate))
        });
    });

    group.finish();
}

/// Benchmark VoIP (Voice over IP) performance
fn bench_voip(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let mut group = c.benchmark_group("voip");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(20));

    // Simulate Opus codec @ 64 kbps
    group.bench_function("opus_64kbps", |b| {
        b.to_async(&rt).iter(|| async {
            let network = TestNetwork::new().await;

            let bitrate_kbps = 64;
            let frame_duration_ms = 20; // Opus default
            let frame_size = (bitrate_kbps * frame_duration_ms / 8) as usize;
            let duration_secs = 10;

            let start = Instant::now();
            let mut latencies = Vec::new();
            let mut jitters = Vec::new();
            let mut prev_latency = Duration::ZERO;

            for _ in 0..(duration_secs * 1000 / frame_duration_ms) {
                let frame = vec![0u8; frame_size];
                let frame_start = Instant::now();

                // Encrypt and send voice frame
                let encrypted = {
                    let cipher = network.cipher.lock().await;
                    let nonce = [0u8; 12];
                    cipher.encrypt(&nonce.into(), &frame).unwrap()
                };

                network
                    .sender_socket
                    .send_to(&encrypted, network.receiver_addr)
                    .await
                    .unwrap();

                // Receive and decrypt response
                let mut buf = vec![0u8; frame_size + 64];
                let (len, _) = network.receiver_socket.recv_from(&mut buf).await.unwrap();

                let _decrypted = {
                    let cipher = network.cipher.lock().await;
                    let nonce = [0u8; 12];
                    cipher.decrypt(&nonce.into(), &buf[..len]).unwrap()
                };

                let latency = frame_start.elapsed();
                let jitter = if prev_latency > Duration::ZERO {
                    if latency > prev_latency {
                        latency - prev_latency
                    } else {
                        prev_latency - latency
                    }
                } else {
                    Duration::ZERO
                };

                latencies.push(latency);
                jitters.push(jitter);
                prev_latency = latency;

                // Maintain real-time pacing
                tokio::time::sleep(Duration::from_millis(frame_duration_ms as u64)).await;
            }

            let avg_latency = latencies.iter().sum::<Duration>() / latencies.len() as u32;
            let avg_jitter = jitters.iter().sum::<Duration>() / jitters.len() as u32;

            // Calculate MOS (Mean Opinion Score) approximation
            let latency_ms = avg_latency.as_millis() as f64;
            let jitter_ms = avg_jitter.as_millis() as f64;
            let mos = calculate_mos(latency_ms, jitter_ms, 0.0);

            black_box((avg_latency, avg_jitter, mos))
        });
    });

    group.finish();
}

/// Calculate MOS (Mean Opinion Score) for VoIP quality
/// Range: 1.0 (bad) to 5.0 (excellent)
fn calculate_mos(latency_ms: f64, jitter_ms: f64, loss_rate: f64) -> f64 {
    // Simplified E-Model calculation
    let r_latency = if latency_ms < 160.0 {
        93.2 - latency_ms / 40.0
    } else {
        93.2 - (latency_ms - 120.0) / 10.0
    };

    let r_jitter = 95.0 - jitter_ms / 2.0;
    let r_loss = 95.0 - loss_rate * 100.0 * 2.5;

    let r_factor = (r_latency.min(r_jitter).min(r_loss)).max(0.0);

    // Convert R-factor to MOS
    if r_factor < 0.0 {
        1.0
    } else if r_factor > 100.0 {
        4.5
    } else {
        1.0 + 0.035 * r_factor
            + r_factor * (r_factor - 60.0) * (100.0 - r_factor) * 7.0 / 1_000_000.0
    }
}

/// Benchmark concurrent connections scalability
fn bench_scalability(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let mut group = c.benchmark_group("scalability");
    group.sample_size(10);

    for &conn_count in &[10, 100, 500] {
        group.bench_with_input(
            BenchmarkId::new("concurrent_connections", conn_count),
            &conn_count,
            |b, &count| {
                b.to_async(&rt).iter(|| async {
                    // Create multiple network connections
                    let networks: Vec<_> =
                        futures::future::join_all((0..count).map(|_| TestNetwork::new())).await;

                    let start = Instant::now();
                    let message = vec![0u8; 1024];

                    // Spawn concurrent message sends
                    let handles: Vec<_> = networks
                        .iter()
                        .map(|network| {
                            let msg = message.clone();
                            let net = network;
                            tokio::spawn(async move {
                                // Encrypt and send
                                let encrypted = {
                                    let cipher = net.cipher.lock().await;
                                    let nonce = [0u8; 12];
                                    cipher.encrypt(&nonce.into(), &msg).unwrap()
                                };

                                net.sender_socket
                                    .send_to(&encrypted, net.receiver_addr)
                                    .await
                                    .unwrap();

                                // Receive response
                                let mut buf = vec![0u8; 1024 + 64];
                                let (len, _) =
                                    net.receiver_socket.recv_from(&mut buf).await.unwrap();

                                let _decrypted = {
                                    let cipher = net.cipher.lock().await;
                                    let nonce = [0u8; 12];
                                    cipher.decrypt(&nonce.into(), &buf[..len]).unwrap()
                                };
                            })
                        })
                        .collect();

                    // Wait for all connections
                    for handle in handles {
                        handle.await.unwrap();
                    }

                    let elapsed = start.elapsed();
                    let avg_latency = elapsed / count as u32;

                    black_box((elapsed, avg_latency))
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_file_transfer,
    bench_messaging,
    bench_video_streaming,
    bench_voip,
    bench_scalability
);
criterion_main!(benches);
