//! gRPC Client Usage Example
//!
//! Demonstrates common Nyx daemon control operations via gRPC API:
//! - Connecting to daemon
//! - Getting node information
//! - Opening and managing streams
//! - Subscribing to events
//! - Managing configuration
//!
//! Run with:
//! ```bash
//! # Start daemon first (configure gRPC in nyx.toml)
//! cargo run --bin nyx-daemon
//!
//! # In another terminal
//! cargo run --package nyx-sdk --example grpc_client_example
//! ```
//!
//! Note: Requires daemon with gRPC enabled in nyx.toml:
//! ```toml
//! [daemon]
//! grpc_addr = "127.0.0.1:50051"
//! enable_grpc = true
//! ```

use nyx_sdk::grpc_client::{GrpcClientConfig, GrpcClientError, NyxGrpcClient};
use std::time::Duration;
use tokio_stream::StreamExt;
use tracing::{error, info};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize logging
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();

    info!("Connecting to Nyx daemon...");

    // Create client configuration
    let daemon_addr =
        std::env::var("NYX_GRPC_ADDR").unwrap_or_else(|_| "http://127.0.0.1:50051".to_string());

    let config = GrpcClientConfig {
        server_address: daemon_addr.clone(),
        connect_timeout: Duration::from_secs(10),
        request_timeout: Duration::from_secs(30),
        ..Default::default()
    };

    // Connect to daemon
    let mut client = match NyxGrpcClient::with_config(config).await {
        Ok(c) => c,
        Err(e) => {
            error!("Failed to connect to daemon at {}: {}", daemon_addr, e);
            error!("Make sure the daemon is running with gRPC enabled");
            return Err(e.into());
        }
    };

    info!("Connected successfully!");

    // Example 1: Get node information
    info!("\n=== Example 1: Get Node Info ===");
    match client.get_node_info().await {
        Ok(info) => {
            println!("Node ID: {}", info.node_id);
            println!("Version: {}", info.version);
            println!("Uptime: {} seconds", info.uptime_sec);
            println!("Active streams: {}", info.active_streams);
            println!("Connected peers: {}", info.connected_peers);
            println!(
                "Traffic - In: {} bytes, Out: {} bytes",
                info.bytes_in, info.bytes_out
            );

            if let Some(perf) = info.performance {
                println!("Performance:");
                println!("  Avg latency: {:.2} ms", perf.avg_latency_ms);
                println!("  Packet loss: {:.2}%", perf.packet_loss_rate * 100.0);
                println!("  CPU usage: {:.1}%", perf.cpu_usage * 100.0);
            }
        }
        Err(e) => error!("Failed to get info: {}", e),
    }

    // Example 2: Health check
    info!("\n=== Example 2: Health Check ===");
    match client.get_health(true).await {
        Ok(health) => {
            println!("Health status: {}", health.status);
            println!("Checks: {} components checked", health.checks.len());
            for check in &health.checks {
                println!(
                    "  - {}: {} ({}ms)",
                    check.name, check.status, check.response_time_ms
                );
            }
        }
        Err(e) => error!("Health check failed: {}", e),
    }

    // Example 3: Open stream (requires peer node ID)
    info!("\n=== Example 3: Stream Management ===");
    let stream_name = "example_stream";
    let target_address = "example.peer.node:8080";

    match client
        .open_stream(stream_name.to_string(), target_address.to_string(), None)
        .await
    {
        Ok(stream_resp) => {
            println!("Stream opened successfully!");
            println!("  Stream ID: {}", stream_resp.stream_id);
            println!("  Status: {}", stream_resp.status);
            println!("  Target: {}", stream_resp.target_address);

            let stream_id = stream_resp.stream_id;

            // Send data on stream
            info!("Sending data on stream {}...", stream_id);
            match client
                .send_data(stream_id.to_string(), b"Hello, Nyx!".to_vec())
                .await
            {
                Ok(resp) => {
                    println!(
                        "Data sent: {} bytes, Success: {}",
                        resp.bytes_sent, resp.success
                    );
                    if !resp.error.is_empty() {
                        println!("  Error: {}", resp.error);
                    }
                }
                Err(e) => error!("Send failed: {}", e),
            }

            // Get stream stats
            match client.get_stream_stats(stream_id).await {
                Ok(stats) => {
                    println!("Stream stats:");
                    println!("  State: {}", stats.state);
                    println!(
                        "  Bytes TX: {}, RX: {}",
                        stats.bytes_sent, stats.bytes_received
                    );
                    println!(
                        "  Packets TX: {}, RX: {}",
                        stats.packets_sent, stats.packets_received
                    );
                    println!(
                        "  RTT: avg={:.2}ms, min={:.2}ms, max={:.2}ms",
                        stats.avg_rtt_ms, stats.min_rtt_ms, stats.max_rtt_ms
                    );
                    println!("  Bandwidth: {:.2} Mbps", stats.bandwidth_mbps);
                    println!("  Packet loss: {:.2}%", stats.packet_loss_rate * 100.0);
                }
                Err(e) => error!("Failed to get stats: {}", e),
            }

            // Close stream
            info!("Closing stream {}...", stream_id);
            match client.close_stream(stream_id).await {
                Ok(_) => println!("Stream closed successfully"),
                Err(e) => error!("Close failed: {}", e),
            }
        }
        Err(GrpcClientError::NotFound(_)) => {
            println!("Note: Stream opening requires a valid peer node ID.");
            println!(
                "This example uses a placeholder. In production, get peer IDs via GetPeers()."
            );
        }
        Err(e) => error!("Failed to open stream: {}", e),
    }

    // Example 4: List streams
    info!("\n=== Example 4: List All Streams ===");
    match client.list_streams().await {
        Ok(mut streams) => {
            let mut count = 0;
            while let Some(result) = streams.next().await {
                match result {
                    Ok(stream) => {
                        count += 1;
                        println!(
                            "Stream {}: ID={}, State={}, TX={} bytes, RX={} bytes",
                            count,
                            stream.stream_id,
                            stream.state,
                            stream.bytes_sent,
                            stream.bytes_received
                        );
                    }
                    Err(e) => error!("Stream error: {}", e),
                }
            }
            if count == 0 {
                println!("No active streams");
            } else {
                println!("Total streams: {}", count);
            }
        }
        Err(e) => error!("Failed to list streams: {}", e),
    }

    // Example 5: Subscribe to events (async task)
    info!("\n=== Example 5: Event Subscription ===");
    println!("Subscribing to daemon events for 5 seconds...");

    use nyx_sdk::grpc_proto::EventFilter;
    let event_filter = EventFilter {
        types: vec![
            "connection".to_string(),
            "stream".to_string(),
            "error".to_string(),
        ],
        stream_ids: vec![],
        severity: "info".to_string(),
    };

    match client.subscribe_events(event_filter).await {
        Ok(mut events) => {
            let event_task = tokio::spawn(async move {
                let mut event_count = 0;
                while let Some(result) = events.next().await {
                    match result {
                        Ok(event) => {
                            event_count += 1;
                            println!(
                                "Event #{}: type={}, detail={}, severity={}",
                                event_count, event.r#type, event.detail, event.severity
                            );
                            if !event.attributes.is_empty() {
                                println!("  Attributes: {:?}", event.attributes);
                            }
                        }
                        Err(e) => {
                            error!("Event stream error: {}", e);
                            break;
                        }
                    }
                }
                if event_count == 0 {
                    println!("No events received (daemon idle)");
                }
            });

            // Wait 5 seconds then cancel
            tokio::time::sleep(Duration::from_secs(5)).await;
            event_task.abort();
        }
        Err(e) => error!("Failed to subscribe to events: {}", e),
    }

    // Example 6: Configuration management
    info!("\n=== Example 6: Configuration Management ===");

    // Update specific config keys
    let mut updates = std::collections::HashMap::new();
    updates.insert("max_paths".to_string(), "8".to_string());
    updates.insert("cover_traffic_ratio".to_string(), "0.3".to_string());

    match client.update_config(updates).await {
        Ok(resp) => {
            println!("Config update result:");
            println!("  Success: {}", resp.success);
            println!("  Message: {}", resp.message);
            if !resp.validation_errors.is_empty() {
                println!("  Validation errors:");
                for err in &resp.validation_errors {
                    println!("    - {}", err);
                }
            }
        }
        Err(e) => error!("Config update failed: {}", e),
    }

    // Example 7: Network topology
    info!("\n=== Example 7: Network Topology ===");
    match client.get_topology().await {
        Ok(topo) => {
            println!("Network topology:");
            println!("  Total known nodes: {}", topo.total_nodes_known);
            println!("  Reachable nodes: {}", topo.reachable_nodes);
            println!("  Current region: {}", topo.current_region);
            println!("  Available regions: {:?}", topo.available_regions);
            println!("  Connected peers: {}", topo.peers.len());
            println!("  Active paths: {}", topo.paths.len());
        }
        Err(e) => error!("Failed to get topology: {}", e),
    }

    // Example 8: Get peers (streaming)
    info!("\n=== Example 8: Peer List ===");
    match client.get_peers().await {
        Ok(mut peers) => {
            let mut count = 0;
            while let Some(result) = peers.next().await {
                match result {
                    Ok(peer) => {
                        count += 1;
                        println!(
                            "Peer {}: ID={}, Addr={}, Latency={:.2}ms, Status={}",
                            count, peer.node_id, peer.address, peer.latency_ms, peer.status
                        );
                    }
                    Err(e) => error!("Peer error: {}", e),
                }
            }
            if count == 0 {
                println!("No connected peers");
            } else {
                println!("Total peers: {}", count);
            }
        }
        Err(e) => error!("Failed to get peers: {}", e),
    }

    info!("\n=== Example Complete ===");
    println!("All gRPC operations demonstrated successfully!");
    println!("\nFor more details, see:");
    println!("  - API documentation: docs/api.md");
    println!("  - Protobuf definitions: nyx-daemon/proto/control.proto");
    println!("  - SDK source: nyx-sdk/src/grpc_client.rs");

    Ok(())
}
