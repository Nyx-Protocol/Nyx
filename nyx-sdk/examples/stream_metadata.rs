// Example: Stream metadata and monitoring
//
// This example demonstrates:
// - Setting and retrieving stream metadata
// - Monitoring stream statistics
// - Tracking stream health
// - Custom metadata management

use bytes::Bytes;
use nyx_sdk::{NyxStream, Result};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== Stream Metadata and Monitoring Example ===\n");

    // Create streams
    let (mut sender, mut receiver) = NyxStream::pair(4096);

    // Set metadata
    println!("Setting stream metadata...");
    sender.set_target("example.com:443").await;
    sender.add_user_data("protocol", "https").await;
    sender.add_user_data("connection_id", "conn-12345").await;

    receiver.set_target("localhost:8080").await;
    receiver.add_user_data("role", "receiver").await;
    receiver.add_user_data("buffer_size", "4096").await;

    // Display initial metadata
    display_metadata(&sender, "Sender").await;
    display_metadata(&receiver, "Receiver").await;

    // Perform some operations
    println!("\n=== Performing Stream Operations ===");
    for i in 0..10 {
        let message = format!("Message {}", i + 1);
        sender.send(Bytes::from(message.clone())).await?;

        if let Some(data) = receiver.recv().await? {
            let text = String::from_utf8_lossy(&data);
            println!("Sent and received: {}", text);
        }

        sleep(Duration::from_millis(100)).await;
    }

    // Monitor stream statistics
    println!("\n=== Stream Statistics ===");
    monitor_stream(&sender, "Sender");
    monitor_stream(&receiver, "Receiver");

    // Check stream health
    println!("\n=== Stream Health Check ===");
    check_stream_health(&sender, "Sender");
    check_stream_health(&receiver, "Receiver");

    // Wait a bit to demonstrate idle time
    println!("\nWaiting 2 seconds...");
    sleep(Duration::from_secs(2)).await;

    // Check idle time
    println!("\n=== Idle Time Check ===");
    if let Some(idle) = sender.idle_time() {
        println!("Sender idle for: {:?}", idle);
    }
    if let Some(idle) = receiver.idle_time() {
        println!("Receiver idle for: {:?}", idle);
    }

    // Clean up
    sender.close().await?;
    receiver.close().await?;

    Ok(())
}

async fn display_metadata(stream: &NyxStream, name: &str) {
    let metadata = stream.metadata().await;
    println!("\n{} Metadata:", name);
    println!("  Stream ID: {}", metadata.stream_id);
    println!("  Protocol Version: {}", metadata.protocol_version);
    if let Some(target) = &metadata.target {
        println!("  Target: {}", target);
    }
    println!("  User Data:");
    for (key, value) in &metadata.user_data {
        println!("    {}: {}", key, value);
    }
}

fn monitor_stream(stream: &NyxStream, name: &str) {
    let stats = stream.stats();
    println!("\n{} Statistics:", name);
    println!("  Bytes sent: {}", stats.bytes_sent);
    println!("  Bytes received: {}", stats.bytes_received);
    println!("  Messages sent: {}", stats.messages_sent);
    println!("  Messages received: {}", stats.messages_received);
    println!("  Errors: {}", stats.errors);

    if let Some(uptime) = stream.uptime() {
        println!("  Uptime: {:?}", uptime);
    }

    if let Some(last_activity) = stream.idle_time() {
        println!("  Time since last activity: {:?}", last_activity);
    }
}

fn check_stream_health(stream: &NyxStream, name: &str) {
    let stats = stream.stats();

    println!("\n{} Health:", name);

    // Check for errors
    if stats.errors > 0 {
        println!("  ⚠ Warning: {} errors detected", stats.errors);
    } else {
        println!("  ✓ No errors");
    }

    // Check if stream is closed
    if stream.is_closed() {
        println!("  ✗ Stream is closed");
    } else {
        println!("  ✓ Stream is active");
    }

    // Check idle time
    if let Some(idle) = stream.idle_time() {
        if idle > Duration::from_secs(60) {
            println!("  ⚠ Warning: Stream idle for {:?}", idle);
        } else {
            println!("  ✓ Stream activity is recent");
        }
    }

    // Check message throughput
    let total_messages = stats.messages_sent + stats.messages_received;
    if total_messages == 0 {
        println!("  ⚠ Warning: No messages sent or received");
    } else {
        println!("  ✓ Total messages: {}", total_messages);
    }
}
