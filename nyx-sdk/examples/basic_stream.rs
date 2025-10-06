// Example: Basic stream usage demonstrating send/receive operations
//
// This example shows:
// - Creating a pair of connected streams
// - Sending and receiving data
// - Checking stream statistics
// - Proper resource cleanup

use bytes::Bytes;
use nyx_sdk::{NyxStream, Result};

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== Basic Stream Example ===\n");

    // Create a pair of connected streams
    let (mut sender, mut receiver) = NyxStream::pair(4096);
    println!("Created stream pair");

    // Send some messages
    let messages = vec!["Hello", "from", "Nyx", "SDK"];

    for msg in &messages {
        sender.send(Bytes::from(*msg)).await?;
        println!("Sent: {}", msg);
    }

    // Receive messages
    println!("\nReceiving messages:");
    for _ in 0..messages.len() {
        if let Some(data) = receiver.recv().await? {
            let text = String::from_utf8_lossy(&data);
            println!("Received: {}", text);
        }
    }

    // Check statistics
    println!("\n=== Sender Statistics ===");
    let sender_stats = sender.stats();
    println!("Bytes sent: {}", sender_stats.bytes_sent);
    println!("Messages sent: {}", sender_stats.messages_sent);

    println!("\n=== Receiver Statistics ===");
    let receiver_stats = receiver.stats();
    println!("Bytes received: {}", receiver_stats.bytes_received);
    println!("Messages received: {}", receiver_stats.messages_received);

    // Check uptime
    if let Some(uptime) = sender.uptime() {
        println!("\nStream uptime: {:?}", uptime);
    }

    // Close streams properly
    sender.close().await?;
    receiver.close().await?;
    println!("\nStreams closed successfully");

    Ok(())
}
