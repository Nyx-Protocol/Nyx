// Example: Event subscription and handling
//
// This example demonstrates:
// - Subscribing to daemon events
// - Processing events asynchronously
// - Filtering specific event types
// - Graceful shutdown

use nyx_sdk::{DaemonClient, Result, SdkConfig};
use std::time::Duration;
use tokio::time::timeout;

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== Event Subscription Example ===\n");

    // Create configuration
    let config = SdkConfig::builder()
        .request_timeout_ms(30000)
        .build()?;

    // Create client
    let client = DaemonClient::new_with_auto_token(config).await;

    println!("Subscribing to daemon events...");
    println!("Press Ctrl+C to stop\n");

    // Subscribe to all events
    let mut events = match client.subscribe_events(None).await {
        Ok(rx) => rx,
        Err(e) => {
            eprintln!("Failed to subscribe to events: {}", e);
            println!("\nNote: Make sure the Nyx daemon is running");
            return Ok(());
        }
    };

    // Process events for 30 seconds or until interrupted
    let duration = Duration::from_secs(30);
    let result = timeout(duration, async {
        let mut event_count = 0;

        loop {
            match events.recv().await {
                Ok(event) => {
                    event_count += 1;
                    println!("[Event #{}]", event_count);
                    println!("  Type: {}", event.event_type);
                    println!("  Detail: {}", event.detail);
                    println!();

                    // Check for system events
                    if event.event_type == "system" {
                        if event.detail.contains("closed") {
                            println!("Event stream closed");
                            break;
                        }
                    }
                }
                Err(e) => {
                    eprintln!("Error receiving event: {}", e);
                    break;
                }
            }
        }

        println!("\nTotal events received: {}", event_count);
    })
    .await;

    match result {
        Ok(_) => println!("Event stream completed"),
        Err(_) => println!("Event monitoring timed out after 30 seconds"),
    }

    Ok(())
}
