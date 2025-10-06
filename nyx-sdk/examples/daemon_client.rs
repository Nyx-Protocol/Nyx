// Example: Daemon client operations
//
// This example demonstrates:
// - Connecting to the Nyx daemon
// - Getting daemon information
// - Configuration management
// - Error handling

use nyx_sdk::{DaemonClient, Result, SdkConfig};
use serde_json::json;

#[tokio::main]
async fn main() -> Result<()> {
    println!("=== Nyx Daemon Client Example ===\n");

    // Create configuration with custom timeout
    let config = SdkConfig::builder()
        .request_timeout_ms(15000)
        .auto_reconnect(true)
        .enable_logging(true)
        .build()?;

    println!("Configuration created");
    println!("Endpoint: {}", config.daemon_endpoint);
    println!("Timeout: {}ms", config.request_timeout_ms);

    // Create client with auto-discovered authentication token
    println!("\nConnecting to daemon...");
    let client = DaemonClient::new_with_auto_token(config).await;

    // Get daemon info
    match client.get_info().await {
        Ok(info) => {
            println!("\n=== Daemon Information ===");
            println!("{}", serde_json::to_string_pretty(&info)?);
        }
        Err(e) => {
            eprintln!("Failed to get daemon info: {}", e);
            println!("\nNote: Make sure the Nyx daemon is running");
            println!("  Unix: Check /tmp/nyx.sock");
            println!("  Windows: Check \\\\.\\pipe\\nyx-daemon");
            return Ok(());
        }
    }

    // List configuration versions
    match client.list_versions().await {
        Ok(versions) => {
            println!("\n=== Configuration Versions ===");
            println!("{}", serde_json::to_string_pretty(&versions)?);
        }
        Err(e) => {
            eprintln!("Failed to list versions: {}", e);
        }
    }

    // Create a configuration snapshot
    println!("\nCreating configuration snapshot...");
    match client
        .create_config_snapshot(Some("Example snapshot".to_string()))
        .await
    {
        Ok(snapshot) => {
            println!("Snapshot created:");
            println!("{}", serde_json::to_string_pretty(&snapshot)?);
        }
        Err(e) => {
            eprintln!("Failed to create snapshot: {}", e);
        }
    }

    // Update configuration (example)
    println!("\nUpdating configuration...");
    let mut settings = serde_json::Map::new();
    settings.insert("log_level".into(), json!("debug"));

    match client.update_config(settings).await {
        Ok(response) => {
            if response.success {
                println!("✓ Configuration updated successfully");
                println!("  Message: {}", response.message);
            } else {
                println!("✗ Configuration update failed");
                println!("  Message: {}", response.message);
                if !response.validation_errors.is_empty() {
                    println!("  Validation errors:");
                    for error in response.validation_errors {
                        println!("    - {}", error);
                    }
                }
            }
        }
        Err(e) => {
            eprintln!("Failed to update config: {}", e);
        }
    }

    // Reload configuration
    println!("\nReloading configuration...");
    match client.reload_config().await {
        Ok(result) => {
            println!("✓ Configuration reloaded");
            println!("{}", serde_json::to_string_pretty(&result)?);
        }
        Err(e) => {
            eprintln!("Failed to reload config: {}", e);
        }
    }

    // Get compliance report
    println!("\nGetting compliance report...");
    match client.get_compliance_report().await {
        Ok(report) => {
            println!("=== Compliance Report ===");
            println!("{}", serde_json::to_string_pretty(&report)?);
        }
        Err(e) => {
            eprintln!("Failed to get compliance report: {}", e);
        }
    }

    println!("\n=== Example completed ===");

    Ok(())
}
