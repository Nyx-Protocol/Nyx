use nyx_telemetry::metrics::{
    record_cmix_batch, record_cmix_messages, record_handshake_failure, record_handshake_success,
    record_rekey_event, record_rekey_failure, start_http_server, truncate_id,
};
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Start metrics HTTP server on port 9090
    let addr = "127.0.0.1:9090".parse().unwrap();
    let _guard = start_http_server(addr).await?;

    println!("Metrics server started at http://127.0.0.1:9090/metrics");
    println!("Recording sample metrics...");

    // Record handshake metrics
    for i in 0..5 {
        let session_id = truncate_id(&format!("session-{}", i), 8);
        let peer_id = truncate_id(&format!("peer-{}", i), 8);
        record_handshake_success(&session_id, &peer_id, "client", 100.0 + (i as f64 * 20.0));
    }

    // Record a few failures
    record_handshake_failure(
        &truncate_id("session-failed", 8),
        &truncate_id("peer-timeout", 8),
        "server",
        "timeout",
    );
    record_handshake_failure(
        &truncate_id("session-failed2", 8),
        &truncate_id("peer-invalid", 8),
        "client",
        "invalid_signature",
    );

    // Record cMix batch processing
    record_cmix_batch(5, true, 15.5);
    record_cmix_batch(25, true, 45.3);
    record_cmix_batch(75, true, 120.8);
    record_cmix_batch(150, false, 250.0);

    // Record cMix messages
    record_cmix_messages("inbound", 1000);
    record_cmix_messages("outbound", 750);

    // Record rekey events
    for i in 0..3 {
        let session_id = truncate_id(&format!("session-rekey-{}", i), 8);
        record_rekey_event(&session_id, "scheduled", 50.0 + (i as f64 * 10.0));
    }

    record_rekey_event(&truncate_id("session-forced", 8), "forced", 120.0);
    record_rekey_failure(&truncate_id("session-rekey-fail", 8), "crypto_error");

    println!("Sample metrics recorded successfully!");
    println!("\nOpen http://127.0.0.1:9090/metrics to view the metrics");
    println!("Press Ctrl+C to stop the server");

    // Keep server running
    loop {
        sleep(Duration::from_secs(1)).await;
    }
}
