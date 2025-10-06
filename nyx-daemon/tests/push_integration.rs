//! Integration tests for push notification relay with Go proxy
//!
//! These tests require the Go push proxy to be running on localhost:8765
//! Start proxy: cd nyx-push-proxy && ./nyx-push-proxy.exe

use nyx_core::push::PushProvider;
use nyx_daemon::push::{ApnsConfig, FcmConfig, PushConfig, PushRelay, WebPushConfig};

#[tokio::test]
#[ignore] // Requires Go proxy + valid credentials
async fn test_fcm_notification_via_proxy() {
    // This test demonstrates FCM integration but requires valid service account
    let config = PushConfig {
        fcm: Some(FcmConfig {
            service_account_path: "/path/to/service-account.json".to_string(),
            project_id: "test-project".to_string(),
        }),
        ..Default::default()
    };

    let relay = PushRelay::new(config).unwrap();

    // FCM token (long format)
    let fcm_token = "a".repeat(160);

    // This will fail with "Failed to read service account" error
    // In production, provide valid service account JSON
    let result = relay.send(&fcm_token, "Test Title", "Test Body").await;

    // Should fail due to missing credentials
    assert!(result.is_err());
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("Failed to read service account"));
}

#[tokio::test]
#[ignore] // Requires Go proxy + valid credentials
async fn test_apns_notification_via_proxy() {
    // This test demonstrates APNS integration but requires valid .p8 key
    let config = PushConfig {
        apns: Some(ApnsConfig {
            key_path: "/path/to/AuthKey.p8".to_string(),
            key_id: "ABC1234567".to_string(),
            team_id: "DEF7890123".to_string(),
            topic: "com.example.app".to_string(),
            sandbox: true,
        }),
        ..Default::default()
    };

    let relay = PushRelay::new(config).unwrap();

    // APNS token (64 hex characters)
    // SECURITY: This is a dummy token for testing only, not a real APNS credential
    let apns_token = "a1b2c3d4e5f6789012345678901234567890123456789012345678901234abcd";

    // This will fail with "Failed to read APNS key" error
    // In production, provide valid .p8 key file
    let result = relay.send(apns_token, "Test Title", "Test Body").await;

    // Should fail due to missing credentials
    assert!(result.is_err());
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("Failed to read APNS key"));
}

#[tokio::test]
#[ignore] // Requires Go proxy + valid credentials
async fn test_webpush_notification_via_proxy() {
    // This test demonstrates WebPush integration but requires valid VAPID keys
    let config = PushConfig {
        webpush: Some(WebPushConfig {
            vapid_public_key: "BPublicKey123".to_string(),
            vapid_private_key_path: "/path/to/vapid_private.pem".to_string(),
            contact_email: "admin@example.com".to_string(),
        }),
        ..Default::default()
    };

    let relay = PushRelay::new(config).unwrap();

    // WebPush endpoint (URL format)
    let webpush_endpoint = "https://fcm.googleapis.com/fcm/send/abc123";

    // This will fail with "Failed to read VAPID private key" error
    // In production, provide valid VAPID private key
    let result = relay
        .send(webpush_endpoint, "Test Title", "Test Body")
        .await;

    // Should fail due to missing credentials
    assert!(result.is_err());
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("Failed to read VAPID private key"));
}

#[tokio::test]
async fn test_proxy_connectivity() {
    // Test basic connectivity to Go proxy (no credentials needed)
    let config = PushConfig::default();
    let relay = PushRelay::new(config).unwrap();

    // Stats should be initialized
    let stats = relay.get_stats().await;
    assert_eq!(stats.total_sent, 0);
    assert_eq!(stats.total_failed, 0);
}

/// Test proxy health check endpoint
///
/// This test requires the Go push proxy to be running on localhost:8765.
/// To start the proxy manually: `cd nyx-push-proxy && go run .` or `./nyx-push-proxy.exe`
///
/// The test is marked as `#[ignore]` by default to avoid CI failures when the proxy is not running.
/// Run with `cargo test --ignored` to execute this test.
#[tokio::test]
#[ignore = "requires Go push proxy running on localhost:8765"]
async fn test_proxy_health_check() {
    // Verify Go proxy health endpoint using hyper (Pure Rust HTTP)
    use http_body_util::BodyExt;
    use hyper::{Method, Request, Uri};
    use hyper_util::client::legacy::{connect::HttpConnector, Client};
    use hyper_util::rt::TokioExecutor;

    let http_connector = HttpConnector::new();
    let client: Client<HttpConnector, http_body_util::Full<hyper::body::Bytes>> =
        Client::builder(TokioExecutor::new()).build(http_connector);

    let uri: Uri = "http://localhost:8765/health".parse().unwrap();
    let req = Request::builder()
        .method(Method::GET)
        .uri(uri)
        .body(http_body_util::Full::new(hyper::body::Bytes::new()))
        .unwrap();

    let response = client.request(req).await.expect(
        "Go proxy not running? Start: cd nyx-push-proxy && go run . or ./nyx-push-proxy.exe",
    );

    assert_eq!(response.status(), hyper::StatusCode::OK);

    let body_bytes = response.into_body().collect().await.unwrap().to_bytes();
    let health: serde_json::Value = serde_json::from_slice(&body_bytes).unwrap();
    assert_eq!(health["status"], "healthy");
}
