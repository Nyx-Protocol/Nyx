#![forbid(unsafe_code)]

//! gRPC client for Nyx Daemon control API.
//!
//! Provides high-level client interface with:
//! - Automatic connection management and reconnection
//! - Exponential backoff retry logic
//! - Streaming subscription helpers
//! - Timeout configuration
//! - Pure Rust implementation (zero C/C++ dependencies)

use crate::grpc_proto::{
    nyx_control_client::NyxControlClient, session_service_client::SessionServiceClient,
    ConfigUpdate, DataRequest, Empty, Event, EventFilter, HealthRequest, ListSessionsRequest,
    NetworkTopology, NodeInfo, OpenRequest, PathInfo, PathRequest, PeerInfo, SessionStatusRequest,
    StatsRequest, StatsUpdate, StreamId, StreamOptions, StreamStats,
};
use std::collections::HashMap;
use std::time::Duration;
use thiserror::Error;
use tonic::transport::{Channel, Endpoint};
use tonic::{Request, Status, Streaming};
use tracing::{debug, error, info, instrument, warn};

/// Maximum data size for send_data (1MB)
const MAX_DATA_SIZE: usize = 1024 * 1024;

/// Default connection timeout
const DEFAULT_CONNECT_TIMEOUT: Duration = Duration::from_secs(10);

/// Default request timeout
const DEFAULT_REQUEST_TIMEOUT: Duration = Duration::from_secs(30);

/// gRPC client errors
#[derive(Debug, Error)]
pub enum GrpcClientError {
    #[error("Connection failed: {0}")]
    ConnectionFailed(String),

    #[error("Request failed: {0}")]
    RequestFailed(String),

    #[error("Invalid argument: {0}")]
    InvalidArgument(String),

    #[error("Not found: {0}")]
    NotFound(String),

    #[error("Already exists: {0}")]
    AlreadyExists(String),

    #[error("Permission denied: {0}")]
    PermissionDenied(String),

    #[error("Resource exhausted: {0}")]
    ResourceExhausted(String),

    #[error("Deadline exceeded: {0}")]
    DeadlineExceeded(String),

    #[error("Service unavailable: {0}")]
    Unavailable(String),

    #[error("Internal error: {0}")]
    Internal(String),
}

impl From<Status> for GrpcClientError {
    fn from(status: Status) -> Self {
        let message = status.message().to_string();
        match status.code() {
            tonic::Code::InvalidArgument => GrpcClientError::InvalidArgument(message),
            tonic::Code::NotFound => GrpcClientError::NotFound(message),
            tonic::Code::AlreadyExists => GrpcClientError::AlreadyExists(message),
            tonic::Code::PermissionDenied => GrpcClientError::PermissionDenied(message),
            tonic::Code::ResourceExhausted => GrpcClientError::ResourceExhausted(message),
            tonic::Code::DeadlineExceeded => GrpcClientError::DeadlineExceeded(message),
            tonic::Code::Unavailable => GrpcClientError::Unavailable(message),
            tonic::Code::Internal => GrpcClientError::Internal(message),
            _ => GrpcClientError::RequestFailed(message),
        }
    }
}

pub type Result<T> = std::result::Result<T, GrpcClientError>;

/// Configuration for gRPC client
#[derive(Debug, Clone)]
pub struct GrpcClientConfig {
    /// Daemon gRPC server address (e.g., "http://127.0.0.1:50051")
    pub server_address: String,

    /// Connection timeout
    pub connect_timeout: Duration,

    /// Request timeout
    pub request_timeout: Duration,

    /// Maximum retry attempts for failed requests
    pub max_retry_attempts: u32,

    /// Initial retry delay (exponential backoff)
    pub initial_retry_delay: Duration,

    /// Maximum retry delay
    pub max_retry_delay: Duration,
}

impl Default for GrpcClientConfig {
    fn default() -> Self {
        Self {
            server_address: "http://127.0.0.1:50051".to_string(),
            connect_timeout: DEFAULT_CONNECT_TIMEOUT,
            request_timeout: DEFAULT_REQUEST_TIMEOUT,
            max_retry_attempts: 3,
            initial_retry_delay: Duration::from_millis(100),
            max_retry_delay: Duration::from_secs(5),
        }
    }
}

/// High-level gRPC client for Nyx Daemon
pub struct NyxGrpcClient {
    control_client: NyxControlClient<Channel>,
    session_client: SessionServiceClient<Channel>,
    config: GrpcClientConfig,
}

impl NyxGrpcClient {
    /// Create a new gRPC client with default configuration
    #[instrument(skip_all)]
    pub async fn new() -> Result<Self> {
        Self::with_config(GrpcClientConfig::default()).await
    }

    /// Create a new gRPC client with custom configuration
    #[instrument(skip_all, fields(server_address = %config.server_address))]
    pub async fn with_config(config: GrpcClientConfig) -> Result<Self> {
        info!("Connecting to Nyx daemon at {}", config.server_address);

        let channel = Self::create_channel(&config).await?;

        let control_client = NyxControlClient::new(channel.clone())
            .max_decoding_message_size(MAX_DATA_SIZE)
            .max_encoding_message_size(MAX_DATA_SIZE);

        let session_client = SessionServiceClient::new(channel)
            .max_decoding_message_size(MAX_DATA_SIZE)
            .max_encoding_message_size(MAX_DATA_SIZE);

        info!("Successfully connected to Nyx daemon");

        Ok(Self {
            control_client,
            session_client,
            config,
        })
    }

    /// Create a channel with retry logic
    async fn create_channel(config: &GrpcClientConfig) -> Result<Channel> {
        let endpoint = Endpoint::from_shared(config.server_address.clone())
            .map_err(|e| GrpcClientError::ConnectionFailed(format!("Invalid endpoint: {}", e)))?
            .connect_timeout(config.connect_timeout)
            .timeout(config.request_timeout);

        let mut attempt = 0;
        let mut delay = config.initial_retry_delay;

        loop {
            match endpoint.connect().await {
                Ok(channel) => {
                    debug!("Channel connected successfully");
                    return Ok(channel);
                }
                Err(e) => {
                    attempt += 1;
                    if attempt >= config.max_retry_attempts {
                        error!("Failed to connect after {} attempts: {}", attempt, e);
                        return Err(GrpcClientError::ConnectionFailed(format!(
                            "Max retry attempts reached: {}",
                            e
                        )));
                    }

                    warn!(
                        "Connection attempt {} failed: {}, retrying in {:?}",
                        attempt, e, delay
                    );
                    tokio::time::sleep(delay).await;

                    // Exponential backoff with jitter
                    delay = std::cmp::min(delay * 2, config.max_retry_delay);
                    let jitter =
                        Duration::from_millis(fastrand::u64(0..delay.as_millis() as u64 / 10));
                    delay += jitter;
                }
            }
        }
    }

    /// Reconnect to the daemon (useful after connection loss)
    #[instrument(skip(self))]
    pub async fn reconnect(&mut self) -> Result<()> {
        info!("Reconnecting to Nyx daemon");
        let channel = Self::create_channel(&self.config).await?;

        self.control_client = NyxControlClient::new(channel.clone())
            .max_decoding_message_size(MAX_DATA_SIZE)
            .max_encoding_message_size(MAX_DATA_SIZE);

        self.session_client = SessionServiceClient::new(channel)
            .max_decoding_message_size(MAX_DATA_SIZE)
            .max_encoding_message_size(MAX_DATA_SIZE);

        info!("Reconnection successful");
        Ok(())
    }

    // ===== Node Information =====

    /// Get node information (version, uptime, active connections)
    #[instrument(skip(self))]
    pub async fn get_node_info(&mut self) -> Result<NodeInfo> {
        debug!("Fetching node info");
        let request = Request::new(Empty {});
        let response = self.control_client.get_info(request).await.map_err(|e| {
            error!("get_info failed: {}", e);
            GrpcClientError::from(e)
        })?;
        Ok(response.into_inner())
    }

    /// Get daemon health status
    #[instrument(skip(self))]
    pub async fn get_health(
        &mut self,
        include_details: bool,
    ) -> Result<crate::grpc_proto::HealthResponse> {
        debug!("Checking daemon health");
        let request = Request::new(HealthRequest { include_details });
        let response = self.control_client.get_health(request).await.map_err(|e| {
            error!("get_health failed: {}", e);
            GrpcClientError::from(e)
        })?;
        Ok(response.into_inner())
    }

    // ===== Stream Management =====

    /// Open a new stream
    #[instrument(skip(self))]
    pub async fn open_stream(
        &mut self,
        stream_name: String,
        target_address: String,
        options: Option<StreamOptions>,
    ) -> Result<crate::grpc_proto::StreamResponse> {
        debug!("Opening stream: {}", stream_name);
        let request = Request::new(OpenRequest {
            stream_name,
            target_address,
            options,
        });
        let response = self
            .control_client
            .open_stream(request)
            .await
            .map_err(|e| {
                error!("open_stream failed: {}", e);
                GrpcClientError::from(e)
            })?;
        Ok(response.into_inner())
    }

    /// Close a stream
    #[instrument(skip(self))]
    pub async fn close_stream(&mut self, stream_id: u32) -> Result<()> {
        debug!("Closing stream: {}", stream_id);
        let request = Request::new(StreamId { id: stream_id });
        self.control_client
            .close_stream(request)
            .await
            .map_err(|e| {
                error!("close_stream failed: {}", e);
                GrpcClientError::from(e)
            })?;
        Ok(())
    }

    /// Get stream statistics
    #[instrument(skip(self))]
    pub async fn get_stream_stats(&mut self, stream_id: u32) -> Result<StreamStats> {
        debug!("Fetching stream stats: {}", stream_id);
        let request = Request::new(StreamId { id: stream_id });
        let response = self
            .control_client
            .get_stream_stats(request)
            .await
            .map_err(|e| {
                error!("get_stream_stats failed: {}", e);
                GrpcClientError::from(e)
            })?;
        Ok(response.into_inner())
    }

    /// List all active streams (streaming response)
    #[instrument(skip(self))]
    pub async fn list_streams(&mut self) -> Result<Streaming<StreamStats>> {
        debug!("Listing streams (streaming)");
        let request = Request::new(Empty {});
        let response = self
            .control_client
            .list_streams(request)
            .await
            .map_err(|e| {
                error!("list_streams failed: {}", e);
                GrpcClientError::from(e)
            })?;
        Ok(response.into_inner())
    }

    // ===== Data Transfer =====

    /// Send data through a stream
    #[instrument(skip(self, data), fields(stream_id = %stream_id, data_len = data.len()))]
    pub async fn send_data(
        &mut self,
        stream_id: String,
        data: Vec<u8>,
    ) -> Result<crate::grpc_proto::DataResponse> {
        if data.len() > MAX_DATA_SIZE {
            return Err(GrpcClientError::InvalidArgument(format!(
                "Data size {} exceeds maximum {}",
                data.len(),
                MAX_DATA_SIZE
            )));
        }

        debug!("Sending {} bytes to stream: {}", data.len(), stream_id);
        let request = Request::new(DataRequest { stream_id, data });
        let response = self.control_client.send_data(request).await.map_err(|e| {
            error!("send_data failed: {}", e);
            GrpcClientError::from(e)
        })?;
        Ok(response.into_inner())
    }

    /// Receive data from a stream
    #[instrument(skip(self))]
    pub async fn receive_data(
        &mut self,
        stream_id: u32,
    ) -> Result<crate::grpc_proto::ReceiveResponse> {
        debug!("Receiving data from stream: {}", stream_id);
        let request = Request::new(StreamId { id: stream_id });
        let response = self
            .control_client
            .receive_data(request)
            .await
            .map_err(|e| {
                error!("receive_data failed: {}", e);
                GrpcClientError::from(e)
            })?;
        Ok(response.into_inner())
    }

    // ===== Configuration Management =====

    /// Update daemon configuration
    #[instrument(skip(self, settings))]
    pub async fn update_config(
        &mut self,
        settings: HashMap<String, String>,
    ) -> Result<crate::grpc_proto::ConfigResponse> {
        debug!("Updating configuration with {} settings", settings.len());
        let request = Request::new(ConfigUpdate {
            settings,
            restart_required: false,
        });
        let response = self
            .control_client
            .update_config(request)
            .await
            .map_err(|e| {
                error!("update_config failed: {}", e);
                GrpcClientError::from(e)
            })?;
        Ok(response.into_inner())
    }

    /// Reload daemon configuration from disk
    #[instrument(skip(self))]
    pub async fn reload_config(&mut self) -> Result<crate::grpc_proto::ConfigResponse> {
        debug!("Reloading configuration");
        let request = Request::new(Empty {});
        let response = self
            .control_client
            .reload_config(request)
            .await
            .map_err(|e| {
                error!("reload_config failed: {}", e);
                GrpcClientError::from(e)
            })?;
        Ok(response.into_inner())
    }

    // ===== Path and Topology =====

    /// Build a new path through the mixnet
    #[instrument(skip(self))]
    pub async fn build_path(
        &mut self,
        target: String,
        hops: u32,
        strategy: String,
    ) -> Result<crate::grpc_proto::PathResponse> {
        debug!("Building path to {} with {} hops", target, hops);
        let request = Request::new(PathRequest {
            target,
            hops,
            strategy,
        });
        let response = self.control_client.build_path(request).await.map_err(|e| {
            error!("build_path failed: {}", e);
            GrpcClientError::from(e)
        })?;
        Ok(response.into_inner())
    }

    /// Get all paths (streaming response)
    #[instrument(skip(self))]
    pub async fn get_paths(&mut self) -> Result<Streaming<PathInfo>> {
        debug!("Getting paths");
        let request = Request::new(Empty {});
        let response = self.control_client.get_paths(request).await.map_err(|e| {
            error!("get_paths failed: {}", e);
            GrpcClientError::from(e)
        })?;
        Ok(response.into_inner())
    }

    /// Get network topology snapshot
    #[instrument(skip(self))]
    pub async fn get_topology(&mut self) -> Result<NetworkTopology> {
        debug!("Fetching topology snapshot");
        let request = Request::new(Empty {});
        let response = self
            .control_client
            .get_topology(request)
            .await
            .map_err(|e| {
                error!("get_topology failed: {}", e);
                GrpcClientError::from(e)
            })?;
        Ok(response.into_inner())
    }

    /// Get peer list (streaming response)
    #[instrument(skip(self))]
    pub async fn get_peers(&mut self) -> Result<Streaming<PeerInfo>> {
        debug!("Getting peer list (streaming)");
        let request = Request::new(Empty {});
        let response = self.control_client.get_peers(request).await.map_err(|e| {
            error!("get_peers failed: {}", e);
            GrpcClientError::from(e)
        })?;
        Ok(response.into_inner())
    }

    // ===== Event and Stats Subscriptions =====

    /// Subscribe to daemon events (streaming response)
    #[instrument(skip(self))]
    pub async fn subscribe_events(
        &mut self,
        event_filter: EventFilter,
    ) -> Result<Streaming<Event>> {
        debug!("Subscribing to events: {:?}", event_filter.types);
        let request = Request::new(event_filter);
        let response = self
            .control_client
            .subscribe_events(request)
            .await
            .map_err(|e| {
                error!("subscribe_events failed: {}", e);
                GrpcClientError::from(e)
            })?;
        Ok(response.into_inner())
    }

    /// Subscribe to daemon statistics (streaming response)
    #[instrument(skip(self))]
    pub async fn subscribe_stats(
        &mut self,
        interval_ms: u32,
        metrics: Vec<String>,
    ) -> Result<Streaming<StatsUpdate>> {
        debug!("Subscribing to stats with interval: {}ms", interval_ms);
        let request = Request::new(StatsRequest {
            interval_ms,
            metrics,
        });
        let response = self
            .control_client
            .subscribe_stats(request)
            .await
            .map_err(|e| {
                error!("subscribe_stats failed: {}", e);
                GrpcClientError::from(e)
            })?;
        Ok(response.into_inner())
    }

    // ===== Session Management =====

    /// Get session status
    #[instrument(skip(self))]
    pub async fn get_session_status(
        &mut self,
        session_id: u32,
    ) -> Result<crate::grpc_proto::SessionStatusResponse> {
        debug!("Getting session status: {}", session_id);
        let request = Request::new(SessionStatusRequest { session_id });
        let response = self
            .session_client
            .get_session_status(request)
            .await
            .map_err(|e| {
                error!("get_session_status failed: {}", e);
                GrpcClientError::from(e)
            })?;
        Ok(response.into_inner())
    }

    /// List all active sessions
    #[instrument(skip(self))]
    pub async fn list_sessions(
        &mut self,
        state_filter: Option<String>,
        role_filter: Option<String>,
    ) -> Result<crate::grpc_proto::ListSessionsResponse> {
        debug!("Listing sessions");
        let request = Request::new(ListSessionsRequest {
            state_filter,
            role_filter,
        });
        let response = self
            .session_client
            .list_sessions(request)
            .await
            .map_err(|e| {
                error!("list_sessions failed: {}", e);
                GrpcClientError::from(e)
            })?;
        Ok(response.into_inner())
    }

    /// Close a session
    #[instrument(skip(self))]
    pub async fn close_session(&mut self, session_id: u32) -> Result<()> {
        debug!("Closing session: {}", session_id);
        let request = Request::new(SessionStatusRequest { session_id });
        self.session_client
            .close_session(request)
            .await
            .map_err(|e| {
                error!("close_session failed: {}", e);
                GrpcClientError::from(e)
            })?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = GrpcClientConfig::default();
        assert_eq!(config.server_address, "http://127.0.0.1:50051");
        assert_eq!(config.connect_timeout, Duration::from_secs(10));
        assert_eq!(config.request_timeout, Duration::from_secs(30));
        assert_eq!(config.max_retry_attempts, 3);
    }

    #[test]
    fn test_custom_config() {
        let config = GrpcClientConfig {
            server_address: "http://localhost:8080".to_string(),
            connect_timeout: Duration::from_secs(5),
            request_timeout: Duration::from_secs(15),
            max_retry_attempts: 5,
            initial_retry_delay: Duration::from_millis(50),
            max_retry_delay: Duration::from_secs(10),
        };
        assert_eq!(config.server_address, "http://localhost:8080");
        assert_eq!(config.connect_timeout, Duration::from_secs(5));
        assert_eq!(config.max_retry_attempts, 5);
    }

    #[test]
    fn test_error_conversion_from_status() {
        let status = Status::invalid_argument("bad input");
        let error = GrpcClientError::from(status);
        match error {
            GrpcClientError::InvalidArgument(msg) => assert_eq!(msg, "bad input"),
            _ => panic!("Expected InvalidArgument error"),
        }

        let status = Status::not_found("resource missing");
        let error = GrpcClientError::from(status);
        match error {
            GrpcClientError::NotFound(msg) => assert_eq!(msg, "resource missing"),
            _ => panic!("Expected NotFound error"),
        }
    }

    #[tokio::test]
    async fn test_create_channel_invalid_endpoint() {
        let config = GrpcClientConfig {
            server_address: "invalid://not-a-valid-url".to_string(),
            connect_timeout: Duration::from_millis(100),
            request_timeout: Duration::from_millis(100),
            max_retry_attempts: 1,
            initial_retry_delay: Duration::from_millis(10),
            max_retry_delay: Duration::from_millis(50),
        };

        let result = NyxGrpcClient::create_channel(&config).await;
        assert!(result.is_err());
        match result.unwrap_err() {
            GrpcClientError::ConnectionFailed(msg) => {
                // Either invalid endpoint or max retry attempts error is acceptable
                assert!(msg.contains("Invalid endpoint") || msg.contains("Max retry attempts"));
            }
            _ => panic!("Expected ConnectionFailed error"),
        }
    }

    // Integration tests would require a running daemon
    // These are placeholder tests demonstrating the API

    #[tokio::test]
    #[ignore] // Requires running daemon
    async fn test_integration_get_node_info() {
        let mut client = NyxGrpcClient::new().await.unwrap();
        let info = client.get_node_info().await.unwrap();
        assert!(!info.node_id.is_empty());
        assert!(!info.version.is_empty());
    }

    #[tokio::test]
    #[ignore] // Requires running daemon
    async fn test_integration_open_stream() {
        let mut client = NyxGrpcClient::new().await.unwrap();
        let response = client
            .open_stream(
                "test-stream".to_string(),
                "example.com:443".to_string(),
                None,
            )
            .await
            .unwrap();
        assert!(response.success);
    }

    #[tokio::test]
    #[ignore] // Requires running daemon
    async fn test_integration_reconnect() {
        let mut client = NyxGrpcClient::new().await.unwrap();
        // First request should work
        let _info1 = client.get_node_info().await.unwrap();

        // Reconnect
        client.reconnect().await.unwrap();

        // Second request after reconnect should still work
        let _info2 = client.get_node_info().await.unwrap();
    }

    #[tokio::test]
    #[ignore] // Requires running daemon
    async fn test_integration_streaming_events() {
        let mut client = NyxGrpcClient::new().await.unwrap();
        let filter = EventFilter {
            types: vec!["stream".to_string()],
            stream_ids: vec![],
            severity: "info".to_string(),
        };
        let mut stream = client.subscribe_events(filter).await.unwrap();

        // Read a few events
        use tokio_stream::StreamExt;
        for _ in 0..3 {
            if let Some(result) = stream.next().await {
                let event = result.unwrap();
                assert!(!event.r#type.is_empty());
            }
        }
    }

    #[tokio::test]
    #[ignore] // Requires running daemon
    async fn test_integration_list_sessions() {
        let mut client = NyxGrpcClient::new().await.unwrap();
        let response = client.list_sessions(None, None).await.unwrap();
        // Should succeed even if no sessions exist (total_count is u32, always >= 0)
        let _count = response.total_count;
    }
}
