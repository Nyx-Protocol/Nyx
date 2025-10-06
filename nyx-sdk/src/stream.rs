#![forbid(unsafe_code)]

use crate::error::{Error, Result};
use bytes::Bytes;
use nyx_stream::{pair, AsyncStream, AsyncStreamConfig};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::time::timeout;

/// Stream statistics
#[derive(Debug, Clone, Default)]
pub struct StreamStats {
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub messages_sent: u64,
    pub messages_received: u64,
    pub errors: u64,
    pub created_at: Option<Instant>,
    pub last_activity: Option<Instant>,
}

/// Stream metadata
#[derive(Debug, Clone)]
pub struct StreamMetadata {
    pub stream_id: u32,
    pub target: Option<String>,
    pub protocol_version: u8,
    pub user_data: std::collections::HashMap<String, String>,
}

impl Default for StreamMetadata {
    fn default() -> Self {
        Self {
            stream_id: 0,
            target: None,
            protocol_version: 1,
            user_data: std::collections::HashMap::new(),
        }
    }
}

/// SDK wrapper for streams. Delegates to nyx-stream's AsyncStream, providing an adapter
/// with additional features like statistics, metadata, and lifecycle management.
#[derive(Clone)]
pub struct NyxStream {
    inner: AsyncStream,
    stats: Arc<StreamStatsInner>,
    metadata: Arc<tokio::sync::RwLock<StreamMetadata>>,
}

#[derive(Debug, Default)]
struct StreamStatsInner {
    bytes_sent: AtomicU64,
    bytes_received: AtomicU64,
    messages_sent: AtomicU64,
    messages_received: AtomicU64,
    errors: AtomicU64,
    created_at: std::sync::RwLock<Option<Instant>>,
    last_activity: std::sync::RwLock<Option<Instant>>,
}

impl NyxStream {
    /// Create a new stream with default configuration
    pub fn new() -> Self {
        let created_at = Instant::now();
        Self {
            inner: AsyncStream::new(AsyncStreamConfig::default()),
            stats: Arc::new(StreamStatsInner {
                created_at: std::sync::RwLock::new(Some(created_at)),
                ..Default::default()
            }),
            metadata: Arc::new(tokio::sync::RwLock::new(StreamMetadata::default())),
        }
    }

    /// Create a stream with custom configuration
    pub fn with_config(config: AsyncStreamConfig) -> Self {
        let created_at = Instant::now();
        let stream_id = config.stream_id;
        Self {
            inner: AsyncStream::new(config),
            stats: Arc::new(StreamStatsInner {
                created_at: std::sync::RwLock::new(Some(created_at)),
                ..Default::default()
            }),
            metadata: Arc::new(tokio::sync::RwLock::new(StreamMetadata {
                stream_id,
                ..Default::default()
            })),
        }
    }

    /// Create a pair of connected streams for testing
    pub fn pair(_buffer_size: usize) -> (Self, Self) {
        let config1 = AsyncStreamConfig {
            stream_id: 1,
            ..AsyncStreamConfig::default()
        };
        let config2 = AsyncStreamConfig {
            stream_id: 2,
            ..AsyncStreamConfig::default()
        };
        let (inner1, inner2) = pair(config1, config2);
        let created_at = Instant::now();
        (
            Self {
                inner: inner1,
                stats: Arc::new(StreamStatsInner {
                    created_at: std::sync::RwLock::new(Some(created_at)),
                    ..Default::default()
                }),
                metadata: Arc::new(tokio::sync::RwLock::new(StreamMetadata {
                    stream_id: 1,
                    ..Default::default()
                })),
            },
            Self {
                inner: inner2,
                stats: Arc::new(StreamStatsInner {
                    created_at: std::sync::RwLock::new(Some(created_at)),
                    ..Default::default()
                }),
                metadata: Arc::new(tokio::sync::RwLock::new(StreamMetadata {
                    stream_id: 2,
                    ..Default::default()
                })),
            },
        )
    }

    /// Send data through the stream
    pub async fn send<T: Into<Bytes>>(&mut self, data: T) -> Result<()> {
        let bytes = data.into();
        let len = bytes.len() as u64;

        self.inner
            .send(bytes)
            .await
            .map_err(|e| {
                self.stats.errors.fetch_add(1, Ordering::Relaxed);
                Error::Stream(e.to_string())
            })?;

        self.stats.bytes_sent.fetch_add(len, Ordering::Relaxed);
        self.stats.messages_sent.fetch_add(1, Ordering::Relaxed);
        self.update_last_activity();

        Ok(())
    }

    /// Send data with timeout
    pub async fn send_with_timeout<T: Into<Bytes>>(
        &mut self,
        data: T,
        timeout_ms: u64,
    ) -> Result<()> {
        timeout(Duration::from_millis(timeout_ms), self.send(data))
            .await
            .map_err(|_| Error::timeout(timeout_ms))?
    }

    /// Receive data from the stream
    pub async fn recv(&mut self) -> Result<Option<Bytes>> {
        let result = self
            .inner
            .recv()
            .await
            .map_err(|e| {
                self.stats.errors.fetch_add(1, Ordering::Relaxed);
                Error::Stream(e.to_string())
            })?;

        if let Some(ref bytes) = result {
            let len = bytes.len() as u64;
            self.stats
                .bytes_received
                .fetch_add(len, Ordering::Relaxed);
            self.stats
                .messages_received
                .fetch_add(1, Ordering::Relaxed);
            self.update_last_activity();
        }

        Ok(result)
    }

    /// Receive data from the stream with timeout
    pub async fn recv_with_timeout(&mut self, timeout_ms: u64) -> Result<Option<Bytes>> {
        timeout(Duration::from_millis(timeout_ms), self.recv())
            .await
            .map_err(|_| Error::timeout(timeout_ms))?
    }

    /// Close the stream
    pub async fn close(&mut self) -> Result<()> {
        self.inner
            .close()
            .await
            .map_err(|e| Error::Stream(e.to_string()))
    }

    /// Check if the stream is closed
    pub fn is_closed(&self) -> bool {
        self.inner.is_closed()
    }

    /// Get stream statistics
    pub fn stats(&self) -> StreamStats {
        StreamStats {
            bytes_sent: self.stats.bytes_sent.load(Ordering::Relaxed),
            bytes_received: self.stats.bytes_received.load(Ordering::Relaxed),
            messages_sent: self.stats.messages_sent.load(Ordering::Relaxed),
            messages_received: self.stats.messages_received.load(Ordering::Relaxed),
            errors: self.stats.errors.load(Ordering::Relaxed),
            created_at: *self.stats.created_at.read().unwrap(),
            last_activity: *self.stats.last_activity.read().unwrap(),
        }
    }

    /// Reset statistics
    pub fn reset_stats(&self) {
        self.stats.bytes_sent.store(0, Ordering::Relaxed);
        self.stats.bytes_received.store(0, Ordering::Relaxed);
        self.stats.messages_sent.store(0, Ordering::Relaxed);
        self.stats.messages_received.store(0, Ordering::Relaxed);
        self.stats.errors.store(0, Ordering::Relaxed);
    }

    /// Get stream metadata
    pub async fn metadata(&self) -> StreamMetadata {
        self.metadata.read().await.clone()
    }

    /// Update stream metadata
    pub async fn set_metadata(&self, metadata: StreamMetadata) {
        *self.metadata.write().await = metadata;
    }

    /// Set target address for the stream
    pub async fn set_target(&self, target: impl Into<String>) {
        self.metadata.write().await.target = Some(target.into());
    }

    /// Add custom metadata
    pub async fn add_user_data(&self, key: impl Into<String>, value: impl Into<String>) {
        self.metadata
            .write()
            .await
            .user_data
            .insert(key.into(), value.into());
    }

    /// Get uptime in seconds
    pub fn uptime(&self) -> Option<Duration> {
        self.stats
            .created_at
            .read()
            .unwrap()
            .map(|created| created.elapsed())
    }

    /// Get time since last activity
    pub fn idle_time(&self) -> Option<Duration> {
        self.stats
            .last_activity
            .read()
            .unwrap()
            .map(|last| last.elapsed())
    }

    fn update_last_activity(&self) {
        *self.stats.last_activity.write().unwrap() = Some(Instant::now());
    }
}

impl Default for NyxStream {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_stream_pair() {
        let (mut a, mut b) = NyxStream::pair(1024);
        
        a.send(Bytes::from_static(b"hello")).await.unwrap();
        let received = b.recv().await.unwrap();
        assert_eq!(received, Some(Bytes::from_static(b"hello")));
        
        // Check stats
        let stats_a = a.stats();
        assert_eq!(stats_a.bytes_sent, 5);
        assert_eq!(stats_a.messages_sent, 1);
        
        let stats_b = b.stats();
        assert_eq!(stats_b.bytes_received, 5);
        assert_eq!(stats_b.messages_received, 1);
    }

    #[tokio::test]
    async fn test_stream_metadata() {
        let stream = NyxStream::new();
        
        stream.set_target("example.com").await;
        stream.add_user_data("key", "value").await;
        
        let metadata = stream.metadata().await;
        assert_eq!(metadata.target, Some("example.com".to_string()));
        assert_eq!(metadata.user_data.get("key"), Some(&"value".to_string()));
    }

    #[tokio::test]
    async fn test_stream_timeout() {
        let (mut _a, mut b) = NyxStream::pair(1024);
        
        // Should timeout since no data is sent
        let result = b.recv_with_timeout(100).await;
        assert!(matches!(result, Err(Error::Timeout { .. })));
    }

    #[tokio::test]
    async fn test_stream_uptime() {
        let stream = NyxStream::new();
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        let uptime = stream.uptime().unwrap();
        assert!(uptime >= Duration::from_millis(100));
    }
}
