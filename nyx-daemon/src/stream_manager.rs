//! Stream Manager
//!
//! Manages multiplexed streams within connections:
//! - Stream ID allocation (odd/even separation per QUIC model)
//! - Bidirectional and unidirectional stream support
//! - Stream state tracking (Open, HalfClosed, Closed)
//! - Frame demultiplexing by stream ID
//! - Backpressure handling with receive buffer limits
//! - CLOSE frame processing
//!
//! Design decisions:
//! - Client-initiated streams: odd IDs (1, 3, 5, ...)
//! - Server-initiated streams: even IDs (2, 4, 6, ...)
//! - Per-stream receive buffer with configurable max size
//! - Flow control window per stream

#![forbid(unsafe_code)]

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use std::time::Instant;
use tokio::sync::RwLock;
use tracing::{debug, info};

/// Stream identifier
pub type StreamId = u64;

/// Connection identifier
pub type ConnectionId = u32;

/// Stream Manager configuration
#[derive(Debug, Clone)]
pub struct StreamManagerConfig {
    /// Maximum number of concurrent streams per connection
    pub max_streams_per_connection: usize,
    /// Maximum receive buffer size per stream (bytes)
    pub max_recv_buffer_size: usize,
    /// Initial flow control window (bytes)
    pub initial_flow_control_window: u64,
    /// Maximum bidirectional streams
    pub max_bidi_streams: usize,
    /// Maximum unidirectional streams
    pub max_uni_streams: usize,
}

impl Default for StreamManagerConfig {
    fn default() -> Self {
        Self {
            max_streams_per_connection: 100,
            max_recv_buffer_size: 1_048_576,    // 1 MB
            initial_flow_control_window: 65536, // 64 KB
            max_bidi_streams: 100,
            max_uni_streams: 100,
        }
    }
}

/// Stream type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamType {
    /// Bidirectional stream (can send and receive)
    Bidirectional,
    /// Unidirectional stream (send-only or receive-only)
    Unidirectional,
}

/// Stream state
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamState {
    /// Stream is open for both send and receive
    Open,
    /// Send side is closed, receive side is open
    HalfClosedSend,
    /// Receive side is closed, send side is open
    HalfClosedRecv,
    /// Stream is fully closed
    Closed,
}

/// Stream data frame
#[derive(Debug, Clone)]
pub struct StreamFrame {
    pub stream_id: StreamId,
    pub offset: u64,
    pub data: Vec<u8>,
    pub fin: bool, // Final frame indicator
}

/// Stream
pub struct Stream {
    pub id: StreamId,
    pub connection_id: ConnectionId,
    pub stream_type: StreamType,
    pub state: StreamState,
    pub created_at: Instant,
    pub last_activity: Instant,

    // Send state
    pub send_offset: u64,
    pub send_buffer: VecDeque<u8>,
    pub send_closed: bool,

    // Receive state
    pub recv_offset: u64,
    pub recv_buffer: VecDeque<u8>,
    pub recv_closed: bool,
    pub flow_control_window: u64,

    // Out-of-order frame reassembly
    // Maps frame offset -> frame data for frames received ahead of time
    pub pending_frames: HashMap<u64, Vec<u8>>,

    // Statistics
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub frames_sent: u64,
    pub frames_received: u64,
}

impl Stream {
    pub fn new(
        id: StreamId,
        connection_id: ConnectionId,
        stream_type: StreamType,
        initial_window: u64,
    ) -> Self {
        Self {
            id,
            connection_id,
            stream_type,
            state: StreamState::Open,
            created_at: Instant::now(),
            last_activity: Instant::now(),
            send_offset: 0,
            send_buffer: VecDeque::new(),
            send_closed: false,
            recv_offset: 0,
            recv_buffer: VecDeque::new(),
            recv_closed: false,
            flow_control_window: initial_window,
            pending_frames: HashMap::new(),
            bytes_sent: 0,
            bytes_received: 0,
            frames_sent: 0,
            frames_received: 0,
        }
    }

    /// Check if stream can receive more data
    pub fn can_receive(&self, data_len: usize) -> bool {
        self.recv_buffer.len() + data_len <= self.flow_control_window as usize
    }

    /// Write data to send buffer
    pub fn write(&mut self, data: &[u8]) -> Result<usize, StreamError> {
        if self.send_closed {
            return Err(StreamError::SendClosed);
        }

        self.send_buffer.extend(data);
        self.last_activity = Instant::now();
        Ok(data.len())
    }

    /// Read data from receive buffer
    pub fn read(&mut self, buf: &mut [u8]) -> Result<usize, StreamError> {
        if self.recv_buffer.is_empty() {
            if self.recv_closed {
                return Ok(0); // EOF
            }
            return Err(StreamError::WouldBlock);
        }

        let to_read = buf.len().min(self.recv_buffer.len());
        for item in buf.iter_mut().take(to_read) {
            *item = self.recv_buffer.pop_front().unwrap();
        }

        self.last_activity = Instant::now();
        Ok(to_read)
    }

    /// Process incoming frame with out-of-order handling
    ///
    /// This method handles frames arriving in any order by:
    /// 1. Checking if the frame offset matches the expected recv_offset (in-order)
    /// 2. If in-order, appending to recv_buffer immediately
    /// 3. If out-of-order (offset > recv_offset), storing in pending_frames
    /// 4. After each frame, attempting to reassemble consecutive pending frames
    ///
    /// Edge cases:
    /// - Duplicate frames (same offset): ignored
    /// - Overlapping frames: not supported, returns error
    /// - Flow control: enforced on total buffered data including pending
    pub fn on_frame_received(&mut self, frame: StreamFrame) -> Result<(), StreamError> {
        if self.recv_closed {
            return Err(StreamError::RecvClosed);
        }

        let frame_end = frame.offset + frame.data.len() as u64;

        // Reject frames that are behind our current recv_offset (duplicates or retransmissions)
        if frame_end <= self.recv_offset {
            // Duplicate/old frame, silently ignore
            return Ok(());
        }

        // Check flow control: total pending data must not exceed window
        let pending_total: usize = self.pending_frames.values().map(|v| v.len()).sum();
        let total_buffered = self.recv_buffer.len() + pending_total + frame.data.len();
        if total_buffered > self.flow_control_window as usize {
            return Err(StreamError::FlowControlViolation);
        }

        // Case 1: In-order frame (offset matches expected recv_offset)
        if frame.offset == self.recv_offset {
            self.recv_buffer.extend(&frame.data);
            self.recv_offset += frame.data.len() as u64;
            self.bytes_received += frame.data.len() as u64;
            self.frames_received += 1;

            if frame.fin {
                self.recv_closed = true;
            }

            // Try to reassemble any pending frames that are now consecutive
            self.reassemble_pending_frames();

            if self.recv_closed {
                self.update_state();
            }

            self.last_activity = Instant::now();
            return Ok(());
        }

        // Case 2: Out-of-order frame (offset > recv_offset)
        if frame.offset > self.recv_offset {
            // Check for overlapping frames (not supported)
            if frame.offset < self.recv_offset + self.recv_buffer.len() as u64 {
                return Err(StreamError::OverlappingFrame);
            }

            // Store in pending frames for later reassembly
            self.pending_frames.insert(frame.offset, frame.data);
            self.frames_received += 1;

            // Store FIN flag if present (will be applied when frame is reassembled)
            if frame.fin {
                self.recv_closed = true;
            }

            self.last_activity = Instant::now();
            return Ok(());
        }

        // Case 3: Partial overlap (should not happen with proper frame boundaries)
        Err(StreamError::OverlappingFrame)
    }

    /// Reassemble consecutive pending frames into recv_buffer
    ///
    /// This method is called after receiving an in-order frame to check if
    /// any previously received out-of-order frames can now be appended.
    /// It iterates through pending_frames in order and appends any that
    /// are now consecutive with the recv_offset.
    fn reassemble_pending_frames(&mut self) {
        loop {
            if let Some(data) = self.pending_frames.remove(&self.recv_offset) {
                self.recv_buffer.extend(&data);
                self.recv_offset += data.len() as u64;
                self.bytes_received += data.len() as u64;
            } else {
                // No more consecutive frames
                break;
            }
        }
    }

    /// Close send side
    pub fn close_send(&mut self) {
        self.send_closed = true;
        self.update_state();
    }

    /// Close receive side
    pub fn close_recv(&mut self) {
        self.recv_closed = true;
        self.update_state();
    }

    /// Update stream state based on send/recv closure
    fn update_state(&mut self) {
        self.state = match (self.send_closed, self.recv_closed) {
            (false, false) => StreamState::Open,
            (true, false) => StreamState::HalfClosedSend,
            (false, true) => StreamState::HalfClosedRecv,
            (true, true) => StreamState::Closed,
        };
    }

    /// Get available receive buffer space
    pub fn recv_window_available(&self) -> u64 {
        self.flow_control_window
            .saturating_sub(self.recv_buffer.len() as u64)
    }
}

/// Connection streams
struct ConnectionStreams {
    streams: HashMap<StreamId, Stream>,
    next_client_stream_id: StreamId, // Next odd ID
    next_server_stream_id: StreamId, // Next even ID
    bidi_count: usize,
    uni_count: usize,
}

impl ConnectionStreams {
    fn new() -> Self {
        Self {
            streams: HashMap::new(),
            next_client_stream_id: 1, // Start with odd
            next_server_stream_id: 2, // Start with even
            bidi_count: 0,
            uni_count: 0,
        }
    }
}

/// Stream Manager
pub struct StreamManager {
    connections: Arc<RwLock<HashMap<ConnectionId, ConnectionStreams>>>,
    config: StreamManagerConfig,
}

impl StreamManager {
    pub fn new(config: StreamManagerConfig) -> Self {
        info!("StreamManager initialized with config: {:?}", config);
        Self {
            connections: Arc::new(RwLock::new(HashMap::new())),
            config,
        }
    }

    /// Register a new connection
    pub async fn register_connection(&self, conn_id: ConnectionId) {
        let mut conns = self.connections.write().await;
        conns.insert(conn_id, ConnectionStreams::new());
        info!("Registered connection {} for stream management", conn_id);
    }

    /// Unregister a connection (closes all streams)
    pub async fn unregister_connection(&self, conn_id: ConnectionId) -> Result<(), StreamError> {
        let mut conns = self.connections.write().await;

        if let Some(conn_streams) = conns.remove(&conn_id) {
            info!(
                "Unregistered connection {} (closed {} streams)",
                conn_id,
                conn_streams.streams.len()
            );
            Ok(())
        } else {
            Err(StreamError::ConnectionNotFound)
        }
    }

    /// Create a new client-initiated stream (odd ID)
    pub async fn create_client_stream(
        &self,
        conn_id: ConnectionId,
        stream_type: StreamType,
    ) -> Result<StreamId, StreamError> {
        let mut conns = self.connections.write().await;

        let conn_streams = conns
            .get_mut(&conn_id)
            .ok_or(StreamError::ConnectionNotFound)?;

        // Check limits
        match stream_type {
            StreamType::Bidirectional => {
                if conn_streams.bidi_count >= self.config.max_bidi_streams {
                    return Err(StreamError::TooManyStreams);
                }
                conn_streams.bidi_count += 1;
            }
            StreamType::Unidirectional => {
                if conn_streams.uni_count >= self.config.max_uni_streams {
                    return Err(StreamError::TooManyStreams);
                }
                conn_streams.uni_count += 1;
            }
        }

        let stream_id = conn_streams.next_client_stream_id;
        conn_streams.next_client_stream_id += 2; // Next odd

        let stream = Stream::new(
            stream_id,
            conn_id,
            stream_type,
            self.config.initial_flow_control_window,
        );

        conn_streams.streams.insert(stream_id, stream);

        debug!(
            "Created client stream {} on connection {} (type: {:?})",
            stream_id, conn_id, stream_type
        );

        Ok(stream_id)
    }

    /// Create a new server-initiated stream (even ID)
    pub async fn create_server_stream(
        &self,
        conn_id: ConnectionId,
        stream_type: StreamType,
    ) -> Result<StreamId, StreamError> {
        let mut conns = self.connections.write().await;

        let conn_streams = conns
            .get_mut(&conn_id)
            .ok_or(StreamError::ConnectionNotFound)?;

        // Check limits
        match stream_type {
            StreamType::Bidirectional => {
                if conn_streams.bidi_count >= self.config.max_bidi_streams {
                    return Err(StreamError::TooManyStreams);
                }
                conn_streams.bidi_count += 1;
            }
            StreamType::Unidirectional => {
                if conn_streams.uni_count >= self.config.max_uni_streams {
                    return Err(StreamError::TooManyStreams);
                }
                conn_streams.uni_count += 1;
            }
        }

        let stream_id = conn_streams.next_server_stream_id;
        conn_streams.next_server_stream_id += 2; // Next even

        let stream = Stream::new(
            stream_id,
            conn_id,
            stream_type,
            self.config.initial_flow_control_window,
        );

        conn_streams.streams.insert(stream_id, stream);

        debug!(
            "Created server stream {} on connection {} (type: {:?})",
            stream_id, conn_id, stream_type
        );

        Ok(stream_id)
    }

    /// Close a stream
    pub async fn close_stream(
        &self,
        conn_id: ConnectionId,
        stream_id: StreamId,
    ) -> Result<(), StreamError> {
        let mut conns = self.connections.write().await;

        let conn_streams = conns
            .get_mut(&conn_id)
            .ok_or(StreamError::ConnectionNotFound)?;

        if let Some(stream) = conn_streams.streams.get_mut(&stream_id) {
            stream.close_send();
            stream.close_recv();

            if stream.state == StreamState::Closed {
                let stream_type = stream.stream_type;
                conn_streams.streams.remove(&stream_id);

                match stream_type {
                    StreamType::Bidirectional => conn_streams.bidi_count -= 1,
                    StreamType::Unidirectional => conn_streams.uni_count -= 1,
                }

                debug!(
                    "Closed and removed stream {} on connection {}",
                    stream_id, conn_id
                );
            }

            Ok(())
        } else {
            Err(StreamError::StreamNotFound)
        }
    }

    /// Process incoming frame (demultiplex by stream ID)
    pub async fn on_frame_received(
        &self,
        conn_id: ConnectionId,
        frame: StreamFrame,
    ) -> Result<(), StreamError> {
        let mut conns = self.connections.write().await;

        let conn_streams = conns
            .get_mut(&conn_id)
            .ok_or(StreamError::ConnectionNotFound)?;

        let stream = conn_streams
            .streams
            .get_mut(&frame.stream_id)
            .ok_or(StreamError::StreamNotFound)?;

        stream.on_frame_received(frame)
    }

    /// Write data to stream
    pub async fn write_stream(
        &self,
        conn_id: ConnectionId,
        stream_id: StreamId,
        data: &[u8],
    ) -> Result<usize, StreamError> {
        let mut conns = self.connections.write().await;

        let conn_streams = conns
            .get_mut(&conn_id)
            .ok_or(StreamError::ConnectionNotFound)?;

        let stream = conn_streams
            .streams
            .get_mut(&stream_id)
            .ok_or(StreamError::StreamNotFound)?;

        stream.write(data)
    }

    /// Read data from stream
    pub async fn read_stream(
        &self,
        conn_id: ConnectionId,
        stream_id: StreamId,
        buf: &mut [u8],
    ) -> Result<usize, StreamError> {
        let mut conns = self.connections.write().await;

        let conn_streams = conns
            .get_mut(&conn_id)
            .ok_or(StreamError::ConnectionNotFound)?;

        let stream = conn_streams
            .streams
            .get_mut(&stream_id)
            .ok_or(StreamError::StreamNotFound)?;

        stream.read(buf)
    }

    /// Get stream status
    pub async fn get_stream_status(
        &self,
        conn_id: ConnectionId,
        stream_id: StreamId,
    ) -> Option<StreamStatus> {
        let conns = self.connections.read().await;

        conns.get(&conn_id).and_then(|conn_streams| {
            conn_streams
                .streams
                .get(&stream_id)
                .map(|stream| StreamStatus {
                    id: stream.id,
                    connection_id: stream.connection_id,
                    stream_type: stream.stream_type,
                    state: stream.state,
                    age: stream.created_at.elapsed(),
                    idle_time: stream.last_activity.elapsed(),
                    bytes_sent: stream.bytes_sent,
                    bytes_received: stream.bytes_received,
                    frames_sent: stream.frames_sent,
                    frames_received: stream.frames_received,
                    send_buffer_len: stream.send_buffer.len(),
                    recv_buffer_len: stream.recv_buffer.len(),
                    recv_window_available: stream.recv_window_available(),
                })
        })
    }

    /// List all streams for a connection
    pub async fn list_streams(&self, conn_id: ConnectionId) -> Vec<StreamId> {
        let conns = self.connections.read().await;

        conns
            .get(&conn_id)
            .map(|conn_streams| conn_streams.streams.keys().copied().collect())
            .unwrap_or_default()
    }

    /// Get total stream count across all connections
    pub fn stream_count(&self) -> usize {
        // Non-blocking access for synchronous contexts
        self.connections
            .try_read()
            .map(|conns| conns.values().map(|cs| cs.streams.len()).sum())
            .unwrap_or(0)
    }

    /// Iterate all streams across all connections
    ///
    /// Returns a vector of StreamStatus for all active streams.
    /// This is useful for monitoring, debugging, and gRPC API exposure.
    ///
    /// Note: This creates a snapshot of all streams at the time of call.
    /// Streams may be created or destroyed after this call returns.
    pub async fn iter_all_streams(&self) -> Vec<StreamStatus> {
        let conns = self.connections.read().await;
        let mut all_streams = Vec::new();

        for conn_streams in conns.values() {
            for stream in conn_streams.streams.values() {
                all_streams.push(StreamStatus {
                    id: stream.id,
                    connection_id: stream.connection_id,
                    stream_type: stream.stream_type,
                    state: stream.state,
                    age: stream.created_at.elapsed(),
                    idle_time: stream.last_activity.elapsed(),
                    bytes_sent: stream.bytes_sent,
                    bytes_received: stream.bytes_received,
                    frames_sent: stream.frames_sent,
                    frames_received: stream.frames_received,
                    send_buffer_len: stream.send_buffer.len(),
                    recv_buffer_len: stream.recv_buffer.len(),
                    recv_window_available: stream.recv_window_available(),
                });
            }
        }

        all_streams
    }

    /// Create a reverse index for stream_id -> connection_id lookup
    ///
    /// Returns a HashMap mapping stream_id to connection_id.
    ///
    /// # Important Limitations
    /// - Stream IDs are only unique within a connection, not globally
    /// - If multiple connections have streams with the same ID, only one will be in the index
    /// - This method is primarily useful for single-connection scenarios
    /// - For multi-connection scenarios, use `iter_all_streams()` instead
    ///
    /// # Performance
    /// This is an O(n) operation where n is the total number of streams.
    /// Consider caching this index if called frequently.
    pub async fn build_stream_index(&self) -> HashMap<StreamId, ConnectionId> {
        let conns = self.connections.read().await;
        let mut index = HashMap::new();

        for (conn_id, conn_streams) in conns.iter() {
            for stream_id in conn_streams.streams.keys() {
                index.insert(*stream_id, *conn_id);
            }
        }

        index
    }
}

/// Stream status (for API exposure)
#[derive(Debug, Clone)]
pub struct StreamStatus {
    pub id: StreamId,
    pub connection_id: ConnectionId,
    pub stream_type: StreamType,
    pub state: StreamState,
    pub age: std::time::Duration,
    pub idle_time: std::time::Duration,
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub frames_sent: u64,
    pub frames_received: u64,
    pub send_buffer_len: usize,
    pub recv_buffer_len: usize,
    pub recv_window_available: u64,
}

/// Stream errors
#[derive(Debug, thiserror::Error)]
pub enum StreamError {
    #[error("Connection not found")]
    ConnectionNotFound,

    #[error("Stream not found")]
    StreamNotFound,

    #[error("Too many streams")]
    TooManyStreams,

    #[error("Send side closed")]
    SendClosed,

    #[error("Receive side closed")]
    RecvClosed,

    #[error("Flow control violation")]
    FlowControlViolation,

    #[error("Would block")]
    WouldBlock,

    #[error("Overlapping frame detected")]
    OverlappingFrame,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_stream_id_allocation() {
        let manager = StreamManager::new(StreamManagerConfig::default());
        let conn_id = 1;

        manager.register_connection(conn_id).await;

        // Client streams should be odd
        let stream1 = manager
            .create_client_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();
        assert_eq!(stream1, 1);

        let stream2 = manager
            .create_client_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();
        assert_eq!(stream2, 3);

        // Server streams should be even
        let stream3 = manager
            .create_server_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();
        assert_eq!(stream3, 2);

        let stream4 = manager
            .create_server_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();
        assert_eq!(stream4, 4);
    }

    #[tokio::test]
    async fn test_stream_lifecycle() {
        let manager = StreamManager::new(StreamManagerConfig::default());
        let conn_id = 1;

        manager.register_connection(conn_id).await;

        let stream_id = manager
            .create_client_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();

        // Write data
        let written = manager
            .write_stream(conn_id, stream_id, b"hello")
            .await
            .unwrap();
        assert_eq!(written, 5);

        // Close stream
        manager.close_stream(conn_id, stream_id).await.unwrap();

        // Should be removed
        let status = manager.get_stream_status(conn_id, stream_id).await;
        assert!(status.is_none());
    }

    #[tokio::test]
    async fn test_frame_processing() {
        let manager = StreamManager::new(StreamManagerConfig::default());
        let conn_id = 1;

        manager.register_connection(conn_id).await;

        let stream_id = manager
            .create_client_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();

        // Send frame
        let frame = StreamFrame {
            stream_id,
            offset: 0,
            data: b"test data".to_vec(),
            fin: false,
        };

        manager.on_frame_received(conn_id, frame).await.unwrap();

        // Read data
        let mut buf = [0u8; 100];
        let read = manager
            .read_stream(conn_id, stream_id, &mut buf)
            .await
            .unwrap();
        assert_eq!(read, 9);
        assert_eq!(&buf[..9], b"test data");
    }

    #[tokio::test]
    async fn test_flow_control() {
        let config = StreamManagerConfig {
            initial_flow_control_window: 10, // Very small window
            ..Default::default()
        };
        let manager = StreamManager::new(config);
        let conn_id = 1;

        manager.register_connection(conn_id).await;

        let stream_id = manager
            .create_client_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();

        // First frame within window
        let frame1 = StreamFrame {
            stream_id,
            offset: 0,
            data: b"12345".to_vec(),
            fin: false,
        };
        manager.on_frame_received(conn_id, frame1).await.unwrap();

        // Second frame exceeds window
        let frame2 = StreamFrame {
            stream_id,
            offset: 5,
            data: b"123456".to_vec(), // 5 + 6 = 11 > 10
            fin: false,
        };
        let result = manager.on_frame_received(conn_id, frame2).await;
        assert!(matches!(result, Err(StreamError::FlowControlViolation)));
    }

    #[tokio::test]
    async fn test_max_streams_limit() {
        let config = StreamManagerConfig {
            max_bidi_streams: 2,
            ..Default::default()
        };
        let manager = StreamManager::new(config);
        let conn_id = 1;

        manager.register_connection(conn_id).await;

        // Create 2 streams (should succeed)
        manager
            .create_client_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();
        manager
            .create_client_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();

        // Third should fail
        let result = manager
            .create_client_stream(conn_id, StreamType::Bidirectional)
            .await;
        assert!(matches!(result, Err(StreamError::TooManyStreams)));
    }

    #[tokio::test]
    async fn test_stream_state_transitions() {
        let manager = StreamManager::new(StreamManagerConfig::default());
        let conn_id = 1;

        manager.register_connection(conn_id).await;

        let stream_id = manager
            .create_client_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();

        // Initial state: Open
        let status = manager.get_stream_status(conn_id, stream_id).await.unwrap();
        assert_eq!(status.state, StreamState::Open);

        // Send FIN frame -> HalfClosedRecv
        let frame = StreamFrame {
            stream_id,
            offset: 0,
            data: b"final".to_vec(),
            fin: true,
        };
        manager.on_frame_received(conn_id, frame).await.unwrap();

        let status = manager.get_stream_status(conn_id, stream_id).await.unwrap();
        assert_eq!(status.state, StreamState::HalfClosedRecv);
    }

    #[tokio::test]
    async fn test_list_streams() {
        let manager = StreamManager::new(StreamManagerConfig::default());
        let conn_id = 1;

        manager.register_connection(conn_id).await;

        let stream1 = manager
            .create_client_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();
        let stream2 = manager
            .create_server_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();

        let streams = manager.list_streams(conn_id).await;
        assert_eq!(streams.len(), 2);
        assert!(streams.contains(&stream1));
        assert!(streams.contains(&stream2));
    }

    #[tokio::test]
    async fn test_out_of_order_frames() {
        let manager = StreamManager::new(StreamManagerConfig::default());
        let conn_id = 1;

        manager.register_connection(conn_id).await;

        let stream_id = manager
            .create_client_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();

        // Send frame 2 first (out of order)
        let frame2 = StreamFrame {
            stream_id,
            offset: 5,
            data: b"world".to_vec(),
            fin: false,
        };
        manager.on_frame_received(conn_id, frame2).await.unwrap();

        // Data should not be readable yet (waiting for frame 1)
        let mut buf = [0u8; 100];
        let result = manager.read_stream(conn_id, stream_id, &mut buf).await;
        assert!(matches!(result, Err(StreamError::WouldBlock)));

        // Send frame 1 (fills the gap)
        let frame1 = StreamFrame {
            stream_id,
            offset: 0,
            data: b"hello".to_vec(),
            fin: false,
        };
        manager.on_frame_received(conn_id, frame1).await.unwrap();

        // Now both frames should be readable in order
        let read = manager
            .read_stream(conn_id, stream_id, &mut buf)
            .await
            .unwrap();
        assert_eq!(read, 10);
        assert_eq!(&buf[..10], b"helloworld");
    }

    #[tokio::test]
    async fn test_duplicate_frame_handling() {
        let manager = StreamManager::new(StreamManagerConfig::default());
        let conn_id = 1;

        manager.register_connection(conn_id).await;

        let stream_id = manager
            .create_client_stream(conn_id, StreamType::Bidirectional)
            .await
            .unwrap();

        // Send same frame twice
        let frame = StreamFrame {
            stream_id,
            offset: 0,
            data: b"test".to_vec(),
            fin: false,
        };

        manager
            .on_frame_received(conn_id, frame.clone())
            .await
            .unwrap();
        manager.on_frame_received(conn_id, frame).await.unwrap(); // Should be silently ignored

        // Should only have one copy of the data
        let mut buf = [0u8; 100];
        let read = manager
            .read_stream(conn_id, stream_id, &mut buf)
            .await
            .unwrap();
        assert_eq!(read, 4);
        assert_eq!(&buf[..4], b"test");
    }

    #[tokio::test]
    async fn test_iter_all_streams() {
        let manager = StreamManager::new(StreamManagerConfig::default());

        // Create multiple connections with streams
        manager.register_connection(1).await;
        manager.register_connection(2).await;

        manager
            .create_client_stream(1, StreamType::Bidirectional)
            .await
            .unwrap();
        manager
            .create_server_stream(1, StreamType::Bidirectional)
            .await
            .unwrap();
        manager
            .create_client_stream(2, StreamType::Bidirectional)
            .await
            .unwrap();

        let all_streams = manager.iter_all_streams().await;
        assert_eq!(all_streams.len(), 3);

        // Verify connection IDs are correct
        assert!(all_streams.iter().any(|s| s.connection_id == 1));
        assert!(all_streams.iter().any(|s| s.connection_id == 2));
    }

    #[tokio::test]
    async fn test_stream_index() {
        let manager = StreamManager::new(StreamManagerConfig::default());

        manager.register_connection(1).await;

        let stream1 = manager
            .create_client_stream(1, StreamType::Bidirectional)
            .await
            .unwrap();
        let stream2 = manager
            .create_server_stream(1, StreamType::Bidirectional)
            .await
            .unwrap();

        let index = manager.build_stream_index().await;

        // Both streams belong to connection 1
        assert_eq!(index.get(&stream1), Some(&1));
        assert_eq!(index.get(&stream2), Some(&1));
        
        // Verify stream IDs are different (client odd, server even)
        assert_ne!(stream1, stream2);
        assert_eq!(stream1 % 2, 1); // Client stream is odd
        assert_eq!(stream2 % 2, 0); // Server stream is even
    }
}
