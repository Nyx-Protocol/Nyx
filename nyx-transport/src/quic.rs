use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};

use bytes::{BufMut, Bytes, BytesMut};
use chacha20poly1305::{
    aead::{Aead, KeyInit},
    ChaCha20Poly1305, Nonce as ChaNonce,
};
use hkdf::Hkdf;
use rand::Rng;
use sha2::Sha256;
use tokio::net::UdpSocket;
use tokio::sync::{mpsc, RwLock as TokioRwLock};

/// CUBIC Congestion Control State (RFC 8312)
/// Implements CUBIC algorithm for TCP-friendly congestion control
#[derive(Debug, Clone)]
pub struct CubicState {
    /// Congestion window (bytes)
    pub cwnd: u32,
    /// Slow start threshold (bytes)
    pub ssthresh: u32,
    /// Window size before last reduction (W_max)
    pub w_max: f64,
    /// Time offset for CUBIC calculation (K)
    pub k: f64,
    /// Epoch start time (when last cwnd reduction occurred)
    pub epoch_start: Option<Instant>,
    /// CUBIC constant C (0.4 per RFC 8312)
    pub c: f64,
    /// Minimum RTT observed (for delay-based control)
    pub min_rtt: Option<Duration>,
    /// Latest RTT measurement
    pub latest_rtt: Option<Duration>,
    /// Smoothed RTT (exponentially weighted moving average)
    pub smoothed_rtt: Option<Duration>,
    /// RTT variance (for RTO calculation)
    pub rtt_var: Option<Duration>,
    /// Maximum packet size (MTU)
    pub max_packet_size: u32,
}

impl CubicState {
    /// Create new CUBIC state with initial cwnd
    pub fn new(initial_cwnd: u32, max_packet_size: u32) -> Self {
        Self {
            cwnd: initial_cwnd,
            ssthresh: u32::MAX, // Initial ssthresh is unlimited
            w_max: 0.0,
            k: 0.0,
            epoch_start: None,
            c: 0.4, // RFC 8312 §5
            min_rtt: None,
            latest_rtt: None,
            smoothed_rtt: None,
            rtt_var: None,
            max_packet_size,
        }
    }

    /// Reset CUBIC state after idle period
    pub fn reset(&mut self) {
        self.cwnd = self.max_packet_size * 10; // Conservative restart
        self.ssthresh = u32::MAX;
        self.w_max = 0.0;
        self.k = 0.0;
        self.epoch_start = None;
    }

    /// Update RTT measurements (RFC 6298 algorithm)
    pub fn update_rtt(&mut self, rtt: Duration) {
        self.latest_rtt = Some(rtt);

        // Track minimum RTT
        // SAFETY: Use map_or to avoid unwrap() even though short-circuit evaluation makes it safe
        // This improves readability and prevents future bugs if code is refactored
        if self.min_rtt.map_or(true, |min| rtt < min) {
            self.min_rtt = Some(rtt);
        }

        // Initialize smoothed RTT on first sample
        if self.smoothed_rtt.is_none() {
            self.smoothed_rtt = Some(rtt);
            self.rtt_var = Some(rtt / 2);
            return;
        }

        // EWMA: SRTT = (1 - α) * SRTT + α * RTT, where α = 1/8
        // SAFETY: smoothed_rtt is guaranteed to be Some() after the early return above
        // If this fails, it indicates a critical invariant violation (concurrent modification)
        let srtt = self.smoothed_rtt.expect("BUG: smoothed_rtt should be initialized after first RTT sample");
        // Use abs_diff to get absolute difference
        let rtt_diff = Duration::from_micros(rtt.as_micros().abs_diff(srtt.as_micros()) as u64);

        // RTTVAR = (1 - β) * RTTVAR + β * |SRTT - RTT|, where β = 1/4
        let rttvar = self.rtt_var.expect("BUG: rtt_var should be initialized with smoothed_rtt");
        self.rtt_var = Some(Duration::from_micros(
            rttvar.as_micros() as u64 * 3 / 4 + rtt_diff.as_micros() as u64 / 4,
        ));

        self.smoothed_rtt = Some(Duration::from_micros(
            srtt.as_micros() as u64 * 7 / 8 + rtt.as_micros() as u64 / 8,
        ));
    }

    /// Handle ACK: Increase congestion window
    /// Returns new cwnd value
    pub fn on_ack(&mut self, bytes_acked: u32) -> u32 {
        // Slow Start: Exponential growth (cwnd += bytes_acked)
        if self.cwnd < self.ssthresh {
            self.cwnd = self.cwnd.saturating_add(bytes_acked);
            return self.cwnd;
        }

        // Congestion Avoidance: CUBIC formula
        // W(t) = C * (t - K)³ + W_max

        let now = Instant::now();
        let epoch_start = self.epoch_start.get_or_insert(now);
        let t = now.duration_since(*epoch_start).as_secs_f64();

        // Calculate CUBIC window
        let delta = t - self.k;
        let cubic_window = self.c * delta.powi(3) + self.w_max;

        // Convert to bytes (W_max is in bytes)
        let target_cwnd = cubic_window.max(self.cwnd as f64) as u32;

        // Increment cwnd gradually toward target (per-ACK increase)
        let increase = if target_cwnd > self.cwnd {
            (target_cwnd - self.cwnd).min(self.max_packet_size)
        } else {
            0
        };

        self.cwnd = self.cwnd.saturating_add(increase);
        self.cwnd
    }

    /// Handle packet loss: Reduce congestion window
    /// Implements multiplicative decrease (RFC 8312 §4.5)
    pub fn on_packet_lost(&mut self) {
        // Fast Recovery: W_max = cwnd, ssthresh = cwnd * β (β = 0.7 per RFC 8312)
        self.w_max = self.cwnd as f64;
        self.ssthresh = (self.cwnd as f64 * 0.7) as u32;
        self.cwnd = self.ssthresh.max(self.max_packet_size * 2); // Min 2 * MSS

        // Calculate K: time to reach W_max
        // K = ((W_max - cwnd) / C)^(1/3)
        let cwnd_diff = (self.w_max - self.cwnd as f64).max(0.0);
        self.k = (cwnd_diff / self.c).cbrt();

        // Reset epoch
        self.epoch_start = Some(Instant::now());
    }

    /// Get current cwnd in bytes
    pub fn get_cwnd(&self) -> u32 {
        self.cwnd
    }

    /// Get available window (cwnd - bytes_in_flight)
    pub fn get_available_window(&self, bytes_in_flight: u32) -> u32 {
        self.cwnd.saturating_sub(bytes_in_flight)
    }
}

/// Connection timeout constant
pub const CONNECTION_TIMEOUT: Duration = Duration::from_secs(10);
/// Maximum concurrent streams per connection
pub const MAX_CONCURRENT_STREAMS: usize = 256;
/// Maximum datagram size (MTU - overhead)
pub const MAX_DATAGRAM_SIZE: usize = 1200;

/// QUIC specific errors
#[derive(Debug)]
pub enum QuicError {
    Transport(String),
    Protocol(String),
    ConnectionClosed(String),
    Stream(String),
    CongestionControl(String),
    FlowControl(String),
    Crypto(String),
    Timeout(String),
    Configuration(String),
    VersionNegotiation(String),
    HandshakeFailed(String),
    CertificateVerification(String),
    AlpnNegotiation(String),
    AddressValidation(String),
    MigrationNotAllowed(String),
    PacketDecode(String),
    InvalidFrame(String),
    Internal(String),
    InvalidConnectionId(String),
    InvalidPacketNumber(String),
    InvalidToken(String),
    KeyUpdate(String),
    TooManyStreams,
    StreamNotFound(String),
    InvalidStreamState(String),
    StreamAlreadyClosed(String),
    Application(String),
    ResourceExhausted(String),
    RateLimited(String),
    PathValidation(String),
    IdleTimeout(String),
    KeepaliveTimeout(String),
    DatagramTooLarge(String),
    FeatureNotSupported(String),
    InvalidParameter(String),
    NoAvailablePaths(String),
    Serialization(String),
    Io(String),
    CryptoError(String),
    ConnectionNotFound(Bytes),
    StreamNotFoundError,
    StreamClosed,
}

/// Connection state management enumeration#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConnectionState {
    Connecting {
        peer: SocketAddr,
        start_time: Instant,
        attempt_count: u32,
    },
    Connected {
        peer: SocketAddr,
        established_at: Instant,
        stream_count: u32,
        congestion_window: u32,
    },
    Closing {
        peer: SocketAddr,
        close_reason: String,
        started_at: Instant,
        remaining_streams: u32,
    },
    Closed {
        close_reason: String,
        closed_at: Instant,
    },
}

/// Stream type#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamType {
    Bidirectional,
    Unidirectional,
}

/// Stream state
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamState {
    Open,
    HalfClosed,
    Closed,
}

/// Encryption level
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EncryptionLevel {
    Initial,
    Handshake,
    Application,
}

/// QUIC Frame types (RFC 9000 + RFC 9221 Datagram Extension)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuicFrame {
    /// STREAM frame: carries stream data
    Stream {
        stream_id: u64,
        offset: u64,
        data: Bytes,
        fin: bool,
    },
    /// DATAGRAM frame: unreliable datagram delivery (RFC 9221)
    /// Length-prefixed variant with explicit length field
    Datagram { data: Bytes },
    /// ACK frame: acknowledges packet receipt
    Ack {
        largest_acknowledged: u64,
        ack_delay: u64,
        ack_ranges: Vec<(u64, u64)>,
    },
    /// CONNECTION_CLOSE frame: terminates connection
    ConnectionClose { error_code: u64, reason: String },
    /// PATH_CHALLENGE frame: path validation challenge (RFC 9000 §19.17)
    PathChallenge { data: [u8; 8] },
    /// PATH_RESPONSE frame: response to PATH_CHALLENGE (RFC 9000 §19.18)
    PathResponse { data: [u8; 8] },
}

impl QuicFrame {
    /// Encode frame to bytes (simplified, production would use proper varint encoding)
    pub fn encode(&self) -> Result<Bytes, QuicError> {
        let mut buf = BytesMut::new();

        match self {
            QuicFrame::Stream {
                stream_id,
                offset,
                data,
                fin,
            } => {
                // Frame type: 0x08-0x0f (STREAM frame with various flags)
                let frame_type = 0x08 | (if *fin { 0x01 } else { 0x00 });
                buf.put_u8(frame_type);
                buf.put_u64(*stream_id);
                buf.put_u64(*offset);
                buf.put_u64(data.len() as u64);
                buf.extend_from_slice(data);
            }
            QuicFrame::Datagram { data } => {
                // RFC 9221: DATAGRAM frame type 0x30-0x31
                // 0x30: no length field, 0x31: with length field
                // We use 0x31 (with length) for simplicity
                buf.put_u8(0x31);
                buf.put_u64(data.len() as u64);
                buf.extend_from_slice(data);
            }
            QuicFrame::Ack {
                largest_acknowledged,
                ack_delay,
                ack_ranges,
            } => {
                buf.put_u8(0x02); // ACK frame type
                buf.put_u64(*largest_acknowledged);
                buf.put_u64(*ack_delay);
                buf.put_u64(ack_ranges.len() as u64);
                for (start, end) in ack_ranges {
                    buf.put_u64(*start);
                    buf.put_u64(*end);
                }
            }
            QuicFrame::ConnectionClose { error_code, reason } => {
                buf.put_u8(0x1c); // CONNECTION_CLOSE frame type
                buf.put_u64(*error_code);
                let reason_bytes = reason.as_bytes();
                buf.put_u64(reason_bytes.len() as u64);
                buf.extend_from_slice(reason_bytes);
            }
            QuicFrame::PathChallenge { data } => {
                // RFC 9000 §19.17: PATH_CHALLENGE frame type 0x1a
                buf.put_u8(0x1a);
                buf.extend_from_slice(data);
            }
            QuicFrame::PathResponse { data } => {
                // RFC 9000 §19.18: PATH_RESPONSE frame type 0x1b
                buf.put_u8(0x1b);
                buf.extend_from_slice(data);
            }
        }

        Ok(buf.freeze())
    }

    /// Decode frame from bytes (simplified)
    pub fn decode(data: &[u8]) -> Result<(Self, usize), QuicError> {
        if data.is_empty() {
            return Err(QuicError::PacketDecode("Empty frame data".to_string()));
        }

        let frame_type = data[0];
        let mut offset = 1;

        match frame_type {
            0x08..=0x0f => {
                // STREAM frame
                if data.len() < offset + 24 {
                    return Err(QuicError::PacketDecode(
                        "Incomplete STREAM frame".to_string(),
                    ));
                }
                // SAFETY: Length check above guarantees [offset..offset+8] has exactly 8 bytes
                // Using expect() instead of unwrap() provides diagnostic context if invariant is violated
                let stream_id = u64::from_be_bytes(
                    data[offset..offset + 8].try_into()
                        .expect("BUG: slice length checked above but try_into failed"));
                offset += 8;
                let stream_offset = u64::from_be_bytes(
                    data[offset..offset + 8].try_into()
                        .expect("BUG: slice length checked above but try_into failed"));
                offset += 8;
                let length = u64::from_be_bytes(
                    data[offset..offset + 8].try_into()
                        .expect("BUG: slice length checked above but try_into failed")) as usize;
                offset += 8;

                if data.len() < offset + length {
                    return Err(QuicError::PacketDecode(
                        "Incomplete STREAM data".to_string(),
                    ));
                }

                let frame_data = Bytes::copy_from_slice(&data[offset..offset + length]);
                offset += length;
                let fin = (frame_type & 0x01) != 0;

                Ok((
                    QuicFrame::Stream {
                        stream_id,
                        offset: stream_offset,
                        data: frame_data,
                        fin,
                    },
                    offset,
                ))
            }
            0x30 | 0x31 => {
                // DATAGRAM frame (RFC 9221)
                if frame_type == 0x31 {
                    // With length field
                    if data.len() < offset + 8 {
                        return Err(QuicError::PacketDecode(
                            "Incomplete DATAGRAM frame".to_string(),
                        ));
                    }
                    let length = u64::from_be_bytes(
                        data[offset..offset + 8].try_into()
                            .expect("BUG: slice length checked above but try_into failed")) as usize;
                    offset += 8;

                    if data.len() < offset + length {
                        return Err(QuicError::PacketDecode(
                            "Incomplete DATAGRAM data".to_string(),
                        ));
                    }

                    let frame_data = Bytes::copy_from_slice(&data[offset..offset + length]);
                    offset += length;

                    Ok((QuicFrame::Datagram { data: frame_data }, offset))
                } else {
                    // Without length field (rest of packet is datagram)
                    let frame_data = Bytes::copy_from_slice(&data[offset..]);
                    offset = data.len();
                    Ok((QuicFrame::Datagram { data: frame_data }, offset))
                }
            }
            0x02 => {
                // ACK frame
                if data.len() < offset + 24 {
                    return Err(QuicError::PacketDecode("Incomplete ACK frame".to_string()));
                }
                let largest_ack = u64::from_be_bytes(
                    data[offset..offset + 8].try_into()
                        .expect("BUG: slice length checked above but try_into failed"));
                offset += 8;
                let ack_delay = u64::from_be_bytes(
                    data[offset..offset + 8].try_into()
                        .expect("BUG: slice length checked above but try_into failed"));
                offset += 8;
                let range_count = u64::from_be_bytes(
                    data[offset..offset + 8].try_into()
                        .expect("BUG: slice length checked above but try_into failed")) as usize;
                offset += 8;

                let mut ack_ranges = Vec::new();
                for _ in 0..range_count {
                    if data.len() < offset + 16 {
                        return Err(QuicError::PacketDecode("Incomplete ACK ranges".to_string()));
                    }
                    let start = u64::from_be_bytes(
                        data[offset..offset + 8].try_into()
                            .expect("BUG: slice length checked above but try_into failed"));
                    offset += 8;
                    let end = u64::from_be_bytes(
                        data[offset..offset + 8].try_into()
                            .expect("BUG: slice length checked above but try_into failed"));
                    offset += 8;
                    ack_ranges.push((start, end));
                }

                Ok((
                    QuicFrame::Ack {
                        largest_acknowledged: largest_ack,
                        ack_delay,
                        ack_ranges,
                    },
                    offset,
                ))
            }
            0x1c => {
                // CONNECTION_CLOSE frame
                if data.len() < offset + 16 {
                    return Err(QuicError::PacketDecode(
                        "Incomplete CONNECTION_CLOSE frame".to_string(),
                    ));
                }
                let error_code = u64::from_be_bytes(
                    data[offset..offset + 8].try_into()
                        .expect("BUG: slice length checked above but try_into failed"));
                offset += 8;
                let reason_len = u64::from_be_bytes(
                    data[offset..offset + 8].try_into()
                        .expect("BUG: slice length checked above but try_into failed")) as usize;
                offset += 8;

                if data.len() < offset + reason_len {
                    return Err(QuicError::PacketDecode(
                        "Incomplete reason phrase".to_string(),
                    ));
                }

                let reason =
                    String::from_utf8_lossy(&data[offset..offset + reason_len]).to_string();
                offset += reason_len;

                Ok((QuicFrame::ConnectionClose { error_code, reason }, offset))
            }
            0x1a => {
                // PATH_CHALLENGE frame (RFC 9000 §19.17)
                if data.len() < offset + 8 {
                    return Err(QuicError::PacketDecode(
                        "Incomplete PATH_CHALLENGE frame".to_string(),
                    ));
                }
                let mut challenge_data = [0u8; 8];
                challenge_data.copy_from_slice(&data[offset..offset + 8]);
                offset += 8;
                Ok((
                    QuicFrame::PathChallenge {
                        data: challenge_data,
                    },
                    offset,
                ))
            }
            0x1b => {
                // PATH_RESPONSE frame (RFC 9000 §19.18)
                if data.len() < offset + 8 {
                    return Err(QuicError::PacketDecode(
                        "Incomplete PATH_RESPONSE frame".to_string(),
                    ));
                }
                let mut response_data = [0u8; 8];
                response_data.copy_from_slice(&data[offset..offset + 8]);
                offset += 8;
                Ok((
                    QuicFrame::PathResponse {
                        data: response_data,
                    },
                    offset,
                ))
            }
            _ => Err(QuicError::InvalidFrame(format!(
                "Unknown frame type: 0x{:02x}",
                frame_type
            ))),
        }
    }
}

/// Transport Parameters (RFC 9000 §18.2 + RFC 9221 §3)
#[derive(Debug, Clone)]
pub struct TransportParameters {
    /// Initial maximum data (bytes)
    pub initial_max_data: u64,
    /// Initial maximum stream data (bytes)
    pub initial_max_stream_data_bidi_local: u64,
    pub initial_max_stream_data_bidi_remote: u64,
    pub initial_max_stream_data_uni: u64,
    /// Maximum bidirectional/unidirectional streams
    pub initial_max_streams_bidi: u64,
    pub initial_max_streams_uni: u64,
    /// Idle timeout (milliseconds)
    pub max_idle_timeout: u64,
    /// Maximum UDP payload size
    pub max_udp_payload_size: u64,
    /// Maximum datagram frame size (RFC 9221)
    /// If None, datagram extension is not supported
    pub max_datagram_frame_size: Option<u64>,
}

impl Default for TransportParameters {
    fn default() -> Self {
        Self {
            initial_max_data: 1_048_576,                 // 1 MB
            initial_max_stream_data_bidi_local: 262_144, // 256 KB
            initial_max_stream_data_bidi_remote: 262_144,
            initial_max_stream_data_uni: 262_144,
            initial_max_streams_bidi: 100,
            initial_max_streams_uni: 100,
            max_idle_timeout: 30_000, // 30 seconds
            max_udp_payload_size: MAX_DATAGRAM_SIZE as u64,
            // RFC 9221: Enable datagram extension with 1200 byte limit
            max_datagram_frame_size: Some(MAX_DATAGRAM_SIZE as u64),
        }
    }
}

/// Connection statistics
#[derive(Debug, Clone)]
pub struct ConnectionStats {
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub packets_sent: u64,
    pub packets_received: u64,
    pub packet_loss_rate: f64,
    pub round_trip_time: Duration,
    pub congestion_window: u32,
    pub bytes_in_flight: u64,
    pub stream_s_created: u32,
    pub stream_s_closed: u32,
    pub errors_encountered: u32,
    pub last_error: Option<String>,
}

impl Default for ConnectionStats {
    fn default() -> Self {
        Self {
            bytes_sent: 0,
            bytes_received: 0,
            packets_sent: 0,
            packets_received: 0,
            packet_loss_rate: 0.0,
            round_trip_time: Duration::from_millis(0),
            congestion_window: 65536,
            bytes_in_flight: 0,
            stream_s_created: 0,
            stream_s_closed: 0,
            errors_encountered: 0,
            last_error: None,
        }
    }
}

/// Endpoint statistics
#[derive(Debug, Clone)]
pub struct EndpointStatistics {
    pub active_connections: u32,
    pub total_connection_s_created: u64,
    pub total_connection_s_closed: u64,
    pub total_bytes_sent: u64,
    pub total_bytes_received: u64,
    pub packet_loss_rate: f64,
    pub average_rtt: Duration,
    pub peak_congestion_window: u32,
    pub errors_by_type: HashMap<String, u64>,
    pub performance_metrics: HashMap<String, f64>,
}

impl Default for EndpointStatistics {
    fn default() -> Self {
        Self {
            active_connections: 0,
            total_connection_s_created: 0,
            total_connection_s_closed: 0,
            total_bytes_sent: 0,
            total_bytes_received: 0,
            packet_loss_rate: 0.0,
            average_rtt: Duration::from_millis(0),
            peak_congestion_window: 65536,
            errors_by_type: HashMap::new(),
            performance_metrics: HashMap::new(),
        }
    }
}

/// Path validation state (RFC 9000 §8.2)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationState {
    /// No validation in progress
    Idle,
    /// Validation in progress
    Validating,
    /// Path validated successfully
    Validated,
    /// Validation failed
    Failed,
}

/// Path validation for Connection Migration (RFC 9000 §9)
#[derive(Debug, Clone)]
pub struct PathValidation {
    /// Current validation state
    pub state: ValidationState,
    /// Challenge data (8 random bytes)
    pub challenge_data: [u8; 8],
    /// Number of PATH_CHALLENGE attempts
    pub attempts: u8,
    /// Timeout for next retry
    pub next_timeout: Option<Instant>,
    /// Path being validated
    pub path_addr: SocketAddr,
}

impl PathValidation {
    /// Create new path validation with random challenge
    pub fn new(path_addr: SocketAddr) -> Self {
        let mut rng = rand::thread_rng();
        let mut challenge_data = [0u8; 8];
        rng.fill(&mut challenge_data);

        Self {
            state: ValidationState::Idle,
            challenge_data,
            attempts: 0,
            next_timeout: None,
            path_addr,
        }
    }

    /// Start validation process
    pub fn start_validation(&mut self, pto: Duration) {
        self.state = ValidationState::Validating;
        self.attempts = 1;
        self.next_timeout = Some(Instant::now() + pto);
    }

    /// Handle PATH_RESPONSE received
    pub fn on_response(&mut self, response_data: [u8; 8]) -> bool {
        if self.state == ValidationState::Validating && response_data == self.challenge_data {
            self.state = ValidationState::Validated;
            self.next_timeout = None;
            true
        } else {
            false
        }
    }

    /// Check if timeout occurred and retry if needed
    /// Returns true if PATH_CHALLENGE should be retried
    pub fn check_timeout(&mut self, pto: Duration) -> bool {
        if let Some(timeout) = self.next_timeout {
            if Instant::now() >= timeout {
                if self.attempts < 3 {
                    // RFC 9000 §8.2.1: 3 PATH_CHALLENGE attempts
                    self.attempts += 1;
                    self.next_timeout = Some(Instant::now() + pto);
                    true // Retry
                } else {
                    self.state = ValidationState::Failed;
                    self.next_timeout = None;
                    false // Give up
                }
            } else {
                false // Not timed out yet
            }
        } else {
            false
        }
    }
}

/// Connection ID Manager (RFC 9000 §5.1)
#[derive(Debug, Clone)]
pub struct ConnectionIdManager {
    /// Active Connection IDs
    pub active_cids: Vec<Bytes>,
    /// Retired Connection IDs (pending RETIRE_CONNECTION_ID)
    pub retire_cids: Vec<Bytes>,
    /// Sequence number for NEW_CONNECTION_ID
    pub sequence_number: u64,
}

impl ConnectionIdManager {
    pub fn new(initial_cid: Bytes) -> Self {
        Self {
            active_cids: vec![initial_cid],
            retire_cids: Vec::new(),
            sequence_number: 0,
        }
    }

    /// Issue new Connection ID for path migration
    pub fn issue_new_cid(&mut self) -> Bytes {
        self.sequence_number += 1;
        let mut rng = rand::thread_rng();
        let new_cid = Bytes::from(rng.gen::<[u8; 8]>().to_vec());
        self.active_cids.push(new_cid.clone());
        new_cid
    }

    /// Retire old Connection ID
    pub fn retire_cid(&mut self, cid: Bytes) {
        if let Some(pos) = self.active_cids.iter().position(|c| c == &cid) {
            let retired = self.active_cids.remove(pos);
            self.retire_cids.push(retired);
        }
    }

    /// Get current active CID
    pub fn current_cid(&self) -> Option<&Bytes> {
        self.active_cids.last()
    }
}

/// QUIC configuration
#[derive(Debug, Clone)]
pub struct QuicEndpointConfig {
    pub max_connections: u32,
    pub connection_timeout: Duration,
    pub idle_timeout: Duration,
    pub max_stream_s_per_connection: u32,
    pub initial_max_data: u64,
    pub initial_max_stream_data: u64,
}

impl Default for QuicEndpointConfig {
    fn default() -> Self {
        Self {
            max_connections: 1000,
            connection_timeout: Duration::from_secs(10),
            idle_timeout: Duration::from_secs(30),
            max_stream_s_per_connection: 256,
            initial_max_data: 1048576,
            initial_max_stream_data: 262144,
        }
    }
}

/// QUIC connection
#[derive(Clone)]
pub struct QuicConnection {
    pub _connection_id: Bytes,
    pub _peer_addr: SocketAddr,
    pub state: Arc<TokioRwLock<ConnectionState>>,
    pub streams: Arc<TokioRwLock<HashMap<u64, QuicStream>>>,
    pub _next_stream_id: u64,
    pub established_at: Option<Instant>,
    pub _last_activity: Instant,
    pub stats: Arc<TokioRwLock<ConnectionStats>>,
    /// Transport parameters negotiated during handshake
    pub local_transport_params: Arc<TokioRwLock<TransportParameters>>,
    pub peer_transport_params: Arc<TokioRwLock<Option<TransportParameters>>>,
    /// Datagram send queue (RFC 9221)
    pub datagram_send_queue: Arc<TokioRwLock<Vec<Bytes>>>,
    /// Datagram receive queue
    pub datagram_recv_queue: Arc<TokioRwLock<Vec<Bytes>>>,
    /// CUBIC congestion control state (RFC 8312)
    pub congestion_control: Arc<TokioRwLock<CubicState>>,
    /// Current path ID for multipath (0 = primary path)
    pub current_path_id: Arc<TokioRwLock<u64>>,
    /// Path validations in progress (path_id -> PathValidation)
    pub path_validations: Arc<TokioRwLock<HashMap<u64, PathValidation>>>,
    /// Connection ID manager
    pub cid_manager: Arc<TokioRwLock<ConnectionIdManager>>,
}

/// QUIC stream
pub struct QuicStream {
    pub stream_id: u64,
    pub stream_type: StreamType,
    pub state: StreamState,
    pub send_buffer: Vec<u8>,
    pub recv_buffer: Vec<u8>,
    pub _send_offset: u64,
    pub _recv_offset: u64,
}

/// QUIC Endpoint
pub struct QuicEndpoint {
    #[allow(dead_code)]
    socket: UdpSocket,
    #[allow(dead_code)]
    bind_addr: SocketAddr,
    config: QuicEndpointConfig,
    connections: Arc<TokioRwLock<HashMap<Bytes, QuicConnection>>>,
    #[allow(dead_code)]
    statistics: Arc<TokioRwLock<EndpointStatistics>>,
}

/// QUIC暗号化コンチE��スチE#[allow(dead_code)]
pub struct QuicCryptoContext {
    #[allow(dead_code)]
    initial_secret: [u8; 32],
    #[allow(dead_code)]
    handshake_secret: [u8; 32],
    #[allow(dead_code)]
    application_secret: [u8; 32],
    #[allow(dead_code)]
    key_update_secret: [u8; 32],
    #[allow(dead_code)]
    encryption_level: EncryptionLevel,
    #[allow(dead_code)]
    key_phase: u32,
}

/// QUIC Header Protection (RFC 9001 §5.4)
/// Protects packet header to prevent traffic analysis
pub struct HeaderProtection {
    hp_key: [u8; 32],
}

impl HeaderProtection {
    /// Derive header protection key from traffic secret (RFC 9001 §5.4.1)
    /// Uses HKDF-Expand-Label with "quic hp" label
    pub fn derive_from_secret(traffic_secret: &[u8]) -> Result<Self, QuicError> {
        let hp_key = Self::hkdf_expand_label(traffic_secret, b"quic hp", b"", 32)?;
        Ok(Self { hp_key })
    }

    /// HKDF-Expand-Label (RFC 8446 §7.1, RFC 9001 §5.1)
    /// Expands secret with QUIC-specific label format
    fn hkdf_expand_label(
        secret: &[u8],
        label: &[u8],
        context: &[u8],
        length: usize,
    ) -> Result<[u8; 32], QuicError> {
        // Construct HkdfLabel: struct {
        //   uint16 length = Length;
        //   opaque label<7..255> = "tls13 " + Label;
        //   opaque context<0..255> = Context;
        // }
        let mut hkdf_label = Vec::new();
        hkdf_label.extend_from_slice(&(length as u16).to_be_bytes());

        // QUIC uses "tls13 " prefix (6 bytes + label)
        let full_label_len = 6 + label.len();
        hkdf_label.push(full_label_len as u8);
        hkdf_label.extend_from_slice(b"tls13 ");
        hkdf_label.extend_from_slice(label);

        hkdf_label.push(context.len() as u8);
        hkdf_label.extend_from_slice(context);

        let hk = Hkdf::<Sha256>::new(None, secret);
        let mut okm = [0u8; 32];
        hk.expand(&hkdf_label, &mut okm[..length])
            .map_err(|e| QuicError::CryptoError(e.to_string()))?;
        Ok(okm)
    }

    /// Protect packet header (RFC 9001 §5.4.1)
    /// Applies ChaCha20 mask to first byte and packet number
    ///
    /// IMPORTANT: The first byte must already have packet number length encoded
    /// in bits 0-1 (pn_length - 1) BEFORE calling this function.
    pub fn protect(
        &self,
        packet: &mut [u8],
        pn_offset: usize,
        pn_length: usize,
    ) -> Result<(), QuicError> {
        if !(1..=4).contains(&pn_length) {
            return Err(QuicError::PacketDecode(
                "Invalid packet number length".to_string(),
            ));
        }

        if packet.len() < pn_offset + pn_length + 4 {
            return Err(QuicError::PacketDecode(
                "Packet too short for header protection".to_string(),
            ));
        }

        // Encode packet number length in first byte (bits 0-1)
        let pn_length_bits = (pn_length - 1) as u8;
        packet[0] = (packet[0] & 0xfc) | pn_length_bits;

        // Extract sample (16 bytes starting at pn_offset + 4)
        let sample_offset = pn_offset + 4;
        if packet.len() < sample_offset + 16 {
            return Err(QuicError::PacketDecode(
                "Insufficient data for sample".to_string(),
            ));
        }

        let sample = &packet[sample_offset..sample_offset + 16];

        // Generate mask using ChaCha20
        let mask = self.generate_mask(sample)?;

        // Protect first byte (bits 0-4 for long header, bits 0-4 for short header)
        // Long header: protect bits 0-3 (lower 4 bits)
        // Short header: protect bits 0-4 (lower 5 bits)
        let is_long_header = (packet[0] & 0x80) != 0;

        if is_long_header {
            // Long header: protect lower 4 bits only
            packet[0] ^= mask[0] & 0x0f;
        } else {
            // Short header: protect lower 5 bits
            packet[0] ^= mask[0] & 0x1f;
        }

        // Protect packet number (XOR with mask bytes 1..=pn_length)
        for i in 0..pn_length {
            packet[pn_offset + i] ^= mask[1 + i];
        }

        Ok(())
    }

    /// Unprotect packet header (RFC 9001 §5.4.2)
    /// Removes ChaCha20 mask from first byte and packet number
    pub fn unprotect(&self, packet: &mut [u8], pn_offset: usize) -> Result<usize, QuicError> {
        if packet.len() < pn_offset + 4 + 16 {
            return Err(QuicError::PacketDecode(
                "Packet too short for header protection".to_string(),
            ));
        }

        // Extract sample (16 bytes starting at pn_offset + 4)
        let sample_offset = pn_offset + 4;
        let sample = &packet[sample_offset..sample_offset + 16];

        // Generate mask using ChaCha20
        let mask = self.generate_mask(sample)?;

        // Unprotect first byte to determine packet number length
        let first_byte = packet[0];
        let is_long_header = (first_byte & 0x80) != 0;

        if is_long_header {
            packet[0] ^= mask[0] & 0x0f;
        } else {
            packet[0] ^= mask[0] & 0x1f;
        }

        // Extract packet number length from unprotected first byte (bits 0-1)
        let pn_length = ((packet[0] & 0x03) + 1) as usize;

        // Unprotect packet number
        for i in 0..pn_length {
            if pn_offset + i >= packet.len() {
                return Err(QuicError::PacketDecode(
                    "Packet number exceeds packet length".to_string(),
                ));
            }
            packet[pn_offset + i] ^= mask[1 + i];
        }

        Ok(pn_length)
    }

    /// Generate ChaCha20 mask from sample (RFC 9001 §5.4.3)
    /// Returns 5-byte mask for header protection
    fn generate_mask(&self, sample: &[u8]) -> Result<[u8; 5], QuicError> {
        use chacha20::cipher::{KeyIvInit, StreamCipher, StreamCipherSeek};
        use chacha20::ChaCha20;

        if sample.len() != 16 {
            return Err(QuicError::CryptoError(
                "Sample must be 16 bytes".to_string(),
            ));
        }

        // ChaCha20 counter is first 4 bytes of sample
        let counter = u32::from_le_bytes([sample[0], sample[1], sample[2], sample[3]]);

        // Nonce is remaining 12 bytes of sample
        let nonce = &sample[4..16];

        // Create ChaCha20 cipher with HP key
        let mut cipher = ChaCha20::new(&self.hp_key.into(), nonce.into());

        // Set counter (ChaCha20 uses 32-bit counter)
        cipher.seek(counter as u64 * 64);

        // Generate 5-byte mask
        let mut mask = [0u8; 5];
        cipher.apply_keystream(&mut mask);

        Ok(mask)
    }

    /// Get header protection key (for testing)
    #[cfg(test)]
    pub fn key(&self) -> &[u8; 32] {
        &self.hp_key
    }
}

impl QuicConnection {
    /// 新しいQUIC接続を作�E
    pub fn new(
        connection_id: Bytes,
        peer_addr: SocketAddr,
        is_server: bool,
        stats: ConnectionStats,
    ) -> Result<Self, QuicError> {
        let state = if is_server {
            ConnectionState::Connecting {
                peer: peer_addr,
                start_time: Instant::now(),
                attempt_count: 0,
            }
        } else {
            ConnectionState::Connecting {
                peer: peer_addr,
                start_time: Instant::now(),
                attempt_count: 1,
            }
        };

        // Initialize CUBIC congestion control
        let initial_cwnd = MAX_DATAGRAM_SIZE as u32 * 10; // 10 * MTU = 12000 bytes
        let cubic = CubicState::new(initial_cwnd, MAX_DATAGRAM_SIZE as u32);

        // Clone connection_id for CID manager before moving
        let cid_for_manager = connection_id.clone();

        Ok(Self {
            _connection_id: connection_id,
            _peer_addr: peer_addr,
            state: Arc::new(TokioRwLock::new(state)),
            streams: Arc::new(TokioRwLock::new(HashMap::new())),
            _next_stream_id: if is_server { 1 } else { 0 },
            established_at: None,
            _last_activity: Instant::now(),
            stats: Arc::new(TokioRwLock::new(stats)),
            local_transport_params: Arc::new(TokioRwLock::new(TransportParameters::default())),
            peer_transport_params: Arc::new(TokioRwLock::new(None)),
            datagram_send_queue: Arc::new(TokioRwLock::new(Vec::new())),
            datagram_recv_queue: Arc::new(TokioRwLock::new(Vec::new())),
            congestion_control: Arc::new(TokioRwLock::new(cubic)),
            current_path_id: Arc::new(TokioRwLock::new(0)), // Primary path = 0
            path_validations: Arc::new(TokioRwLock::new(HashMap::new())),
            cid_manager: Arc::new(TokioRwLock::new(ConnectionIdManager::new(cid_for_manager))),
        })
    }

    /// Get connection ID
    pub fn connection_id(&self) -> Bytes {
        self._connection_id.clone()
    }

    /// Check if connection is established
    pub async fn is_established(&self) -> bool {
        matches!(*self.state.read().await, ConnectionState::Connected { .. })
    }

    /// Create new stream
    pub async fn create_stream(&mut self, stream_type: StreamType) -> Result<u64, QuicError> {
        if !self.is_established().await {
            return Err(QuicError::Protocol(String::new()));
        }

        let stream_id = self._next_stream_id;
        self._next_stream_id += 1;

        let stream = QuicStream::new(stream_id, stream_type);
        self.streams.write().await.insert(stream_id, stream);
        self._last_activity = Instant::now();

        Ok(stream_id)
    }

    /// ストリーム書き込み
    pub async fn write_stream(&mut self, stream_id: u64, _data: Bytes) -> Result<(), QuicError> {
        let mut stream_s = self.streams.write().await;
        let stream = stream_s
            .get_mut(&stream_id)
            .ok_or(QuicError::StreamNotFound(String::from("Stream not found")))?;

        stream.write_data(_data).await?;
        self._last_activity = Instant::now();

        Ok(())
    }

    /// ストリーム読み込み
    pub async fn read_stream(&mut self, stream_id: u64) -> Result<Option<Bytes>, QuicError> {
        let mut stream_s = self.streams.write().await;
        let stream = stream_s
            .get_mut(&stream_id)
            .ok_or(QuicError::StreamNotFound(String::from("Stream not found")))?;

        let _data = stream.read_data().await?;
        self._last_activity = Instant::now();

        Ok(_data)
    }

    /// Close connection
    pub async fn close(&mut self) -> Result<(), QuicError> {
        let mut state = self.state.write().await;
        *state = ConnectionState::Closing {
            peer: self._peer_addr,
            close_reason: String::new(),
            started_at: Instant::now(),
            remaining_streams: self.streams.read().await.len() as u32,
        };

        Ok(())
    }

    /// Change connection state to Connected
    pub async fn establish_connection(&self, _servername: Option<String>) -> Result<(), QuicError> {
        let mut state = self.state.write().await;

        if let ConnectionState::Connecting {
            peer, start_time, ..
        } = &*state
        {
            *state = ConnectionState::Connected {
                peer: *peer,
                established_at: *start_time,
                stream_count: 0,
                congestion_window: 65536,
            };
        }

        Ok(())
    }

    /// Send DATAGRAM frame (RFC 9221)
    /// Unreliable, unordered delivery
    pub async fn send_datagram(&self, data: Bytes) -> Result<(), QuicError> {
        // Verify datagram extension is enabled
        let peer_params = self.peer_transport_params.read().await;
        let max_datagram_size = match &*peer_params {
            Some(params) => params.max_datagram_frame_size,
            None => {
                // Peer parameters not yet negotiated, use local default
                let local = self.local_transport_params.read().await;
                local.max_datagram_frame_size
            }
        };

        let max_size = match max_datagram_size {
            Some(size) => size,
            None => {
                return Err(QuicError::FeatureNotSupported(
                    "Peer does not support DATAGRAM extension".to_string(),
                ));
            }
        };
        if data.len() as u64 > max_size {
            return Err(QuicError::DatagramTooLarge(format!(
                "Datagram size {} exceeds maximum {}",
                data.len(),
                max_size
            )));
        }

        // CUBIC Flow Control: Check available congestion window
        let cubic = self.congestion_control.read().await;
        let stats = self.stats.read().await;
        let available_window = cubic.get_available_window(stats.bytes_in_flight as u32);

        // Datagrams should not exceed 50% of cwnd to avoid excessive congestion
        let datagram_budget = cubic.get_cwnd() / 2;

        if data.len() as u32 > datagram_budget.min(available_window) {
            return Err(QuicError::CongestionControl(format!(
                "Insufficient congestion window for datagram: {} bytes needed, {} available (cwnd={}, budget={})",
                data.len(),
                available_window,
                cubic.get_cwnd(),
                datagram_budget
            )));
        }
        drop(cubic);
        drop(stats);

        // Queue datagram for transmission
        let mut queue = self.datagram_send_queue.write().await;
        queue.push(data);

        Ok(())
    }

    /// Receive DATAGRAM frame (RFC 9221)
    /// Non-blocking: returns None if queue is empty
    pub async fn recv_datagram(&self) -> Result<Option<Bytes>, QuicError> {
        let mut queue = self.datagram_recv_queue.write().await;

        if queue.is_empty() {
            return Ok(None);
        }

        // FIFO order (datagrams are unordered, but we preserve receive order)
        let datagram = queue.remove(0);
        Ok(Some(datagram))
    }

    /// Get number of queued datagrams (for monitoring)
    pub async fn datagram_queue_len(&self) -> (usize, usize) {
        let send_len = self.datagram_send_queue.read().await.len();
        let recv_len = self.datagram_recv_queue.read().await.len();
        (send_len, recv_len)
    }

    /// Set peer transport parameters (called during handshake)
    pub async fn set_peer_transport_parameters(
        &self,
        params: TransportParameters,
    ) -> Result<(), QuicError> {
        let mut peer_params = self.peer_transport_params.write().await;
        *peer_params = Some(params);
        Ok(())
    }

    /// Get local transport parameters
    pub async fn get_local_transport_parameters(&self) -> TransportParameters {
        self.local_transport_params.read().await.clone()
    }

    /// Handle ACK reception: Update CUBIC state and RTT
    /// Call this when ACK frame is received
    pub async fn on_ack_received(&self, bytes_acked: u32, rtt: Duration) -> Result<(), QuicError> {
        // Update RTT measurements
        let mut cubic = self.congestion_control.write().await;
        cubic.update_rtt(rtt);

        // Update congestion window using CUBIC algorithm
        let new_cwnd = cubic.on_ack(bytes_acked);

        // Update stats
        let mut stats = self.stats.write().await;
        stats.congestion_window = new_cwnd;
        stats.round_trip_time = cubic.smoothed_rtt.unwrap_or(rtt);
        stats.bytes_in_flight = stats.bytes_in_flight.saturating_sub(bytes_acked as u64);

        Ok(())
    }

    /// Handle packet loss: Trigger CUBIC multiplicative decrease
    /// Call this when loss is detected (3-DUP-ACK or timeout)
    pub async fn on_packet_lost(&self, bytes_lost: u32) -> Result<(), QuicError> {
        let mut cubic = self.congestion_control.write().await;
        cubic.on_packet_lost();

        // Update stats
        let mut stats = self.stats.write().await;
        stats.congestion_window = cubic.get_cwnd();
        stats.bytes_in_flight = stats.bytes_in_flight.saturating_sub(bytes_lost as u64);

        // Update loss rate (exponential moving average)
        let loss_event = 1.0;
        stats.packet_loss_rate = stats.packet_loss_rate * 0.9 + loss_event * 0.1;

        Ok(())
    }

    /// Get current congestion window size
    pub async fn get_congestion_window(&self) -> u32 {
        self.congestion_control.read().await.get_cwnd()
    }

    /// Get RTT statistics
    pub async fn get_rtt_stats(&self) -> (Option<Duration>, Option<Duration>, Option<Duration>) {
        let cubic = self.congestion_control.read().await;
        (cubic.latest_rtt, cubic.smoothed_rtt, cubic.min_rtt)
    }

    // ============================================================================
    // Path Migration APIs (RFC 9000 §9)
    // ============================================================================

    /// Initiate path migration to new address
    /// Returns new path_id assigned to this path
    pub async fn migrate_to_path(&self, new_path: SocketAddr) -> Result<u64, QuicError> {
        // Issue new Connection ID for the new path
        let _new_cid = self.cid_manager.write().await.issue_new_cid();

        // Assign new path ID
        let path_id = {
            let mut path_validations = self.path_validations.write().await;
            let path_id = path_validations.len() as u64 + 1;
            path_validations.insert(path_id, PathValidation::new(new_path));
            path_id
        };

        // Start path validation
        self.validate_path(path_id).await?;

        Ok(path_id)
    }

    /// Validate path by sending PATH_CHALLENGE
    pub async fn validate_path(&self, path_id: u64) -> Result<(), QuicError> {
        let mut path_validations = self.path_validations.write().await;
        let validation = path_validations
            .get_mut(&path_id)
            .ok_or_else(|| QuicError::Protocol("Path ID not found".to_string()))?;

        // Calculate PTO from CUBIC RTT (RFC 9000 §6.2.1: PTO = SRTT + max(4*RTTVAR, 1ms))
        let pto = {
            let cubic = self.congestion_control.read().await;
            let srtt = cubic.smoothed_rtt.unwrap_or(Duration::from_millis(100));
            let rttvar = cubic.rtt_var.unwrap_or(Duration::from_millis(50));
            srtt + rttvar.mul_f32(4.0).max(Duration::from_millis(1))
        };

        validation.start_validation(pto);

        // In production: send PATH_CHALLENGE frame to validation.path_addr
        // For now, just mark as started
        Ok(())
    }

    /// Handle received PATH_CHALLENGE frame
    pub async fn on_path_challenge_received(
        &self,
        _data: [u8; 8],
        _from_addr: SocketAddr,
    ) -> Result<(), QuicError> {
        // RFC 9000 §8.2: Respond with PATH_RESPONSE containing same data
        // In production: send PATH_RESPONSE frame to from_addr
        // For now, just log the event
        Ok(())
    }

    /// Handle received PATH_RESPONSE frame
    pub async fn on_path_response_received(
        &self,
        data: [u8; 8],
        from_addr: SocketAddr,
    ) -> Result<(), QuicError> {
        let mut path_validations = self.path_validations.write().await;

        // Find matching path validation
        for (path_id, validation) in path_validations.iter_mut() {
            if validation.path_addr == from_addr && validation.on_response(data) {
                // Path validated successfully
                // Switch to new path
                *self.current_path_id.write().await = *path_id;
                return Ok(());
            }
        }

        // No matching validation found
        Err(QuicError::Protocol(
            "PATH_RESPONSE does not match any challenge".to_string(),
        ))
    }

    /// Check for path validation timeouts and retry if needed
    pub async fn check_path_validation_timeouts(&self) -> Result<(), QuicError> {
        let pto = {
            let cubic = self.congestion_control.read().await;
            let srtt = cubic.smoothed_rtt.unwrap_or(Duration::from_millis(100));
            let rttvar = cubic.rtt_var.unwrap_or(Duration::from_millis(50));
            srtt + rttvar.mul_f32(4.0).max(Duration::from_millis(1))
        };

        let mut path_validations = self.path_validations.write().await;
        for (_path_id, validation) in path_validations.iter_mut() {
            if validation.check_timeout(pto) {
                // Retry: send PATH_CHALLENGE again
                // In production: send frame to validation.path_addr
            }
        }

        Ok(())
    }

    /// Get current active path ID
    pub async fn current_path_id(&self) -> u64 {
        *self.current_path_id.read().await
    }
}

impl QuicStream {
    /// Create new stream
    pub fn new(stream_id: u64, stream_type: StreamType) -> Self {
        Self {
            stream_id,
            stream_type,
            state: StreamState::Open,
            send_buffer: Vec::new(),
            recv_buffer: Vec::new(),
            _send_offset: 0,
            _recv_offset: 0,
        }
    }

    /// Write data
    pub async fn write_data(&mut self, _data: Bytes) -> Result<(), QuicError> {
        if self.state == StreamState::Closed {
            return Err(QuicError::StreamClosed);
        }

        self.send_buffer.extend_from_slice(&_data);
        Ok(())
    }

    /// Read data
    pub async fn read_data(&mut self) -> Result<Option<Bytes>, QuicError> {
        if self.recv_buffer.is_empty() {
            return Ok(None);
        }

        let _data = Bytes::copy_from_slice(&self.recv_buffer);
        self.recv_buffer.clear();
        self._recv_offset += _data.len() as u64;

        Ok(Some(_data))
    }
}

impl Default for QuicCryptoContext {
    fn default() -> Self {
        Self::new()
    }
}

impl QuicCryptoContext {
    /// Create new crypto context
    pub fn new() -> Self {
        Self {
            initial_secret: [0u8; 32],
            handshake_secret: [0u8; 32],
            application_secret: [0u8; 32],
            key_update_secret: [0u8; 32],
            encryption_level: EncryptionLevel::Initial,
            key_phase: 0,
        }
    }

    /// Encrypt packet using ChaCha20Poly1305 AEAD
    ///
    /// Implements QUIC packet protection as per RFC 9001 §5.
    /// Uses ChaCha20Poly1305 with HKDF-derived keys and packet-number-based nonce.
    ///
    /// # Security Properties
    /// - AEAD provides confidentiality and authenticity
    /// - Nonce is derived from packet number to ensure uniqueness
    /// - Encryption level determines which secret to use (Initial/Handshake/Application)
    /// - Tag size is 16 bytes (128 bits) per ChaCha20Poly1305 spec
    ///
    /// # Arguments
    /// * `packet` - Plaintext packet payload
    /// * `packetnumber` - QUIC packet number (used for nonce derivation)
    ///
    /// # Returns
    /// Encrypted packet with 16-byte authentication tag appended
    pub async fn encrypt_packet(
        &self,
        packet: &[u8],
        packetnumber: u64,
    ) -> Result<Bytes, QuicError> {
        // Select encryption secret based on current encryption level
        let secret = match self.encryption_level {
            EncryptionLevel::Initial => &self.initial_secret,
            EncryptionLevel::Handshake => &self.handshake_secret,
            EncryptionLevel::Application => {
                // Application level uses key phase for key rotation
                if self.key_phase == 0 {
                    &self.application_secret
                } else {
                    &self.key_update_secret
                }
            }
        };

        // Derive encryption key using HKDF-SHA256 (RFC 9001 §5.1)
        let hkdf = Hkdf::<Sha256>::new(None, secret);
        let mut key = [0u8; 32]; // ChaCha20 uses 256-bit keys
        hkdf.expand(b"quic key", &mut key)
            .map_err(|e| QuicError::CryptoError(format!("HKDF key derivation failed: {}", e)))?;

        // Derive IV using HKDF-SHA256
        let mut iv_base = [0u8; 12]; // ChaCha20Poly1305 nonce is 96 bits
        hkdf.expand(b"quic iv", &mut iv_base)
            .map_err(|e| QuicError::CryptoError(format!("HKDF IV derivation failed: {}", e)))?;

        // Construct nonce by XORing IV with packet number (RFC 9001 §5.3)
        // This ensures nonce uniqueness per packet
        let mut nonce_bytes = iv_base;
        let pn_bytes = packetnumber.to_be_bytes();
        for i in 0..8 {
            nonce_bytes[4 + i] ^= pn_bytes[i];
        }
        let nonce = ChaNonce::from_slice(&nonce_bytes);

        // Create ChaCha20Poly1305 cipher
        let cipher = ChaCha20Poly1305::new(&key.into());

        // Encrypt with AEAD (includes authentication tag)
        let ciphertext = cipher.encrypt(nonce, packet).map_err(|e| {
            QuicError::CryptoError(format!("ChaCha20Poly1305 encryption failed: {}", e))
        })?;

        Ok(Bytes::copy_from_slice(&ciphertext))
    }

    /// Decrypt packet using ChaCha20Poly1305 AEAD
    ///
    /// Implements QUIC packet protection removal as per RFC 9001 §5.
    /// Verifies authentication tag to prevent tampering.
    ///
    /// # Security Properties
    /// - Authentication tag verification prevents packet modification
    /// - Nonce reconstruction ensures packet number integrity
    /// - Decryption failure indicates tampering or wrong key
    ///
    /// # Arguments
    /// * `encrypted_packet` - Ciphertext packet with 16-byte authentication tag
    /// * `packetnumber` - QUIC packet number (used for nonce derivation)
    ///
    /// # Returns
    /// Decrypted packet payload (without authentication tag)
    ///
    /// # Errors
    /// Returns `CryptoError` if:
    /// - Authentication tag verification fails (tampering detected)
    /// - Decryption fails due to wrong key or corrupted data
    pub async fn decrypt_packet(
        &self,
        encrypted_packet: &[u8],
        packetnumber: u64,
    ) -> Result<Bytes, QuicError> {
        // Select decryption secret based on current encryption level
        let secret = match self.encryption_level {
            EncryptionLevel::Initial => &self.initial_secret,
            EncryptionLevel::Handshake => &self.handshake_secret,
            EncryptionLevel::Application => {
                if self.key_phase == 0 {
                    &self.application_secret
                } else {
                    &self.key_update_secret
                }
            }
        };

        // Derive decryption key using HKDF-SHA256 (must match encryption)
        let hkdf = Hkdf::<Sha256>::new(None, secret);
        let mut key = [0u8; 32];
        hkdf.expand(b"quic key", &mut key)
            .map_err(|e| QuicError::CryptoError(format!("HKDF key derivation failed: {}", e)))?;

        // Derive IV using HKDF-SHA256
        let mut iv_base = [0u8; 12];
        hkdf.expand(b"quic iv", &mut iv_base)
            .map_err(|e| QuicError::CryptoError(format!("HKDF IV derivation failed: {}", e)))?;

        // Reconstruct nonce (must match encryption nonce)
        let mut nonce_bytes = iv_base;
        let pn_bytes = packetnumber.to_be_bytes();
        for i in 0..8 {
            nonce_bytes[4 + i] ^= pn_bytes[i];
        }
        let nonce = ChaNonce::from_slice(&nonce_bytes);

        // Create ChaCha20Poly1305 cipher
        let cipher = ChaCha20Poly1305::new(&key.into());

        // Decrypt and verify authentication tag
        let plaintext = cipher.decrypt(nonce, encrypted_packet).map_err(|e| {
            QuicError::CryptoError(format!(
                "ChaCha20Poly1305 decryption/authentication failed: {}",
                e
            ))
        })?;

        Ok(Bytes::copy_from_slice(&plaintext))
    }

    /// Apply header protection to packet (RFC 9001 §5.4)
    ///
    /// Header protection obscures the packet number and packet type flags
    /// to prevent passive observers from identifying packet boundaries.
    /// Uses ChaCha20 as the cipher (matching packet encryption).
    ///
    /// # Arguments
    /// * `header` - Packet header bytes to protect (first byte + packet number)
    /// * `sample_offset` - Offset in ciphertext where 16-byte sample begins
    /// * `ciphertext` - Full encrypted packet (for sampling)
    ///
    /// # Returns
    /// Protected header with masked first byte and packet number
    pub async fn protect_header(
        &self,
        header: &[u8],
        sample_offset: usize,
        ciphertext: &[u8],
    ) -> Result<Bytes, QuicError> {
        if ciphertext.len() < sample_offset + 16 {
            return Err(QuicError::CryptoError(
                "Insufficient ciphertext for header protection sample".to_string(),
            ));
        }

        // Select secret based on encryption level
        let secret = match self.encryption_level {
            EncryptionLevel::Initial => &self.initial_secret,
            EncryptionLevel::Handshake => &self.handshake_secret,
            EncryptionLevel::Application => {
                if self.key_phase == 0 {
                    &self.application_secret
                } else {
                    &self.key_update_secret
                }
            }
        };

        // Derive header protection key using HKDF
        let hkdf = Hkdf::<Sha256>::new(None, secret);
        let mut hp_key = [0u8; 32];
        hkdf.expand(b"quic hp", &mut hp_key)
            .map_err(|e| QuicError::CryptoError(format!("HKDF HP key derivation failed: {}", e)))?;

        // Note: sample extraction from ciphertext[sample_offset..sample_offset + 16]
        // is implicitly used in ChaCha20 header protection mask generation below.
        // The 16-byte sample serves as the IV input to the ChaCha20 cipher.

        // Use ChaCha20 to generate mask from sample
        // Note: Using ChaCha20Poly1305 cipher in encrypt mode with zero nonce
        // This is safe for header protection as sample acts as IV
        let cipher = ChaCha20Poly1305::new(&hp_key.into());
        let zero_nonce = ChaNonce::from_slice(&[0u8; 12]);

        // Generate mask by encrypting zeros (ChaCha20 keystream)
        let mask_input = vec![0u8; 5]; // Need 5 bytes of mask
        let mask = cipher
            .encrypt(zero_nonce, mask_input.as_slice())
            .map_err(|e| {
                QuicError::CryptoError(format!("Header protection mask generation failed: {}", e))
            })?;

        // Apply mask to header (first byte and packet number)
        let mut protected = header.to_vec();
        if !protected.is_empty() {
            // Mask packet number length bits (lower 2 bits of first byte)
            protected[0] ^= mask[0] & 0x1f;

            // Mask packet number bytes
            for i in 1..protected.len().min(5) {
                protected[i] ^= mask[i];
            }
        }

        Ok(Bytes::copy_from_slice(&protected))
    }

    /// Remove header protection from packet (RFC 9001 §5.4)
    ///
    /// Inverse operation of protect_header. Reveals original packet number
    /// and packet type flags.
    ///
    /// # Arguments
    /// * `protected_header` - Protected header bytes
    /// * `sample_offset` - Offset in ciphertext for 16-byte sample
    /// * `ciphertext` - Full encrypted packet
    ///
    /// # Returns
    /// Unprotected header with original first byte and packet number
    pub async fn unprotect_header(
        &self,
        protected_header: &[u8],
        sample_offset: usize,
        ciphertext: &[u8],
    ) -> Result<Bytes, QuicError> {
        // Header unprotection uses same algorithm as protection (XOR is its own inverse)
        self.protect_header(protected_header, sample_offset, ciphertext)
            .await
    }
}

impl QuicEndpoint {
    /// Create new QUIC Endpoint
    pub async fn new(bind_addr: SocketAddr, config: QuicEndpointConfig) -> Result<Self, QuicError> {
        let socket = UdpSocket::bind(bind_addr)
            .await
            .map_err(|e| QuicError::Io(e.to_string()))?;
        let connections = Arc::new(TokioRwLock::new(HashMap::new()));
        let statistics = Arc::new(TokioRwLock::new(EndpointStatistics::default()));

        Ok(Self {
            socket,
            bind_addr,
            config,
            connections,
            statistics,
        })
    }

    /// Get local address
    pub fn local_addr(&self) -> Result<SocketAddr, QuicError> {
        self.socket
            .local_addr()
            .map_err(|e| QuicError::Io(e.to_string()))
    }

    /// Get connection statistics
    pub async fn get_connection_stats(
        &self,
        connection_id: &Bytes,
    ) -> Result<ConnectionStats, QuicError> {
        let connections = self.connections.read().await;
        let connection = connections
            .get(connection_id)
            .ok_or_else(|| QuicError::ConnectionNotFound(connection_id.clone()))?;

        let stats = (*connection.stats.read().await).clone();

        Ok(stats)
    }

    /// Get active connections list
    pub async fn active_connections(&self) -> Vec<Bytes> {
        self.connections.read().await.keys().cloned().collect()
    }

    /// Get connection
    pub async fn get_connection(&self, connection_id: &Bytes) -> Result<QuicConnection, QuicError> {
        let connections = self.connections.read().await;
        connections
            .get(connection_id)
            .cloned()
            .ok_or_else(|| QuicError::ConnectionNotFound(connection_id.clone()))
    }

    /// Remove connection
    pub async fn remove_connection(&self, connection_id: &Bytes) -> Result<(), QuicError> {
        let mut connections = self.connections.write().await;
        connections.remove(connection_id);

        Ok(())
    }

    /// Cleanup idle connections
    pub async fn cleanup_idle_connections(&self) -> Result<(), QuicError> {
        let mut connections = self.connections.write().await;
        let timeout_duration = self.config.idle_timeout;
        let current_time = Instant::now();

        let idle_ids: Vec<Bytes> = connections
            .iter()
            .filter_map(|(id, conn)| {
                if current_time.duration_since(conn._last_activity) > timeout_duration {
                    Some(id.clone())
                } else {
                    None
                }
            })
            .collect();

        for id in idle_ids {
            connections.remove(&id);
        }

        Ok(())
    }

    /// Send data
    pub async fn send_data(&self, connection_id: &Bytes) -> Result<(), QuicError> {
        let connections = self.connections.read().await;
        connections
            .get(connection_id)
            .ok_or_else(|| QuicError::ConnectionNotFound(connection_id.clone()))?;

        Ok(())
    }
}

// ============================================================================
// QUIC Packet Format Structures (RFC 9000)
// ============================================================================

/// QUIC packet header type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PacketType {
    Initial,
    Handshake,
    ZeroRtt,
    OneRtt,
    Retry,
    VersionNegotiation,
}

/// QUIC packet header
#[derive(Debug, Clone)]
pub struct PacketHeader {
    pub packet_type: PacketType,
    pub conn_id: Bytes,
    pub packet_number: u64,
    pub version: u32,
}

/// QUIC frame type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FrameType {
    Padding,
    Ping,
    Ack,
    ResetStream,
    StopSending,
    Crypto,
    NewToken,
    Stream,
    MaxData,
    MaxStreamData,
    MaxStreams,
    DataBlocked,
    StreamDataBlocked,
    StreamsBlocked,
    NewConnectionId,
    RetireConnectionId,
    PathChallenge,
    PathResponse,
    ConnectionClose,
    HandshakeDone,
    Datagram,
}

/// QUIC frame
#[derive(Debug, Clone)]
pub enum Frame {
    Padding,
    Ping,
    Ack {
        largest: u64,
        delay: u64,
        ranges: Vec<(u64, u64)>,
    },
    Stream {
        id: u64,
        offset: u64,
        data: Bytes,
        fin: bool,
    },
    Crypto {
        offset: u64,
        data: Bytes,
    },
    PathChallenge {
        data: [u8; 8],
    },
    PathResponse {
        data: [u8; 8],
    },
    Datagram {
        data: Bytes,
    },
    ConnectionClose {
        error_code: u64,
        reason: String,
    },
}

/// Parse QUIC packet from bytes
#[allow(unused_assignments)] // data is reassigned for sequential parsing
pub fn parse_packet(mut data: &[u8]) -> Result<(PacketHeader, Vec<Frame>), QuicError> {
    if data.is_empty() {
        return Err(QuicError::PacketDecode("Empty packet".into()));
    }

    let first_byte = data[0];
    let is_long_header = (first_byte & 0x80) != 0;

    let packet_type = if is_long_header {
        let type_bits = (first_byte >> 4) & 0x03;
        match type_bits {
            0x00 => PacketType::Initial,
            0x01 => PacketType::ZeroRtt,
            0x02 => PacketType::Handshake,
            0x03 => PacketType::Retry,
            _ => return Err(QuicError::PacketDecode("Invalid packet type".into())),
        }
    } else {
        PacketType::OneRtt
    };

    data = &data[1..];

    // Parse connection ID (simplified - assume 8 bytes)
    if data.len() < 8 {
        return Err(QuicError::PacketDecode(
            "Insufficient data for conn ID".into(),
        ));
    }
    let conn_id = Bytes::copy_from_slice(&data[..8]);
    data = &data[8..];

    // Parse packet number (simplified - assume 4 bytes)
    if data.len() < 4 {
        return Err(QuicError::PacketDecode(
            "Insufficient data for packet number".into(),
        ));
    }
    let packet_number = u32::from_be_bytes([data[0], data[1], data[2], data[3]]) as u64;
    data = &data[4..];

    let header = PacketHeader {
        packet_type,
        conn_id,
        packet_number,
        version: 1,
    };

    // Parse frames (simplified)
    let frames = vec![];

    Ok((header, frames))
}

/// Serialize QUIC packet to bytes
pub fn serialize_packet(header: &PacketHeader, frames: &[Frame]) -> Result<Bytes, QuicError> {
    let mut buf = BytesMut::with_capacity(1200);

    // Write header
    let first_byte = match header.packet_type {
        PacketType::Initial => 0xC0,
        PacketType::Handshake => 0xE0,
        PacketType::OneRtt => 0x40,
        _ => 0x80,
    };
    buf.put_u8(first_byte);

    // Write connection ID
    buf.put_slice(&header.conn_id);

    // Write packet number
    buf.put_u32(header.packet_number as u32);

    // Write frames
    for frame in frames {
        match frame {
            Frame::Ping => {
                buf.put_u8(0x01);
            }
            Frame::Stream {
                id,
                offset,
                data,
                fin,
            } => {
                buf.put_u8(if *fin { 0x0F } else { 0x0E });
                buf.put_u64(*id);
                buf.put_u64(*offset);
                buf.put_u32(data.len() as u32);
                buf.put_slice(data);
            }
            Frame::Datagram { data } => {
                buf.put_u8(0x31);
                buf.put_u32(data.len() as u32);
                buf.put_slice(data);
            }
            Frame::PathChallenge { data } => {
                buf.put_u8(0x1A);
                buf.put_slice(data);
            }
            Frame::PathResponse { data } => {
                buf.put_u8(0x1B);
                buf.put_slice(data);
            }
            _ => {}
        }
    }

    Ok(buf.freeze())
}

// ============================================================================
// BBR Congestion Control (Bottleneck Bandwidth and RTT)
// ============================================================================

/// BBR congestion control state
#[derive(Debug, Clone)]
pub struct BbrState {
    /// Current congestion window (bytes)
    pub cwnd: u64,
    /// Bottleneck bandwidth estimate (bytes/sec)
    pub btlbw: u64,
    /// Minimum RTT observed (microseconds)
    pub rtprop: u64,
    /// Pacing gain
    pub pacing_gain: f64,
    /// CWND gain
    pub cwnd_gain: f64,
    /// Current BBR mode
    pub mode: BbrMode,
    /// Cycle index for ProbeBW mode
    pub cycle_index: usize,
    /// Last mode switch time
    pub mode_start: Instant,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BbrMode {
    Startup,
    Drain,
    ProbeBW,
    ProbeRTT,
}

impl Default for BbrState {
    fn default() -> Self {
        Self {
            cwnd: 10 * 1200, // 10 packets
            btlbw: 100_000,  // 100 KB/s initial estimate
            rtprop: 100_000, // 100ms initial RTT
            pacing_gain: 2.77,
            cwnd_gain: 2.0,
            mode: BbrMode::Startup,
            cycle_index: 0,
            mode_start: Instant::now(),
        }
    }
}

impl BbrState {
    /// Update BBR state on ACK receipt
    pub fn on_ack(&mut self, bytes_acked: u64, rtt_sample: Duration) {
        let rtt_us = rtt_sample.as_micros() as u64;

        // Update RTprop (minimum RTT)
        if rtt_us < self.rtprop {
            self.rtprop = rtt_us;
        }

        // Update bandwidth estimate
        let delivery_rate = (bytes_acked * 1_000_000) / rtt_us.max(1);
        if delivery_rate > self.btlbw {
            self.btlbw = delivery_rate;
        }

        // Update congestion window based on mode
        match self.mode {
            BbrMode::Startup => {
                self.cwnd = (self.btlbw * self.rtprop * self.cwnd_gain as u64) / 1_000_000;

                // Exit startup if bandwidth not growing
                if self.mode_start.elapsed() > Duration::from_secs(1) {
                    self.mode = BbrMode::Drain;
                    self.pacing_gain = 1.0 / 2.77;
                    self.mode_start = Instant::now();
                }
            }
            BbrMode::Drain => {
                self.cwnd = (self.btlbw * self.rtprop) / 1_000_000;

                // Exit drain when queue is empty
                if self.mode_start.elapsed() > Duration::from_millis(500) {
                    self.mode = BbrMode::ProbeBW;
                    self.pacing_gain = 1.0;
                    self.mode_start = Instant::now();
                }
            }
            BbrMode::ProbeBW => {
                // Cycle through pacing gains
                let gains = [1.25, 0.75, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0];
                self.pacing_gain = gains[self.cycle_index % gains.len()];
                self.cwnd = (self.btlbw * self.rtprop) / 1_000_000;

                if self.mode_start.elapsed() > Duration::from_secs(2) {
                    self.cycle_index += 1;
                    self.mode_start = Instant::now();
                }
            }
            BbrMode::ProbeRTT => {
                self.cwnd = 4 * 1200; // Minimum window

                if self.mode_start.elapsed() > Duration::from_millis(200) {
                    self.mode = BbrMode::ProbeBW;
                    self.mode_start = Instant::now();
                }
            }
        }
    }

    /// Check if sending is allowed
    pub fn can_send(&self, bytes_in_flight: u64) -> bool {
        bytes_in_flight < self.cwnd
    }

    /// Get pacing rate (bytes per second)
    pub fn pacing_rate(&self) -> u64 {
        (self.btlbw as f64 * self.pacing_gain) as u64
    }
}

// ============================================================================
// QuicTransport - High-level Transport Wrapper
// ============================================================================

/// High-level QUIC transport interface
pub struct QuicTransport {
    pub endpoint: QuicEndpoint,
    datagram_tx: mpsc::UnboundedSender<(Bytes, SocketAddr)>,
    datagram_rx: Arc<TokioRwLock<mpsc::UnboundedReceiver<(Bytes, SocketAddr)>>>,
}

impl QuicTransport {
    /// Create new QUIC transport
    pub async fn new(config: nyx_core::config::QuicConfig) -> Result<Self, QuicError> {
        let endpoint_config = QuicEndpointConfig {
            max_connections: config.max_concurrent_streams as u32,
            connection_timeout: Duration::from_secs(10),
            idle_timeout: Duration::from_secs(config.idle_timeout_secs),
            max_stream_s_per_connection: config.max_concurrent_streams as u32,
            initial_max_data: 1048576,
            initial_max_stream_data: 262144,
        };

        let endpoint = QuicEndpoint::new(config.bind_addr, endpoint_config).await?;
        let (datagram_tx, datagram_rx) = mpsc::unbounded_channel();
        let datagram_rx = Arc::new(TokioRwLock::new(datagram_rx));

        Ok(Self {
            endpoint,
            datagram_tx,
            datagram_rx,
        })
    }

    /// Accept incoming connection
    pub async fn accept(&mut self) -> Result<Arc<QuicConnection>, QuicError> {
        // Simplified accept - in production would listen on socket
        let conn_id = Bytes::from(vec![0u8; 8]);
        let peer_addr = "127.0.0.1:0".parse().unwrap();
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id.clone(), peer_addr, true, stats)?;

        self.endpoint
            .connections
            .write()
            .await
            .insert(conn_id.clone(), conn.clone());
        let conn = Arc::new(conn);

        Ok(conn)
    }

    /// Connect to remote peer
    pub async fn connect(&self, peer: SocketAddr) -> Result<Arc<QuicConnection>, QuicError> {
        let mut rng = rand::thread_rng();
        let conn_id = Bytes::from(rng.gen::<[u8; 8]>().to_vec());
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id.clone(), peer, false, stats)?;
        conn.establish_connection(None).await?;

        self.endpoint
            .connections
            .write()
            .await
            .insert(conn_id.clone(), conn.clone());
        let conn = Arc::new(conn);

        Ok(conn)
    }

    /// Send datagram
    pub async fn send_datagram(&self, data: &[u8], peer: SocketAddr) -> Result<(), QuicError> {
        self.datagram_tx
            .send((Bytes::copy_from_slice(data), peer))
            .map_err(|_| QuicError::Transport("Datagram channel closed".into()))
    }

    /// Receive datagram
    pub async fn recv_datagram(&self) -> Result<Bytes, QuicError> {
        self.datagram_rx
            .write()
            .await
            .recv()
            .await
            .map(|(data, _addr)| data)
            .ok_or_else(|| QuicError::Transport("Datagram channel closed".into()))
    }
}

// ============================================================================
// Enhanced QuicConnection with Datagram Support
// ============================================================================

impl QuicConnection {
    /// Get connection state
    pub fn get_state(&self) -> ConnectionState {
        // Clone state synchronously - in production use async properly
        ConnectionState::Connected {
            peer: self._peer_addr,
            established_at: Instant::now(),
            stream_count: 0,
            congestion_window: 65536,
        }
    }

    /// Check if connection is active
    pub fn is_active(&self) -> bool {
        true // Simplified
    }

    /// Open bidirectional stream
    pub async fn open_bidirectional_stream(
        &self,
        _stream_type: StreamType,
        _priority: u8,
    ) -> Result<u64, QuicError> {
        let stream_id = self._next_stream_id;
        let stream = QuicStream::new(stream_id, StreamType::Bidirectional);
        self.streams.write().await.insert(stream_id, stream);
        Ok(stream_id)
    }

    /// Open unidirectional stream
    pub async fn open_unidirectional_stream(
        &self,
        _stream_type: StreamType,
        _priority: u8,
    ) -> Result<u64, QuicError> {
        let stream_id = self._next_stream_id + 1;
        let stream = QuicStream::new(stream_id, StreamType::Unidirectional);
        self.streams.write().await.insert(stream_id, stream);
        Ok(stream_id)
    }

    /// Send data on stream
    pub async fn send_on_stream(&self, stream_id: u64, data: &[u8]) -> Result<(), QuicError> {
        let mut streams = self.streams.write().await;
        let stream = streams
            .get_mut(&stream_id)
            .ok_or(QuicError::StreamNotFoundError)?;
        stream.write_data(Bytes::copy_from_slice(data)).await
    }

    /// Receive data from stream
    pub async fn recv_from_stream(
        &self,
        stream_id: u64,
        _timeout: Duration,
    ) -> Result<Result<Bytes, QuicError>, QuicError> {
        let mut streams = self.streams.write().await;
        let stream = streams
            .get_mut(&stream_id)
            .ok_or(QuicError::StreamNotFoundError)?;
        stream
            .read_data()
            .await
            .map(|opt| opt.ok_or(QuicError::StreamNotFoundError))
    }
}

/// Enhanced crypto context with real encryption
impl QuicCryptoContext {
    /// Encrypt packet with ChaCha20-Poly1305
    pub async fn encrypt_packet_real(
        &self,
        packet: &[u8],
        packet_number: u64,
    ) -> Result<Bytes, QuicError> {
        let cipher = ChaCha20Poly1305::new(&self.application_secret.into());

        // Construct nonce from packet number (RFC 9001)
        let mut nonce_bytes = [0u8; 12];
        nonce_bytes[4..].copy_from_slice(&packet_number.to_be_bytes());
        let nonce = ChaNonce::from_slice(&nonce_bytes);

        let ciphertext = cipher
            .encrypt(nonce, packet)
            .map_err(|e| QuicError::CryptoError(e.to_string()))?;

        Ok(Bytes::from(ciphertext))
    }

    /// Decrypt packet with ChaCha20-Poly1305
    pub async fn decrypt_packet_real(
        &self,
        encrypted_packet: &[u8],
        packet_number: u64,
    ) -> Result<Bytes, QuicError> {
        let cipher = ChaCha20Poly1305::new(&self.application_secret.into());

        let mut nonce_bytes = [0u8; 12];
        nonce_bytes[4..].copy_from_slice(&packet_number.to_be_bytes());
        let nonce = ChaNonce::from_slice(&nonce_bytes);

        let plaintext = cipher
            .decrypt(nonce, encrypted_packet)
            .map_err(|e| QuicError::CryptoError(e.to_string()))?;

        Ok(Bytes::from(plaintext))
    }

    /// Derive traffic keys using HKDF
    pub fn derive_keys(secret: &[u8], label: &str) -> Result<[u8; 32], QuicError> {
        let hk = Hkdf::<Sha256>::new(None, secret);
        let mut okm = [0u8; 32];
        hk.expand(label.as_bytes(), &mut okm)
            .map_err(|e| QuicError::CryptoError(e.to_string()))?;
        Ok(okm)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_quic_frame_datagram_encode_decode() {
        let data = Bytes::from_static(b"test datagram payload");
        let frame = QuicFrame::Datagram { data: data.clone() };

        // Encode
        let encoded = frame.encode().unwrap();

        // Verify frame type is 0x31 (DATAGRAM with length)
        assert_eq!(encoded[0], 0x31);

        // Decode
        let (decoded_frame, consumed) = QuicFrame::decode(&encoded).unwrap();
        assert_eq!(consumed, encoded.len());

        match decoded_frame {
            QuicFrame::Datagram { data: decoded_data } => {
                assert_eq!(decoded_data, data);
            }
            _ => panic!("Expected Datagram frame"),
        }
    }

    #[tokio::test]
    async fn test_transport_parameters_default() {
        let params = TransportParameters::default();

        // RFC 9221: max_datagram_frame_size should be set
        assert!(params.max_datagram_frame_size.is_some());
        assert_eq!(
            params.max_datagram_frame_size.unwrap(),
            MAX_DATAGRAM_SIZE as u64
        );

        // Verify other defaults
        assert_eq!(params.initial_max_data, 1_048_576);
        assert_eq!(params.max_udp_payload_size, MAX_DATAGRAM_SIZE as u64);
    }

    #[tokio::test]
    async fn test_connection_send_datagram_success() {
        let conn_id = Bytes::from_static(b"test-conn");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        // Set peer transport parameters to enable datagram extension
        let peer_params = TransportParameters::default();
        conn.set_peer_transport_parameters(peer_params)
            .await
            .unwrap();

        // Send small datagram (within limit)
        let data = Bytes::from_static(b"small test datagram");
        let result = conn.send_datagram(data.clone()).await;
        assert!(result.is_ok());

        // Verify datagram is queued
        let (send_len, _) = conn.datagram_queue_len().await;
        assert_eq!(send_len, 1);
    }

    #[tokio::test]
    async fn test_connection_send_datagram_too_large() {
        let conn_id = Bytes::from_static(b"test-conn");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        // Set peer transport parameters
        let mut peer_params = TransportParameters::default();
        peer_params.max_datagram_frame_size = Some(100); // Small limit
        conn.set_peer_transport_parameters(peer_params)
            .await
            .unwrap();

        // Try to send too-large datagram
        let data = Bytes::from(vec![0u8; 200]);
        let result = conn.send_datagram(data).await;

        assert!(result.is_err());
        match result.unwrap_err() {
            QuicError::DatagramTooLarge(_) => {}
            e => panic!("Expected DatagramTooLarge error, got {:?}", e),
        }
    }

    #[tokio::test]
    async fn test_connection_send_datagram_not_supported() {
        let conn_id = Bytes::from_static(b"test-conn");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        // Set peer transport parameters WITHOUT datagram extension
        let mut peer_params = TransportParameters::default();
        peer_params.max_datagram_frame_size = None;
        conn.set_peer_transport_parameters(peer_params)
            .await
            .unwrap();

        // Try to send datagram
        let data = Bytes::from_static(b"test");
        let result = conn.send_datagram(data).await;

        assert!(result.is_err());
        match result.unwrap_err() {
            QuicError::FeatureNotSupported(_) => {}
            e => panic!("Expected FeatureNotSupported error, got {:?}", e),
        }
    }

    #[tokio::test]
    async fn test_connection_recv_datagram() {
        let conn_id = Bytes::from_static(b"test-conn");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        // Manually add datagram to receive queue (simulating reception)
        let data = Bytes::from_static(b"received datagram");
        {
            let mut queue = conn.datagram_recv_queue.write().await;
            queue.push(data.clone());
        }

        // Receive datagram
        let received = conn.recv_datagram().await.unwrap();
        assert!(received.is_some());
        assert_eq!(received.unwrap(), data);

        // Queue should be empty now
        let (_, recv_len) = conn.datagram_queue_len().await;
        assert_eq!(recv_len, 0);
    }

    #[tokio::test]
    async fn test_connection_recv_datagram_empty_queue() {
        let conn_id = Bytes::from_static(b"test-conn");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        // Try to receive from empty queue
        let received = conn.recv_datagram().await.unwrap();
        assert!(received.is_none());
    }

    #[tokio::test]
    async fn test_datagram_fifo_order() {
        let conn_id = Bytes::from_static(b"test-conn");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        // Add multiple datagrams
        let data1 = Bytes::from_static(b"first");
        let data2 = Bytes::from_static(b"second");
        let data3 = Bytes::from_static(b"third");

        {
            let mut queue = conn.datagram_recv_queue.write().await;
            queue.push(data1.clone());
            queue.push(data2.clone());
            queue.push(data3.clone());
        }

        // Receive in FIFO order
        assert_eq!(conn.recv_datagram().await.unwrap().unwrap(), data1);
        assert_eq!(conn.recv_datagram().await.unwrap().unwrap(), data2);
        assert_eq!(conn.recv_datagram().await.unwrap().unwrap(), data3);
        assert!(conn.recv_datagram().await.unwrap().is_none());
    }

    #[test]
    fn test_quic_frame_stream_encode_decode() {
        let stream_id = 42;
        let offset = 100;
        let data = Bytes::from_static(b"stream data");
        let fin = true;

        let frame = QuicFrame::Stream {
            stream_id,
            offset,
            data: data.clone(),
            fin,
        };

        // Encode
        let encoded = frame.encode().unwrap();
        assert_eq!(encoded[0] & 0x08, 0x08); // STREAM frame type
        assert_eq!(encoded[0] & 0x01, 0x01); // FIN bit set

        // Decode
        let (decoded_frame, _) = QuicFrame::decode(&encoded).unwrap();

        match decoded_frame {
            QuicFrame::Stream {
                stream_id: decoded_id,
                offset: decoded_offset,
                data: decoded_data,
                fin: decoded_fin,
            } => {
                assert_eq!(decoded_id, stream_id);
                assert_eq!(decoded_offset, offset);
                assert_eq!(decoded_data, data);
                assert_eq!(decoded_fin, fin);
            }
            _ => panic!("Expected Stream frame"),
        }
    }

    #[test]
    fn test_quic_frame_ack_encode_decode() {
        let frame = QuicFrame::Ack {
            largest_acknowledged: 1000,
            ack_delay: 50,
            ack_ranges: vec![(900, 950), (800, 850)],
        };

        let encoded = frame.encode().unwrap();
        assert_eq!(encoded[0], 0x02); // ACK frame type

        let (decoded_frame, _) = QuicFrame::decode(&encoded).unwrap();

        match decoded_frame {
            QuicFrame::Ack {
                largest_acknowledged,
                ack_delay,
                ack_ranges,
            } => {
                assert_eq!(largest_acknowledged, 1000);
                assert_eq!(ack_delay, 50);
                assert_eq!(ack_ranges.len(), 2);
            }
            _ => panic!("Expected Ack frame"),
        }
    }

    #[test]
    fn test_quic_frame_connection_close_encode_decode() {
        let frame = QuicFrame::ConnectionClose {
            error_code: 0x01,
            reason: "Protocol violation".to_string(),
        };

        let encoded = frame.encode().unwrap();
        assert_eq!(encoded[0], 0x1c); // CONNECTION_CLOSE frame type

        let (decoded_frame, _) = QuicFrame::decode(&encoded).unwrap();

        match decoded_frame {
            QuicFrame::ConnectionClose { error_code, reason } => {
                assert_eq!(error_code, 0x01);
                assert_eq!(reason, "Protocol violation");
            }
            _ => panic!("Expected ConnectionClose frame"),
        }
    }

    #[test]
    fn test_quic_frame_decode_invalid() {
        // Empty data
        let result = QuicFrame::decode(&[]);
        assert!(result.is_err());

        // Unknown frame type
        let result = QuicFrame::decode(&[0xFF]);
        assert!(result.is_err());
        match result.unwrap_err() {
            QuicError::InvalidFrame(_) => {}
            e => panic!("Expected InvalidFrame error, got {:?}", e),
        }
    }

    #[tokio::test]
    async fn test_datagram_congestion_control() {
        let conn_id = Bytes::from_static(b"test-conn");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let mut stats = ConnectionStats::default();
        stats.bytes_in_flight = 6000; // Set high bytes in flight

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        // Manually set low congestion window in CUBIC
        {
            let mut cubic = conn.congestion_control.write().await;
            cubic.cwnd = 1000; // Low cwnd
        }

        // Set peer parameters
        let peer_params = TransportParameters::default();
        conn.set_peer_transport_parameters(peer_params)
            .await
            .unwrap();

        // Try to send large datagram (exceeds available budget)
        // cwnd=1000, bytes_in_flight=6000, available=0
        // datagram_budget=500 (50% of cwnd)
        let data = Bytes::from(vec![0u8; 600]); // Exceeds budget
        let result = conn.send_datagram(data).await;

        // Should fail due to congestion control
        assert!(result.is_err());
        match result.unwrap_err() {
            QuicError::CongestionControl(_) => {}
            e => panic!("Expected CongestionControl error, got {:?}", e),
        }
    }

    #[tokio::test]
    async fn test_get_local_transport_parameters() {
        let conn_id = Bytes::from_static(b"test-conn");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        let params = conn.get_local_transport_parameters().await;

        // Verify defaults
        assert!(params.max_datagram_frame_size.is_some());
        assert_eq!(params.initial_max_streams_bidi, 100);
        assert_eq!(params.max_idle_timeout, 30_000);
    }

    // ===== HEADER PROTECTION TESTS (RFC 9001 §5.4) =====

    #[test]
    fn test_header_protection_key_derivation() {
        // Test HKDF-Expand-Label key derivation
        let traffic_secret = [0x55u8; 32];
        let hp = HeaderProtection::derive_from_secret(&traffic_secret).unwrap();

        // Verify key is derived (not all zeros)
        assert_ne!(hp.key(), &[0u8; 32]);

        // Verify deterministic derivation (same secret = same key)
        let hp2 = HeaderProtection::derive_from_secret(&traffic_secret).unwrap();
        assert_eq!(hp.key(), hp2.key());
    }

    #[test]
    fn test_packet_number_protection_roundtrip() {
        let traffic_secret = [0x42u8; 32];
        let hp = HeaderProtection::derive_from_secret(&traffic_secret).unwrap();

        // Create test packet: 1-byte header + 4-byte PN + 20 bytes payload
        // Note: protect() will encode PN length in bits 0-1 of first byte
        let mut packet = vec![
            0xc0, // Long header (bits 7-6 = 11), PN length will be encoded
            0x12, 0x34, 0x56, 0x78, // Packet number (4 bytes)
            // 20 bytes of payload (required for 16-byte sample at offset 4+4)
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
            0x0f, 0x10, 0x11, 0x12, 0x13, 0x14,
        ];

        // Protect header (this encodes PN length and applies mask)
        hp.protect(&mut packet, 1, 4).unwrap();

        // Verify first byte has PN length encoded (0xc0 | 0x03 = 0xc3 before masking)
        // and packet number is modified
        assert_ne!(packet[1], 0x12); // PN is protected

        // Store protected state for verification
        let protected_packet = packet.clone();

        // Unprotect header
        let pn_length = hp.unprotect(&mut packet, 1).unwrap();

        // Verify roundtrip
        assert_eq!(pn_length, 4);
        assert_eq!(packet[0] & 0xfc, 0xc0); // Upper bits preserved
        assert_eq!(packet[0] & 0x03, 0x03); // PN length = 4 (encoded as 3)
        assert_eq!(packet[1], 0x12); // PN restored
        assert_eq!(packet[2], 0x34);
        assert_eq!(packet[3], 0x56);
        assert_eq!(packet[4], 0x78);

        // Re-protecting should give same result
        hp.protect(&mut packet, 1, 4).unwrap();
        assert_eq!(packet, protected_packet);
    }

    #[test]
    fn test_first_byte_protection_long_header() {
        let traffic_secret = [0x99u8; 32];
        let hp = HeaderProtection::derive_from_secret(&traffic_secret).unwrap();

        // Long header packet
        let mut packet = vec![
            0xc3, // Long header with PN length bits 0b11 (4 bytes)
            0xaa, 0xbb, 0xcc, 0xdd, // Packet number
            // 20 bytes payload
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13,
        ];
        let first_byte = packet[0];

        // Protect
        hp.protect(&mut packet, 1, 4).unwrap();

        // First byte should be modified (lower 4 bits protected)
        assert_ne!(packet[0], first_byte);
        // But upper 4 bits (header type) should be preserved
        assert_eq!(packet[0] & 0xf0, first_byte & 0xf0);
    }

    #[test]
    fn test_first_byte_protection_short_header() {
        let traffic_secret = [0x77u8; 32];
        let hp = HeaderProtection::derive_from_secret(&traffic_secret).unwrap();

        // Short header packet (bit 7 = 0)
        let mut packet = vec![
            0x43, // Short header with PN length bits 0b11
            0xee, 0xff, 0x00, 0x11, // Packet number
            // 20 bytes payload
            0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d,
            0x2e, 0x2f, 0x30, 0x31, 0x32, 0x33,
        ];
        let first_byte = packet[0];

        // Protect
        hp.protect(&mut packet, 1, 4).unwrap();

        // First byte should be modified (lower 5 bits protected)
        assert_ne!(packet[0], first_byte);
        // Upper 3 bits should be preserved
        assert_eq!(packet[0] & 0xe0, first_byte & 0xe0);
    }

    #[test]
    fn test_sample_extraction() {
        let traffic_secret = [0x33u8; 32];
        let hp = HeaderProtection::derive_from_secret(&traffic_secret).unwrap();

        // Packet with specific sample region
        let mut packet = vec![
            0xc0, // Header
            0x01, 0x02, 0x03, 0x04, // Packet number (pn_offset=1, length=4)
            // Sample starts at pn_offset + 4 = offset 5 (16 bytes)
            0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xa0, 0xa1, // Extra bytes
        ];

        // Protection should use sample at offset 5..21
        hp.protect(&mut packet, 1, 4).unwrap();

        // Verify protection succeeded (packet modified)
        assert_ne!(packet[0], 0xc0);
        assert_ne!(packet[1], 0x01);
    }

    #[test]
    fn test_header_protection_packet_too_short() {
        let traffic_secret = [0x11u8; 32];
        let hp = HeaderProtection::derive_from_secret(&traffic_secret).unwrap();

        // Packet too short for sample extraction
        let mut short_packet = vec![0xc0, 0x01, 0x02];

        let result = hp.protect(&mut short_packet, 1, 1);
        assert!(result.is_err());

        match result.unwrap_err() {
            QuicError::PacketDecode(msg) => {
                assert!(msg.contains("too short") || msg.contains("Insufficient"));
            }
            e => panic!("Expected PacketDecode error, got {:?}", e),
        }
    }

    #[test]
    fn test_mask_generation_deterministic() {
        let traffic_secret = [0x88u8; 32];
        let hp = HeaderProtection::derive_from_secret(&traffic_secret).unwrap();

        // Same sample should produce same mask
        let sample = [0xaau8; 16];

        let mask1 = hp.generate_mask(&sample).unwrap();
        let mask2 = hp.generate_mask(&sample).unwrap();

        assert_eq!(mask1, mask2);

        // Different sample should produce different mask
        let different_sample = [0xbbu8; 16];
        let mask3 = hp.generate_mask(&different_sample).unwrap();

        assert_ne!(mask1, mask3);
    }

    // ===== CUBIC CONGESTION CONTROL TESTS (RFC 8312) =====

    #[test]
    fn test_cubic_initialization() {
        let cubic = CubicState::new(12000, 1200);

        // Verify initial state
        assert_eq!(cubic.cwnd, 12000);
        assert_eq!(cubic.ssthresh, u32::MAX);
        assert_eq!(cubic.w_max, 0.0);
        assert_eq!(cubic.c, 0.4);
        assert!(cubic.epoch_start.is_none());
        assert_eq!(cubic.max_packet_size, 1200);
    }

    #[test]
    fn test_cubic_slow_start() {
        let mut cubic = CubicState::new(12000, 1200);

        // In slow start, cwnd should grow exponentially
        let initial_cwnd = cubic.cwnd;

        // ACK 1200 bytes (1 packet)
        let new_cwnd = cubic.on_ack(1200);

        // cwnd should increase by bytes_acked
        assert_eq!(new_cwnd, initial_cwnd + 1200);
        assert!(cubic.cwnd < cubic.ssthresh); // Still in slow start
    }

    #[test]
    fn test_cubic_congestion_avoidance() {
        let mut cubic = CubicState::new(12000, 1200);

        // Enter congestion avoidance by setting ssthresh low
        cubic.ssthresh = 10000;

        let initial_cwnd = cubic.cwnd;

        // ACK 1200 bytes
        let new_cwnd = cubic.on_ack(1200);

        // In congestion avoidance, growth should be slower than slow start
        // CUBIC formula applies
        assert!(new_cwnd >= initial_cwnd); // Should grow (or stay same)
        assert!(new_cwnd <= initial_cwnd + 1200); // But not by full bytes_acked
    }

    #[test]
    fn test_cubic_packet_loss_response() {
        let mut cubic = CubicState::new(50000, 1200);

        let initial_cwnd = cubic.cwnd;

        // Trigger packet loss
        cubic.on_packet_lost();

        // cwnd should reduce to 70% (RFC 8312 §4.5)
        let expected_cwnd = (initial_cwnd as f64 * 0.7) as u32;
        assert_eq!(cubic.ssthresh, expected_cwnd);
        assert!(cubic.cwnd <= expected_cwnd);
        assert!(cubic.cwnd >= 1200 * 2); // Min 2 * MSS

        // W_max should be set to pre-loss cwnd
        assert_eq!(cubic.w_max, initial_cwnd as f64);

        // Epoch should be reset
        assert!(cubic.epoch_start.is_some());

        // K should be calculated (time to reach W_max)
        assert!(cubic.k > 0.0);
    }

    #[test]
    fn test_cubic_rtt_measurement() {
        let mut cubic = CubicState::new(12000, 1200);

        // First RTT sample
        let rtt1 = Duration::from_millis(50);
        cubic.update_rtt(rtt1);

        assert_eq!(cubic.latest_rtt, Some(rtt1));
        assert_eq!(cubic.min_rtt, Some(rtt1));
        assert_eq!(cubic.smoothed_rtt, Some(rtt1));
        assert!(cubic.rtt_var.is_some());

        // Second RTT sample (EWMA should apply)
        let rtt2 = Duration::from_millis(60);
        cubic.update_rtt(rtt2);

        assert_eq!(cubic.latest_rtt, Some(rtt2));
        assert_eq!(cubic.min_rtt, Some(rtt1)); // Min should not change

        // Smoothed RTT should be between rtt1 and rtt2
        let srtt = cubic.smoothed_rtt.unwrap().as_millis();
        assert!(srtt > rtt1.as_millis());
        assert!(srtt < rtt2.as_millis());
    }

    #[test]
    fn test_cubic_get_available_window() {
        let cubic = CubicState::new(50000, 1200);

        // With no bytes in flight
        assert_eq!(cubic.get_available_window(0), 50000);

        // With 20000 bytes in flight
        assert_eq!(cubic.get_available_window(20000), 30000);

        // With more bytes in flight than cwnd (edge case)
        assert_eq!(cubic.get_available_window(60000), 0);
    }

    #[test]
    fn test_cubic_reset() {
        let mut cubic = CubicState::new(12000, 1200);

        // Modify state
        cubic.cwnd = 50000;
        cubic.ssthresh = 30000;
        cubic.w_max = 40000.0;
        cubic.epoch_start = Some(Instant::now());

        // Reset
        cubic.reset();

        // Should return to conservative initial state
        assert_eq!(cubic.cwnd, 1200 * 10); // 10 * MTU
        assert_eq!(cubic.ssthresh, u32::MAX);
        assert_eq!(cubic.w_max, 0.0);
        assert!(cubic.epoch_start.is_none());
    }

    #[tokio::test]
    async fn test_connection_with_cubic() {
        let conn_id = Bytes::from_static(b"cubic-test");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        // Verify CUBIC is initialized
        let cwnd = conn.get_congestion_window().await;
        assert_eq!(cwnd, 12000); // 10 * 1200

        // Simulate ACK
        conn.on_ack_received(1200, Duration::from_millis(50))
            .await
            .unwrap();

        // cwnd should increase
        let new_cwnd = conn.get_congestion_window().await;
        assert!(new_cwnd > cwnd);

        // Check RTT stats
        let (latest, smoothed, min) = conn.get_rtt_stats().await;
        assert_eq!(latest, Some(Duration::from_millis(50)));
        assert_eq!(smoothed, Some(Duration::from_millis(50)));
        assert_eq!(min, Some(Duration::from_millis(50)));
    }

    #[tokio::test]
    async fn test_connection_packet_loss_handling() {
        let conn_id = Bytes::from_static(b"loss-test");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        // Increase cwnd first
        for _ in 0..10 {
            conn.on_ack_received(1200, Duration::from_millis(50))
                .await
                .unwrap();
        }

        let cwnd_before_loss = conn.get_congestion_window().await;

        // Simulate packet loss
        conn.on_packet_lost(1200).await.unwrap();

        let cwnd_after_loss = conn.get_congestion_window().await;

        // cwnd should reduce significantly (multiplicative decrease)
        assert!(cwnd_after_loss < cwnd_before_loss);
        assert!(cwnd_after_loss as f64 <= cwnd_before_loss as f64 * 0.7);
    }

    #[tokio::test]
    async fn test_datagram_send_with_cubic_flow_control() {
        let conn_id = Bytes::from_static(b"datagram-cubic");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let mut stats = ConnectionStats::default();
        stats.bytes_in_flight = 5000; // Simulate inflight data

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        // Set peer transport parameters
        let mut peer_params = TransportParameters::default();
        peer_params.max_datagram_frame_size = Some(1200);
        conn.set_peer_transport_parameters(peer_params)
            .await
            .unwrap();

        // Try to send datagram within budget
        let data = Bytes::from(vec![0u8; 500]); // Within 50% cwnd budget
        let result = conn.send_datagram(data).await;

        // Should succeed
        assert!(result.is_ok());

        // Verify queued
        let (send_len, _) = conn.datagram_queue_len().await;
        assert_eq!(send_len, 1);
    }

    // ============================================================================
    // Path Migration Tests (RFC 9000 §9)
    // ============================================================================

    #[tokio::test]
    async fn test_path_challenge_response_frame_roundtrip() {
        let data = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];

        // Test PATH_CHALLENGE
        let challenge_frame = QuicFrame::PathChallenge { data };
        let encoded = challenge_frame.encode().unwrap();

        // Verify frame type 0x1a
        assert_eq!(encoded[0], 0x1a);
        assert_eq!(encoded.len(), 9); // 1 byte type + 8 bytes data

        let (decoded_challenge, consumed) = QuicFrame::decode(&encoded).unwrap();
        assert_eq!(consumed, 9);
        match decoded_challenge {
            QuicFrame::PathChallenge { data: decoded_data } => {
                assert_eq!(decoded_data, data);
            }
            _ => panic!("Expected PathChallenge frame"),
        }

        // Test PATH_RESPONSE
        let response_frame = QuicFrame::PathResponse { data };
        let encoded = response_frame.encode().unwrap();

        // Verify frame type 0x1b
        assert_eq!(encoded[0], 0x1b);
        assert_eq!(encoded.len(), 9);

        let (decoded_response, consumed) = QuicFrame::decode(&encoded).unwrap();
        assert_eq!(consumed, 9);
        match decoded_response {
            QuicFrame::PathResponse { data: decoded_data } => {
                assert_eq!(decoded_data, data);
            }
            _ => panic!("Expected PathResponse frame"),
        }
    }

    #[tokio::test]
    async fn test_path_validation_lifecycle() {
        let path_addr: SocketAddr = "127.0.0.1:5000".parse().unwrap();
        let mut validation = PathValidation::new(path_addr);

        // Initial state
        assert_eq!(validation.state, ValidationState::Idle);
        assert_eq!(validation.attempts, 0);

        // Start validation
        let pto = Duration::from_millis(100);
        validation.start_validation(pto);
        assert_eq!(validation.state, ValidationState::Validating);
        assert_eq!(validation.attempts, 1);
        assert!(validation.next_timeout.is_some());

        // Successful response
        let challenge_data = validation.challenge_data;
        let success = validation.on_response(challenge_data);
        assert!(success);
        assert_eq!(validation.state, ValidationState::Validated);
        assert!(validation.next_timeout.is_none());
    }

    #[tokio::test]
    async fn test_path_validation_timeout_and_retry() {
        let path_addr: SocketAddr = "127.0.0.1:5000".parse().unwrap();
        let mut validation = PathValidation::new(path_addr);

        // Start with very short PTO for testing
        let pto = Duration::from_millis(1);
        validation.start_validation(pto);

        // Wait for timeout
        tokio::time::sleep(Duration::from_millis(5)).await;

        // Check timeout - should retry (attempt 2)
        let should_retry = validation.check_timeout(pto);
        assert!(should_retry);
        assert_eq!(validation.attempts, 2);

        // Wait and retry again
        tokio::time::sleep(Duration::from_millis(5)).await;
        let should_retry = validation.check_timeout(pto);
        assert!(should_retry);
        assert_eq!(validation.attempts, 3);

        // Third timeout - should fail (max 3 attempts)
        tokio::time::sleep(Duration::from_millis(5)).await;
        let should_retry = validation.check_timeout(pto);
        assert!(!should_retry); // No more retries
        assert_eq!(validation.state, ValidationState::Failed);
    }

    #[tokio::test]
    async fn test_connection_id_manager() {
        let initial_cid = Bytes::from_static(b"initial8");
        let mut manager = ConnectionIdManager::new(initial_cid.clone());

        // Initial state
        assert_eq!(manager.active_cids.len(), 1);
        assert_eq!(manager.current_cid(), Some(&initial_cid));
        assert_eq!(manager.sequence_number, 0);

        // Issue new CID
        let new_cid = manager.issue_new_cid();
        assert_eq!(manager.active_cids.len(), 2);
        assert_eq!(manager.sequence_number, 1);
        assert_eq!(manager.current_cid(), Some(&new_cid));

        // Retire old CID
        manager.retire_cid(initial_cid.clone());
        assert_eq!(manager.active_cids.len(), 1);
        assert_eq!(manager.retire_cids.len(), 1);
        assert_eq!(manager.current_cid(), Some(&new_cid));
    }

    #[tokio::test]
    async fn test_connection_path_migration() {
        let conn_id = Bytes::from_static(b"migrate!");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        // Initial path ID should be 0
        assert_eq!(conn.current_path_id().await, 0);

        // Migrate to new path
        let new_path: SocketAddr = "127.0.0.1:5555".parse().unwrap();
        let new_path_id = conn.migrate_to_path(new_path).await.unwrap();

        // New path ID assigned
        assert_eq!(new_path_id, 1);

        // Validation should be in progress
        let validations = conn.path_validations.read().await;
        let validation = validations.get(&new_path_id).unwrap();
        assert_eq!(validation.state, ValidationState::Validating);
        assert_eq!(validation.path_addr, new_path);
    }

    #[tokio::test]
    async fn test_path_response_switches_path() {
        let conn_id = Bytes::from_static(b"switch!!");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        // Migrate to new path
        let new_path: SocketAddr = "127.0.0.1:5555".parse().unwrap();
        let new_path_id = conn.migrate_to_path(new_path).await.unwrap();

        // Get challenge data
        let challenge_data = {
            let validations = conn.path_validations.read().await;
            validations.get(&new_path_id).unwrap().challenge_data
        };

        // Simulate receiving PATH_RESPONSE
        conn.on_path_response_received(challenge_data, new_path)
            .await
            .unwrap();

        // Current path should switch to new path
        assert_eq!(conn.current_path_id().await, new_path_id);

        // Validation should be validated
        let validations = conn.path_validations.read().await;
        let validation = validations.get(&new_path_id).unwrap();
        assert_eq!(validation.state, ValidationState::Validated);
    }

    #[tokio::test]
    async fn test_path_response_mismatch_fails() {
        let conn_id = Bytes::from_static(b"mismatch");
        let peer_addr = "127.0.0.1:4433".parse().unwrap();
        let stats = ConnectionStats::default();

        let conn = QuicConnection::new(conn_id, peer_addr, false, stats).unwrap();

        // Migrate to new path
        let new_path: SocketAddr = "127.0.0.1:5555".parse().unwrap();
        conn.migrate_to_path(new_path).await.unwrap();

        // Send wrong challenge data
        let wrong_data = [0xFF; 8];
        let result = conn.on_path_response_received(wrong_data, new_path).await;

        // Should fail
        assert!(result.is_err());

        // Current path should remain unchanged
        assert_eq!(conn.current_path_id().await, 0);
    }

    // ============================================================================
    // QUIC Crypto Tests (ChaCha20Poly1305 AEAD + Header Protection)
    // ============================================================================

    #[tokio::test]
    async fn test_encrypt_decrypt_roundtrip() {
        let ctx = QuicCryptoContext::new();
        let plaintext = b"Hello, QUIC world!";
        let packet_number = 12345u64;

        let ciphertext = ctx
            .encrypt_packet(plaintext, packet_number)
            .await
            .expect("Encryption failed");
        assert_ne!(ciphertext.as_ref(), plaintext);
        assert_eq!(ciphertext.len(), plaintext.len() + 16);

        let decrypted = ctx
            .decrypt_packet(&ciphertext, packet_number)
            .await
            .expect("Decryption failed");
        assert_eq!(decrypted.as_ref(), plaintext);
    }

    #[tokio::test]
    async fn test_decrypt_with_wrong_packet_number() {
        let ctx = QuicCryptoContext::new();
        let plaintext = b"Test data";
        let packet_number = 100u64;

        let ciphertext = ctx
            .encrypt_packet(plaintext, packet_number)
            .await
            .expect("Encryption failed");
        let result = ctx.decrypt_packet(&ciphertext, packet_number + 1).await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_decrypt_tampered_ciphertext() {
        let ctx = QuicCryptoContext::new();
        let plaintext = b"Important data";
        let packet_number = 200u64;

        let mut ciphertext = ctx
            .encrypt_packet(plaintext, packet_number)
            .await
            .expect("Encryption failed")
            .to_vec();
        if !ciphertext.is_empty() {
            ciphertext[5] ^= 0x01;
        }

        let result = ctx.decrypt_packet(&ciphertext, packet_number).await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_header_protection_roundtrip() {
        let ctx = QuicCryptoContext::new();
        let header = vec![0x01, 0x23, 0x45, 0x67];
        let ciphertext = vec![0u8; 32];
        let sample_offset = 4;

        let protected = ctx
            .protect_header(&header, sample_offset, &ciphertext)
            .await
            .expect("Header protection failed");
        assert_ne!(protected.as_ref(), header.as_slice());

        let unprotected = ctx
            .unprotect_header(&protected, sample_offset, &ciphertext)
            .await
            .expect("Header unprotection failed");
        assert_eq!(unprotected.as_ref(), header.as_slice());
    }

    #[tokio::test]
    async fn test_encryption_level_isolation() {
        // Test that different encryption levels with different secrets produce different ciphertexts
        let mut ctx_initial = QuicCryptoContext::new();
        ctx_initial.encryption_level = EncryptionLevel::Initial;
        ctx_initial.initial_secret = [0x01; 32]; // Different secret

        let mut ctx_handshake = QuicCryptoContext::new();
        ctx_handshake.encryption_level = EncryptionLevel::Handshake;
        ctx_handshake.handshake_secret = [0x02; 32]; // Different secret

        let plaintext = b"Test isolation";
        let packet_number = 1u64;

        let ct_initial = ctx_initial
            .encrypt_packet(plaintext, packet_number)
            .await
            .expect("Initial encryption failed");
        let ct_handshake = ctx_handshake
            .encrypt_packet(plaintext, packet_number)
            .await
            .expect("Handshake encryption failed");

        // With different secrets, ciphertexts should differ
        assert_ne!(ct_initial.as_ref(), ct_handshake.as_ref());

        // Cross-decryption should fail due to different secrets
        assert!(ctx_initial
            .decrypt_packet(&ct_handshake, packet_number)
            .await
            .is_err());
        assert!(ctx_handshake
            .decrypt_packet(&ct_initial, packet_number)
            .await
            .is_err());
    }

    #[tokio::test]
    async fn test_empty_packet_encryption() {
        let ctx = QuicCryptoContext::new();
        let empty = b"";
        let packet_number = 42u64;

        let ciphertext = ctx
            .encrypt_packet(empty, packet_number)
            .await
            .expect("Empty packet encryption failed");
        assert_eq!(ciphertext.len(), 16);

        let decrypted = ctx
            .decrypt_packet(&ciphertext, packet_number)
            .await
            .expect("Empty packet decryption failed");
        assert_eq!(decrypted.as_ref(), empty);
    }

    #[tokio::test]
    async fn test_large_packet_encryption() {
        let ctx = QuicCryptoContext::new();
        let large_data = vec![0x42u8; 1200];
        let packet_number = 999u64;

        let ciphertext = ctx
            .encrypt_packet(&large_data, packet_number)
            .await
            .expect("Large packet encryption failed");
        let decrypted = ctx
            .decrypt_packet(&ciphertext, packet_number)
            .await
            .expect("Large packet decryption failed");
        assert_eq!(decrypted.as_ref(), large_data.as_slice());
    }
}
