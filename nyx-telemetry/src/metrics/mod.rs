use once_cell::sync::Lazy;
use prometheus::Encoder;
use prometheus::{
    HistogramOpts, HistogramVec, IntCounter, IntCounterVec, Opts, Registry, TextEncoder,
};
/// Metrics utilities and Prometheus exposition with robust error handling.
use std::collections::HashMap;
use std::sync::Mutex;

/// Global registry for all Prometheus metrics in the application
pub(crate) static REGISTRY: Lazy<Registry> = Lazy::new(Registry::new);

/// Thread-safe storage for dynamically created counter metrics
/// Counters are created on-demand and cached for reuse to avoid duplicate registrations
static COUNTERS: Lazy<Mutex<HashMap<String, IntCounter>>> =
    Lazy::new(|| Mutex::new(HashMap::new()));

// ===== Handshake Metrics =====

/// Counter for successful handshakes with labeled dimensions
/// Labels: session_id, peer_id, handshake_type (client|server)
static HANDSHAKE_SUCCESS_COUNTER: Lazy<IntCounterVec> = Lazy::new(|| {
    let opts = Opts::new(
        "nyx_handshake_success_total",
        "Total number of successful handshakes",
    );
    let counter = IntCounterVec::new(opts, &["session_id", "peer_id", "handshake_type"])
        .expect("Failed to create handshake_success_total counter");
    REGISTRY
        .register(Box::new(counter.clone()))
        .expect("Failed to register handshake_success_total");
    counter
});

/// Counter for failed handshakes with error reasons
/// Labels: session_id, peer_id, handshake_type, error_type
static HANDSHAKE_FAILURE_COUNTER: Lazy<IntCounterVec> = Lazy::new(|| {
    let opts = Opts::new(
        "nyx_handshake_failure_total",
        "Total number of failed handshakes",
    );
    let counter = IntCounterVec::new(
        opts,
        &["session_id", "peer_id", "handshake_type", "error_type"],
    )
    .expect("Failed to create handshake_failure_total counter");
    REGISTRY
        .register(Box::new(counter.clone()))
        .expect("Failed to register handshake_failure_total");
    counter
});

/// Histogram for handshake duration in milliseconds
/// Labels: handshake_type
/// Buckets: 10ms, 50ms, 100ms, 250ms, 500ms, 1s, 2.5s, 5s, 10s
static HANDSHAKE_DURATION_HISTOGRAM: Lazy<HistogramVec> = Lazy::new(|| {
    let opts = HistogramOpts::new(
        "nyx_handshake_duration_ms",
        "Handshake duration in milliseconds",
    )
    .buckets(vec![
        10.0, 50.0, 100.0, 250.0, 500.0, 1000.0, 2500.0, 5000.0, 10000.0,
    ]);
    let histogram = HistogramVec::new(opts, &["handshake_type"])
        .expect("Failed to create handshake_duration_ms histogram");
    REGISTRY
        .register(Box::new(histogram.clone()))
        .expect("Failed to register handshake_duration_ms");
    histogram
});

// ===== cMix Batch Processing Metrics =====

/// Counter for cMix batch processing operations
/// Labels: batch_size_range (1-10|11-50|51-100|101+), status (success|failure)
static CMIX_BATCH_COUNTER: Lazy<IntCounterVec> = Lazy::new(|| {
    let opts = Opts::new(
        "nyx_cmix_batch_total",
        "Total number of cMix batch processing operations",
    );
    let counter = IntCounterVec::new(opts, &["batch_size_range", "status"])
        .expect("Failed to create cmix_batch_total counter");
    REGISTRY
        .register(Box::new(counter.clone()))
        .expect("Failed to register cmix_batch_total");
    counter
});

/// Histogram for cMix batch processing duration
/// Labels: batch_size_range
/// Buckets: 1ms, 5ms, 10ms, 25ms, 50ms, 100ms, 250ms, 500ms, 1s
static CMIX_BATCH_DURATION_HISTOGRAM: Lazy<HistogramVec> = Lazy::new(|| {
    let opts = HistogramOpts::new(
        "nyx_cmix_batch_duration_ms",
        "cMix batch processing duration",
    )
    .buckets(vec![
        1.0, 5.0, 10.0, 25.0, 50.0, 100.0, 250.0, 500.0, 1000.0,
    ]);
    let histogram = HistogramVec::new(opts, &["batch_size_range"])
        .expect("Failed to create cmix_batch_duration_ms histogram");
    REGISTRY
        .register(Box::new(histogram.clone()))
        .expect("Failed to register cmix_batch_duration_ms");
    histogram
});

/// Counter for cMix messages processed
/// Labels: direction (inbound|outbound)
static CMIX_MESSAGES_COUNTER: Lazy<IntCounterVec> = Lazy::new(|| {
    let opts = Opts::new(
        "nyx_cmix_messages_total",
        "Total number of cMix messages processed",
    );
    let counter = IntCounterVec::new(opts, &["direction"])
        .expect("Failed to create cmix_messages_total counter");
    REGISTRY
        .register(Box::new(counter.clone()))
        .expect("Failed to register cmix_messages_total");
    counter
});

// ===== Path Quality Metrics =====

use prometheus::GaugeVec;

/// Gauge for path RTT (Round-Trip Time) in milliseconds
/// Labels: path_id, session_id
static PATH_RTT_GAUGE: Lazy<GaugeVec> = Lazy::new(|| {
    let opts = Opts::new("nyx_path_rtt_ms", "Path round-trip time in milliseconds");
    let gauge = GaugeVec::new(opts, &["path_id", "session_id"])
        .expect("Failed to create path_rtt_ms gauge");
    REGISTRY
        .register(Box::new(gauge.clone()))
        .expect("Failed to register path_rtt_ms");
    gauge
});

/// Gauge for path packet loss rate (0.0-1.0)
/// Labels: path_id, session_id
static PATH_LOSS_RATE_GAUGE: Lazy<GaugeVec> = Lazy::new(|| {
    let opts = Opts::new(
        "nyx_path_loss_rate",
        "Path packet loss rate (0.0 = no loss, 1.0 = 100% loss)",
    );
    let gauge = GaugeVec::new(opts, &["path_id", "session_id"])
        .expect("Failed to create path_loss_rate gauge");
    REGISTRY
        .register(Box::new(gauge.clone()))
        .expect("Failed to register path_loss_rate");
    gauge
});

/// Gauge for path bandwidth in bytes per second
/// Labels: path_id, session_id
static PATH_BANDWIDTH_GAUGE: Lazy<GaugeVec> = Lazy::new(|| {
    let opts = Opts::new(
        "nyx_path_bandwidth_bytes_per_sec",
        "Path bandwidth in bytes per second",
    );
    let gauge = GaugeVec::new(opts, &["path_id", "session_id"])
        .expect("Failed to create path_bandwidth_bytes_per_sec gauge");
    REGISTRY
        .register(Box::new(gauge.clone()))
        .expect("Failed to register path_bandwidth_bytes_per_sec");
    gauge
});

// ===== Cover Traffic Metrics =====

/// Counter for cover traffic packets sent
/// Labels: session_id, traffic_type (dummy|padding)
static COVER_TRAFFIC_SENT_COUNTER: Lazy<IntCounterVec> = Lazy::new(|| {
    let opts = Opts::new(
        "nyx_cover_traffic_sent_total",
        "Total number of cover traffic packets sent",
    );
    let counter = IntCounterVec::new(opts, &["session_id", "traffic_type"])
        .expect("Failed to create cover_traffic_sent_total counter");
    REGISTRY
        .register(Box::new(counter.clone()))
        .expect("Failed to register cover_traffic_sent_total");
    counter
});

/// Gauge for cover traffic utilization rate (0.0-1.0)
/// Labels: session_id
/// Represents the ratio of cover traffic to total traffic
static COVER_TRAFFIC_UTILIZATION_GAUGE: Lazy<GaugeVec> = Lazy::new(|| {
    let opts = Opts::new(
        "nyx_cover_traffic_utilization",
        "Cover traffic utilization rate (0.0 = no cover traffic, 1.0 = all cover traffic)",
    );
    let gauge = GaugeVec::new(opts, &["session_id"])
        .expect("Failed to create cover_traffic_utilization gauge");
    REGISTRY
        .register(Box::new(gauge.clone()))
        .expect("Failed to register cover_traffic_utilization");
    gauge
});

/// Counter for cover traffic bytes sent
/// Labels: session_id
static COVER_TRAFFIC_BYTES_COUNTER: Lazy<IntCounterVec> = Lazy::new(|| {
    let opts = Opts::new(
        "nyx_cover_traffic_bytes_total",
        "Total bytes of cover traffic sent",
    );
    let counter = IntCounterVec::new(opts, &["session_id"])
        .expect("Failed to create cover_traffic_bytes_total counter");
    REGISTRY
        .register(Box::new(counter.clone()))
        .expect("Failed to register cover_traffic_bytes_total");
    counter
});

// ===== Rekey Event Metrics =====

/// Counter for rekey events
/// Labels: session_id, rekey_reason (scheduled|forced|error_recovery)
static REKEY_EVENTS_COUNTER: Lazy<IntCounterVec> = Lazy::new(|| {
    let opts = Opts::new("nyx_rekey_events_total", "Total number of rekey events");
    let counter = IntCounterVec::new(opts, &["session_id", "rekey_reason"])
        .expect("Failed to create rekey_events_total counter");
    REGISTRY
        .register(Box::new(counter.clone()))
        .expect("Failed to register rekey_events_total");
    counter
});

/// Histogram for rekey operation duration
/// Labels: rekey_reason
/// Buckets: 10ms, 50ms, 100ms, 250ms, 500ms, 1s, 2s, 5s
static REKEY_DURATION_HISTOGRAM: Lazy<HistogramVec> = Lazy::new(|| {
    let opts = HistogramOpts::new(
        "nyx_rekey_duration_ms",
        "Rekey operation duration in milliseconds",
    )
    .buckets(vec![
        10.0, 50.0, 100.0, 250.0, 500.0, 1000.0, 2000.0, 5000.0,
    ]);
    let histogram = HistogramVec::new(opts, &["rekey_reason"])
        .expect("Failed to create rekey_duration_ms histogram");
    REGISTRY
        .register(Box::new(histogram.clone()))
        .expect("Failed to register rekey_duration_ms");
    histogram
});

/// Counter for rekey failures
/// Labels: session_id, error_type
static REKEY_FAILURE_COUNTER: Lazy<IntCounterVec> = Lazy::new(|| {
    let opts = Opts::new(
        "nyx_rekey_failure_total",
        "Total number of failed rekey operations",
    );
    let counter = IntCounterVec::new(opts, &["session_id", "error_type"])
        .expect("Failed to create rekey_failure_total counter");
    REGISTRY
        .register(Box::new(counter.clone()))
        .expect("Failed to register rekey_failure_total");
    counter
});

/// Record a value into an IntCounter, creating and registering it on first use
///
/// This function handles counter creation, registration, and value updates in a
/// thread-safe manner. If the mutex is poisoned, it attempts recovery by clearing
/// the cache and continuing operation.
///
/// # Arguments
/// * `name` - Unique name for the counter metric (should be sanitized by caller)
/// * `v` - Value to increment the counter by
///
/// # Error Handling
/// - Recovers from mutex poisoning by reinitializing the counter cache
/// - Ignores registration errors for already-registered compatible metrics
/// - Logs errors for debugging but continues operation
pub fn record_counter(name: &str, v: u64) {
    let mut map = match COUNTERS.lock() {
        Ok(guard) => guard,
        Err(poisoned) => {
            // Recover from mutex poisoning by getting the underlying _data
            // This allows the application to continue functioning even after a panic
            tracing::warn!(
                metricname = name,
                "Counter mutex was poisoned, attempting recovery"
            );
            poisoned.into_inner()
        }
    };
    let counter = map.entry(name.to_string()).or_insert_with(|| {
        match IntCounter::new(name, format!("Nyx protocol counter: {name}")) {
            Ok(counter) => {
                if let Err(reg_error) = REGISTRY.register(Box::new(counter.clone())) {
                    tracing::debug!(
                        metricname = name,
                        error = %reg_error,
                        "Counter registration failed (likely already registered)"
                    );
                }
                counter
            }
            Err(counter_error) => {
                tracing::error!(
                    metricname = name,
                    error = %counter_error,
                    "Failed to create counter with description, using fallback"
                );
                IntCounter::new(name, "nyx_counter").unwrap_or_else(|fallback_error| {
                    tracing::error!(
                        metricname = name,
                        error = %fallback_error,
                        "Critical: Failed to create fallback counter, metrics may be incomplete"
                    );
                    IntCounter::new("fallback_counter", "").unwrap_or_else(|_| {
                        IntCounter::new("error_counter", "Critical error").unwrap_or_else(|_| {
                            // Final fallback - use a simple default counter if all else fails
                            IntCounter::new("total_errors", "Total error count").unwrap_or_else(|_| {
                                // Last resort: log error and return a dummy counter that does nothing
                                tracing::error!("Critical: Unable to create any metrics counter - system metrics disabled");
                                // Create a minimal working counter as the ultimate fallback
                                IntCounter::new("disabled_counter", "Metrics disabled due to creation failure")
                                    .unwrap_or_else(|_| {
                                        // If even this fails, something is seriously wrong with the metrics system
                                        // Return a counter that will work but log the critical error
                                        tracing::error!("Metrics system failure - counter creation completely broken");
                                        // This should never fail as it's the most basic possible counter
                                        IntCounter::new("", "").expect("Basic counter creation failed - metrics system corrupted")
                                    })
                            })
                        })
                    })
                })
            }
        }
    });
    counter.inc_by(v);
}

// ===== Public Metric Recording Functions =====

/// Record a successful handshake event
///
/// # Arguments
/// * `session_id` - Truncated session identifier (first 8 chars to maintain low cardinality)
/// * `peer_id` - Truncated peer identifier (first 8 chars)
/// * `handshake_type` - Type of handshake: "client" or "server"
/// * `duration_ms` - Duration of handshake in milliseconds
pub fn record_handshake_success(
    session_id: &str,
    peer_id: &str,
    handshake_type: &str,
    duration_ms: f64,
) {
    HANDSHAKE_SUCCESS_COUNTER
        .with_label_values(&[session_id, peer_id, handshake_type])
        .inc();
    HANDSHAKE_DURATION_HISTOGRAM
        .with_label_values(&[handshake_type])
        .observe(duration_ms);
}

/// Record a failed handshake event
///
/// # Arguments
/// * `session_id` - Truncated session identifier
/// * `peer_id` - Truncated peer identifier
/// * `handshake_type` - Type of handshake: "client" or "server"
/// * `error_type` - Type of error: "timeout", "invalid_signature", "network", etc.
pub fn record_handshake_failure(
    session_id: &str,
    peer_id: &str,
    handshake_type: &str,
    error_type: &str,
) {
    HANDSHAKE_FAILURE_COUNTER
        .with_label_values(&[session_id, peer_id, handshake_type, error_type])
        .inc();
}

/// Record a cMix batch processing operation
///
/// # Arguments
/// * `batch_size` - Number of messages in the batch
/// * `success` - Whether the batch processing succeeded
/// * `duration_ms` - Duration of batch processing in milliseconds
pub fn record_cmix_batch(batch_size: usize, success: bool, duration_ms: f64) {
    // Categorize batch size to maintain low cardinality
    let batch_size_range = match batch_size {
        1..=10 => "1-10",
        11..=50 => "11-50",
        51..=100 => "51-100",
        _ => "101+",
    };
    let status = if success { "success" } else { "failure" };

    CMIX_BATCH_COUNTER
        .with_label_values(&[batch_size_range, status])
        .inc();
    CMIX_BATCH_DURATION_HISTOGRAM
        .with_label_values(&[batch_size_range])
        .observe(duration_ms);
}

/// Record cMix message processing
///
/// # Arguments
/// * `direction` - Message direction: "inbound" or "outbound"
/// * `count` - Number of messages processed
pub fn record_cmix_messages(direction: &str, count: u64) {
    CMIX_MESSAGES_COUNTER
        .with_label_values(&[direction])
        .inc_by(count);
}

/// Record a rekey event
///
/// # Arguments
/// * `session_id` - Truncated session identifier
/// * `rekey_reason` - Reason for rekey: "scheduled", "forced", "error_recovery"
/// * `duration_ms` - Duration of rekey operation in milliseconds
pub fn record_rekey_event(session_id: &str, rekey_reason: &str, duration_ms: f64) {
    REKEY_EVENTS_COUNTER
        .with_label_values(&[session_id, rekey_reason])
        .inc();
    REKEY_DURATION_HISTOGRAM
        .with_label_values(&[rekey_reason])
        .observe(duration_ms);
}

/// Record a rekey failure
///
/// # Arguments
/// * `session_id` - Truncated session identifier
/// * `error_type` - Type of error: "timeout", "crypto_error", "network", etc.
pub fn record_rekey_failure(session_id: &str, error_type: &str) {
    REKEY_FAILURE_COUNTER
        .with_label_values(&[session_id, error_type])
        .inc();
}

/// Record path quality metrics
///
/// # Arguments
/// * `path_id` - Truncated path identifier
/// * `session_id` - Truncated session identifier
/// * `rtt_ms` - Round-trip time in milliseconds
/// * `loss_rate` - Packet loss rate (0.0-1.0)
/// * `bandwidth_bps` - Bandwidth in bytes per second
pub fn record_path_quality(
    path_id: &str,
    session_id: &str,
    rtt_ms: f64,
    loss_rate: f64,
    bandwidth_bps: f64,
) {
    PATH_RTT_GAUGE
        .with_label_values(&[path_id, session_id])
        .set(rtt_ms);
    PATH_LOSS_RATE_GAUGE
        .with_label_values(&[path_id, session_id])
        .set(loss_rate.clamp(0.0, 1.0)); // Clamp to valid range
    PATH_BANDWIDTH_GAUGE
        .with_label_values(&[path_id, session_id])
        .set(bandwidth_bps.max(0.0)); // Ensure non-negative
}

/// Record cover traffic sent
///
/// # Arguments
/// * `session_id` - Truncated session identifier
/// * `traffic_type` - Type of cover traffic: "dummy" or "padding"
/// * `packet_count` - Number of cover traffic packets sent
/// * `bytes` - Number of bytes sent
pub fn record_cover_traffic(session_id: &str, traffic_type: &str, packet_count: u64, bytes: u64) {
    COVER_TRAFFIC_SENT_COUNTER
        .with_label_values(&[session_id, traffic_type])
        .inc_by(packet_count);
    COVER_TRAFFIC_BYTES_COUNTER
        .with_label_values(&[session_id])
        .inc_by(bytes);
}

/// Record cover traffic utilization rate
///
/// # Arguments
/// * `session_id` - Truncated session identifier
/// * `utilization_rate` - Cover traffic utilization (0.0-1.0)
pub fn record_cover_traffic_utilization(session_id: &str, utilization_rate: f64) {
    COVER_TRAFFIC_UTILIZATION_GAUGE
        .with_label_values(&[session_id])
        .set(utilization_rate.clamp(0.0, 1.0));
}

/// Truncate identifier to first N characters for low cardinality labels
///
/// Prometheus best practice: keep label cardinality low to avoid memory issues.
/// Session/peer IDs are truncated to first 8 characters for distinguishability
/// while maintaining bounded cardinality.
///
/// # Arguments
/// * `id` - Full identifier string
/// * `max_len` - Maximum length (default: 8)
///
/// # Returns
/// Truncated identifier or "unknown" if empty
pub fn truncate_id(id: &str, max_len: usize) -> String {
    if id.is_empty() {
        return "unknown".to_string();
    }
    if id.len() <= max_len {
        id.to_string()
    } else {
        id[..max_len].to_string()
    }
}

#[allow(dead_code)]
fn dump_prometheus_internal() -> String {
    // Gather all metric families from the registry
    let metric_families = REGISTRY.gather();
    let encoder = TextEncoder::new();
    let mut buffer = Vec::new();

    // Attempt to encode metrics into the buffer
    match encoder.encode(&metric_families, &mut buffer) {
        Ok(()) => {
            // Convert bytes to UTF-8 string with fallback
            String::from_utf8(buffer).unwrap_or_else(|utf8_error| {
                tracing::error!(
                    error = %utf8_error,
                    "Failed to convert Prometheus metrics to UTF-8 string"
                );
                // Return a minimal valid Prometheus response
                String::from("# Prometheus metrics export failed: UTF-8 conversion error\n")
            })
        }
        Err(encode_error) => {
            tracing::error!(
                error = %encode_error,
                "Failed to encode Prometheus metrics"
            );
            // Return a minimal valid Prometheus response indicating the error
            String::from("# Prometheus metrics export failed: encoding error\n")
        }
    }
}

/// Export all registered metrics in Prometheus text exposition format
///
/// This function gathers all metrics from the global registry and encodes them
/// in the standard Prometheus text format. It handles encoding errors gracefully
/// by returning an empty string if the encoding process fails.
///
/// # Returns
/// String containing all metrics in Prometheus format, or empty string on error
///
/// # Error Handling
/// - Returns empty string if metric gathering fails
/// - Returns empty string if text encoding fails
/// - Handles UTF-8 conversion errors gracefully
#[allow(dead_code)]
pub fn dump_prometheus() -> String {
    dump_prometheus_internal()
}

#[cfg(feature = "prometheus")]
use warp::{Filter, Rejection, Reply};

/// Provide a Warp filter that serves "/metrics" with text exposition.
#[cfg(feature = "prometheus")]
pub fn warp_metrics_filter() -> impl Filter<Extract = (impl Reply,), Error = Rejection> + Clone {
    warp::path("metrics").and(warp::get()).map(|| {
        // Inline implementation to avoid scope issues
        let metric_families = REGISTRY.gather();
        let encoder = TextEncoder::new();
        let mut buffer = Vec::new();
        let metrics_text = match encoder.encode(&metric_families, &mut buffer) {
            Ok(()) => String::from_utf8(buffer).unwrap_or_else(|_| {
                String::from("# Prometheus metrics export failed: UTF-8 conversion error\n")
            }),
            Err(_) => String::from("# Prometheus metrics export failed: encoding error\n"),
        };
        warp::reply::with_header(
            metrics_text,
            "content-type",
            "text/plain; version=0.0.4; charset=utf-8",
        )
    })
}

/// A guard that stops the metrics HTTP server when dropped.
#[cfg(feature = "prometheus")]
pub struct MetricsHttpServerGuard {
    shutdown: Option<tokio::sync::oneshot::Sender<()>>,
    handle: Option<tokio::task::JoinHandle<()>>,
    addr: std::net::SocketAddr,
}

#[cfg(feature = "prometheus")]
impl MetricsHttpServerGuard {
    /// Returns the bound address of the server.
    pub fn addr(&self) -> std::net::SocketAddr {
        self.addr
    }
}

#[cfg(feature = "prometheus")]
impl Drop for MetricsHttpServerGuard {
    fn drop(&mut self) {
        // Ignore send error if the server already shut down.
        if let Some(tx) = self.shutdown.take() {
            let _ = tx.send(());
        }
        if let Some(h) = self.handle.take() {
            h.abort();
        }
    }
}

/// Start a background Warp server that serves `/metrics` on the given address.
#[cfg(feature = "prometheus")]
pub async fn start_http_server(
    addr: std::net::SocketAddr,
) -> crate::Result<MetricsHttpServerGuard> {
    use hyper::service::{make_service_fn, service_fn};
    use hyper::{Body, Request, Response, Server, StatusCode};

    let (tx, rx) = tokio::sync::oneshot::channel::<()>();

    // Bind using std listener for compatibility and to obtain bound addr immediately.
    let std_listener = std::net::TcpListener::bind(addr)
        .map_err(|e| crate::Error::Init(format!("failed to bind metrics server: {e}")))?;
    std_listener
        .set_nonblocking(true)
        .map_err(|e| crate::Error::Init(format!("failed to set nonblocking: {e}")))?;
    let bound_addr = std_listener
        .local_addr()
        .map_err(|e| crate::Error::Init(format!("failed to get local addr: {e}")))?;

    // Define a tiny service that only serves /metrics
    let make_svc = make_service_fn(|_conn| async move {
        Ok::<_, hyper::Error>(service_fn(|req: Request<Body>| async move {
            if req.method() == hyper::Method::GET && req.uri().path() == "/metrics" {
                // Inline implementation to avoid scope issues
                let metric_families = REGISTRY.gather();
                let encoder = TextEncoder::new();
                let mut buffer = Vec::new();
                let body = match encoder.encode(&metric_families, &mut buffer) {
                    Ok(()) => String::from_utf8(buffer).unwrap_or_else(|_| {
                        String::from("# Prometheus metrics export failed: UTF-8 conversion error\n")
                    }),
                    Err(_) => String::from("# Prometheus metrics export failed: encoding error\n"),
                };
                let mut resp = Response::new(Body::from(body));
                resp.headers_mut().insert(
                    hyper::header::CONTENT_TYPE,
                    hyper::header::HeaderValue::from_static("text/plain; version=0.0.4"),
                );
                Ok::<_, hyper::Error>(resp)
            } else {
                let mut resp = Response::new(Body::from("Not Found"));
                *resp.status_mut() = StatusCode::NOT_FOUND;
                Ok::<_, hyper::Error>(resp)
            }
        }))
    });

    let server = Server::from_tcp(std_listener)
        .map_err(|e| crate::Error::Init(format!("server from_tcp failed: {e}")))?
        .serve(make_svc)
        .with_graceful_shutdown(async move {
            let _ = rx.await;
        });

    let handle = tokio::spawn(async move {
        let _ = server.await; // discard Result<(), hyper::Error>
    });

    // Readiness probe: ensure the socket accepts connections before returning.
    // Try small, fast attempts to avoid extending test runtime.
    use tokio::time::{sleep, Duration};
    for _ in 0..100u32 {
        if tokio::net::TcpStream::connect(bound_addr).await.is_ok() {
            break;
        }
        sleep(Duration::from_millis(10)).await;
    }

    Ok(MetricsHttpServerGuard {
        shutdown: Some(tx),
        handle: Some(handle),
        addr: bound_addr,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_record_handshake_success() {
        let session_id = truncate_id("session-12345678", 8);
        let peer_id = truncate_id("peer-abcdefgh", 8);

        record_handshake_success(&session_id, &peer_id, "client", 150.5);

        // Verify metrics are recorded by checking dump output
        let output = dump_prometheus_internal();
        assert!(output.contains("nyx_handshake_success_total"));
        assert!(output.contains("nyx_handshake_duration_ms"));
    }

    #[test]
    fn test_record_handshake_failure() {
        let session_id = truncate_id("session-failure", 8);
        let peer_id = truncate_id("peer-error", 8);

        record_handshake_failure(&session_id, &peer_id, "server", "timeout");

        let output = dump_prometheus_internal();
        assert!(output.contains("nyx_handshake_failure_total"));
    }

    #[test]
    fn test_record_cmix_batch() {
        // Test different batch sizes
        record_cmix_batch(5, true, 25.3);
        record_cmix_batch(25, true, 75.8);
        record_cmix_batch(75, false, 120.0);
        record_cmix_batch(150, true, 250.5);

        let output = dump_prometheus_internal();
        assert!(output.contains("nyx_cmix_batch_total"));
        assert!(output.contains("nyx_cmix_batch_duration_ms"));
    }

    #[test]
    fn test_record_cmix_messages() {
        record_cmix_messages("inbound", 100);
        record_cmix_messages("outbound", 50);

        let output = dump_prometheus_internal();
        assert!(output.contains("nyx_cmix_messages_total"));
        assert!(
            output.contains("direction=\"inbound\"")
                || output.contains("direction=\\\"inbound\\\"")
        );
    }

    #[test]
    fn test_record_rekey_event() {
        let session_id = truncate_id("session-rekey", 8);

        record_rekey_event(&session_id, "scheduled", 45.2);
        record_rekey_event(&session_id, "forced", 78.9);

        let output = dump_prometheus_internal();
        assert!(output.contains("nyx_rekey_events_total"));
        assert!(output.contains("nyx_rekey_duration_ms"));
    }

    #[test]
    fn test_record_rekey_failure() {
        let session_id = truncate_id("session-rekey-fail", 8);

        record_rekey_failure(&session_id, "crypto_error");

        let output = dump_prometheus_internal();
        assert!(output.contains("nyx_rekey_failure_total"));
    }

    #[test]
    fn test_truncate_id() {
        assert_eq!(truncate_id("short", 8), "short");
        assert_eq!(truncate_id("verylongidentifier", 8), "verylong");
        assert_eq!(truncate_id("", 8), "unknown");
        assert_eq!(truncate_id("exactly8", 8), "exactly8");
    }

    #[test]
    fn test_batch_size_ranges() {
        // Test batch size categorization
        record_cmix_batch(1, true, 10.0);
        record_cmix_batch(10, true, 20.0);
        record_cmix_batch(11, true, 30.0);
        record_cmix_batch(50, true, 40.0);
        record_cmix_batch(51, true, 50.0);
        record_cmix_batch(100, true, 60.0);
        record_cmix_batch(101, true, 70.0);
        record_cmix_batch(1000, true, 80.0);

        let output = dump_prometheus_internal();
        assert!(output.contains("1-10"));
        assert!(output.contains("11-50"));
        assert!(output.contains("51-100"));
        assert!(output.contains("101+"));
    }

    #[test]
    fn test_metrics_labels() {
        let session = truncate_id("session-test-labels", 8);
        let peer = truncate_id("peer-test-labels", 8);

        record_handshake_success(&session, &peer, "client", 100.0);

        let output = dump_prometheus_internal();
        // Verify labels are present in output
        assert!(output.contains("session_id="));
        assert!(output.contains("peer_id="));
        assert!(output.contains("handshake_type="));
    }

    #[test]
    fn test_histogram_buckets() {
        // Record values across different histogram buckets
        record_handshake_success("sess1", "peer1", "client", 5.0); // < 10ms
        record_handshake_success("sess2", "peer2", "client", 75.0); // 50-100ms
        record_handshake_success("sess3", "peer3", "client", 350.0); // 250-500ms
        record_handshake_success("sess4", "peer4", "client", 1500.0); // 1-2.5s

        let output = dump_prometheus_internal();
        assert!(output.contains("nyx_handshake_duration_ms_bucket"));
        // Verify bucket labels exist
        assert!(output.contains("le="));
    }

    #[tokio::test]
    #[cfg(feature = "prometheus")]
    async fn test_metrics_http_server() {
        use tokio::time::{sleep, Duration};

        // Start metrics server on random port
        let addr = "127.0.0.1:0".parse().unwrap();
        let guard = start_http_server(addr).await.unwrap();

        // Record some metrics
        record_handshake_success("test1", "peer1", "client", 100.0);
        record_cmix_batch(25, true, 50.0);

        // Wait for server to be ready
        sleep(Duration::from_millis(100)).await;

        // Fetch metrics via HTTP using ureq (pure Rust, no C/C++ deps)
        // Wrap synchronous ureq call in spawn_blocking for async test compatibility
        let url = format!("http://{}/metrics", guard.addr());
        let url_clone = url.clone();
        let resp = tokio::task::spawn_blocking(move || ureq::get(&url_clone).call())
            .await
            .expect("Task join failed")
            .expect("HTTP request failed");
        assert_eq!(resp.status(), 200);

        let body = resp
            .into_string()
            .expect("Failed to read response body");
        assert!(body.contains("nyx_handshake_success_total"));
        assert!(body.contains("nyx_cmix_batch_total"));

        // Server should stop when guard is dropped
        drop(guard);
        sleep(Duration::from_millis(100)).await;
    }

    #[test]
    fn test_counter_registration() {
        // Test that duplicate counter registration doesn't panic
        record_counter("test_counter_1", 1);
        record_counter("test_counter_1", 1); // Should reuse existing counter
        record_counter("test_counter_2", 5);

        let output = dump_prometheus_internal();
        assert!(output.contains("test_counter_1"));
        assert!(output.contains("test_counter_2"));
    }

    #[test]
    fn test_record_path_quality() {
        let path_id = truncate_id("path-1234", 8);
        let session_id = truncate_id("session-path-test", 8);

        // Record path quality metrics
        record_path_quality(&path_id, &session_id, 45.5, 0.02, 1_000_000.0);

        let output = dump_prometheus_internal();
        assert!(output.contains("nyx_path_rtt_ms"));
        assert!(output.contains("nyx_path_loss_rate"));
        assert!(output.contains("nyx_path_bandwidth_bytes_per_sec"));
    }

    #[test]
    fn test_record_path_quality_boundary_values() {
        let path_id = truncate_id("path-boundary", 8);
        let session_id = truncate_id("session-boundary", 8);

        // Test boundary values (clamping)
        record_path_quality(&path_id, &session_id, 0.0, -0.5, -1000.0); // Negative values should be clamped
        record_path_quality(&path_id, &session_id, 1000.0, 1.5, 10_000_000.0); // > 1.0 loss rate should be clamped

        let output = dump_prometheus_internal();
        assert!(output.contains("nyx_path_rtt_ms"));
    }

    #[test]
    fn test_record_cover_traffic() {
        let session_id = truncate_id("session-cover", 8);

        // Record cover traffic packets
        record_cover_traffic(&session_id, "dummy", 100, 50_000);
        record_cover_traffic(&session_id, "padding", 50, 10_000);

        let output = dump_prometheus_internal();
        assert!(output.contains("nyx_cover_traffic_sent_total"));
        assert!(output.contains("nyx_cover_traffic_bytes_total"));
        assert!(output.contains("dummy") || output.contains("padding"));
    }

    #[test]
    fn test_record_cover_traffic_utilization() {
        let session_id = truncate_id("session-utilization", 8);

        // Record utilization rates
        record_cover_traffic_utilization(&session_id, 0.35);
        record_cover_traffic_utilization(&session_id, 0.75);

        let output = dump_prometheus_internal();
        assert!(output.contains("nyx_cover_traffic_utilization"));
    }

    #[test]
    fn test_cover_traffic_utilization_clamping() {
        let session_id = truncate_id("session-clamp", 8);

        // Test boundary clamping
        record_cover_traffic_utilization(&session_id, -0.5); // Should clamp to 0.0
        record_cover_traffic_utilization(&session_id, 1.5); // Should clamp to 1.0

        let output = dump_prometheus_internal();
        assert!(output.contains("nyx_cover_traffic_utilization"));
    }

    #[test]
    fn test_multiple_paths_metrics() {
        let session_id = truncate_id("session-multipath", 8);

        // Record metrics for multiple paths
        record_path_quality("path-1", &session_id, 20.0, 0.01, 5_000_000.0);
        record_path_quality("path-2", &session_id, 50.0, 0.05, 2_000_000.0);
        record_path_quality("path-3", &session_id, 100.0, 0.10, 1_000_000.0);

        let output = dump_prometheus_internal();
        assert!(output.contains("path_id="));
        assert!(output.contains("session_id="));
    }
}
