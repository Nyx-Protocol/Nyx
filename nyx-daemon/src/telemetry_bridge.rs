//! Telemetry Bridge for OTLP/Prometheus Integration
//!
//! This module bridges nyx-stream telemetry (TelemetrySpan) to nyx-telemetry
//! OTLP exporter and Prometheus metrics. It maintains clean dependency graph:
//! nyx-daemon -> nyx-stream (telemetry generation)
//! nyx-daemon -> nyx-telemetry (export)
//!
//! Architecture:
//! ```text
//! nyx-stream::TelemetrySpan -> TelemetryBridge -> nyx-telemetry::OtlpExporter
//!                                              -> Prometheus metrics
//! ```

use anyhow::Result;
use nyx_stream::telemetry_schema::{SpanStatus, StreamTelemetryContext, TelemetrySpan};
use nyx_telemetry::otlp::{OtlpExporter, Span as OtlpSpan, SpanStatus as OtlpSpanStatus};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, SystemTime};
use tokio::sync::RwLock;
use tokio::time::interval;
use tracing::{debug, error, info, warn};

/// Configuration for telemetry bridge
#[derive(Debug, Clone)]
pub struct TelemetryBridgeConfig {
    /// Poll interval for collecting finished spans
    pub poll_interval: Duration,

    /// Enable OTLP export
    pub otlp_enabled: bool,

    /// Enable Prometheus metrics
    pub prometheus_enabled: bool,

    /// Service name for OTLP
    pub service_name: String,
}

impl Default for TelemetryBridgeConfig {
    fn default() -> Self {
        Self {
            poll_interval: Duration::from_secs(5),
            otlp_enabled: true,
            prometheus_enabled: true,
            service_name: "nyx-daemon".to_string(),
        }
    }
}

/// Telemetry bridge statistics
#[derive(Debug, Default, Clone)]
pub struct BridgeStats {
    /// Total spans collected
    pub spans_collected: u64,
    /// Total spans exported to OTLP
    pub spans_exported_otlp: u64,
    /// Total spans recorded to Prometheus
    pub spans_recorded_prometheus: u64,
    /// Total export errors
    pub export_errors: u64,
    /// Last poll time
    pub last_poll: Option<SystemTime>,
}

/// Telemetry bridge for integrating stream telemetry with OTLP/Prometheus
pub struct TelemetryBridge {
    config: TelemetryBridgeConfig,
    otlp_exporter: Option<Arc<RwLock<OtlpExporter>>>,
    stats: Arc<RwLock<BridgeStats>>,
    shutdown_tx: Option<tokio::sync::mpsc::Sender<()>>,
}

impl TelemetryBridge {
    /// Create new telemetry bridge
    pub async fn new(config: TelemetryBridgeConfig) -> Result<Self> {
        let otlp_exporter = if config.otlp_enabled {
            // Use environment variable or default OTLP endpoint
            let endpoint = std::env::var("OTEL_EXPORTER_OTLP_ENDPOINT")
                .unwrap_or_else(|_| "http://localhost:4317".to_string());

            let otlp_config = nyx_telemetry::otlp::OtlpConfig {
                endpoint,
                protocol: nyx_telemetry::otlp::OtlpProtocol::Grpc,
                timeout: Duration::from_secs(10),
                headers: HashMap::new(),
                max_batch_size: 512,
                batch_timeout: Duration::from_secs(5),
                max_retries: 3,
                retry_backoff: Duration::from_millis(100),
                compression: false,
                use_tls: false,
            };

            match OtlpExporter::new(otlp_config).await {
                Ok(exporter) => {
                    info!("OTLP exporter initialized successfully");
                    Some(Arc::new(RwLock::new(exporter)))
                }
                Err(e) => {
                    warn!(
                        "Failed to initialize OTLP exporter: {}. OTLP export disabled.",
                        e
                    );
                    None
                }
            }
        } else {
            None
        };

        Ok(Self {
            config,
            otlp_exporter,
            stats: Arc::new(RwLock::new(BridgeStats::default())),
            shutdown_tx: None,
        })
    }

    /// Start bridge polling task
    pub async fn start(&mut self, telemetry_ctx: Arc<StreamTelemetryContext>) -> Result<()> {
        let (shutdown_tx, mut shutdown_rx) = tokio::sync::mpsc::channel::<()>(1);
        self.shutdown_tx = Some(shutdown_tx);

        let config = self.config.clone();
        let otlp_exporter = self.otlp_exporter.clone();
        let stats = self.stats.clone();

        tokio::spawn(async move {
            let mut poll_timer = interval(config.poll_interval);
            poll_timer.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

            info!("Telemetry bridge polling started");

            loop {
                tokio::select! {
                    _ = poll_timer.tick() => {
                        if let Err(e) = Self::poll_and_export(
                            &telemetry_ctx,
                            &otlp_exporter,
                            &stats,
                            &config,
                        ).await {
                            error!("Error during telemetry poll: {}", e);
                        }
                    }

                    _ = shutdown_rx.recv() => {
                        info!("Telemetry bridge shutdown requested");
                        break;
                    }
                }
            }

            info!("Telemetry bridge polling stopped");
        });

        Ok(())
    }

    /// Poll telemetry context and export spans
    async fn poll_and_export(
        telemetry_ctx: &StreamTelemetryContext,
        otlp_exporter: &Option<Arc<RwLock<OtlpExporter>>>,
        stats: &Arc<RwLock<BridgeStats>>,
        config: &TelemetryBridgeConfig,
    ) -> Result<()> {
        // Collect finished spans from telemetry context
        let spans = telemetry_ctx.take_finished_spans().await;

        if spans.is_empty() {
            return Ok(());
        }

        debug!("Collected {} finished spans", spans.len());

        let mut stats_guard = stats.write().await;
        stats_guard.spans_collected += spans.len() as u64;
        stats_guard.last_poll = Some(SystemTime::now());

        // Export to OTLP
        if let Some(exporter) = otlp_exporter {
            for span in &spans {
                match Self::convert_to_otlp_span(span, &config.service_name) {
                    Ok(otlp_span) => {
                        let exporter_guard = exporter.write().await;
                        match exporter_guard.export_span(otlp_span).await {
                            Ok(_) => {
                                stats_guard.spans_exported_otlp += 1;
                            }
                            Err(e) => {
                                error!("Failed to export span to OTLP: {}", e);
                                stats_guard.export_errors += 1;
                            }
                        }
                    }
                    Err(e) => {
                        error!("Failed to convert span to OTLP format: {}", e);
                        stats_guard.export_errors += 1;
                    }
                }
            }
        }

        // Record to Prometheus
        if config.prometheus_enabled {
            Self::record_to_prometheus(&spans, &mut stats_guard);
        }

        Ok(())
    }

    /// Convert TelemetrySpan to OTLP Span
    fn convert_to_otlp_span(span: &TelemetrySpan, service_name: &str) -> Result<OtlpSpan> {
        let status = match span.status {
            SpanStatus::Ok => OtlpSpanStatus::Ok,
            SpanStatus::Error => OtlpSpanStatus::Error,
            SpanStatus::Unset => OtlpSpanStatus::Unset,
        };

        let mut attributes = span.attributes.clone();
        attributes.insert("service.name".to_string(), service_name.to_string());

        // Add trace/span IDs as attributes
        attributes.insert("trace.id".to_string(), span.trace_id.to_string());
        attributes.insert("span.id".to_string(), span.span_id.to_string());
        if let Some(parent_id) = span.parent_span_id {
            attributes.insert("parent.span.id".to_string(), parent_id.to_string());
        }

        Ok(OtlpSpan {
            trace_id: format!("{:016x}", span.trace_id),
            span_id: format!("{:016x}", span.span_id),
            parent_span_id: span.parent_span_id.map(|id| format!("{:016x}", id)),
            name: span.name.clone(),
            start_time: span.start_time,
            end_time: span.end_time,
            attributes,
            status,
            events: vec![],
        })
    }

    /// Record span metrics to Prometheus
    fn record_to_prometheus(spans: &[TelemetrySpan], stats: &mut BridgeStats) {
        for span in spans {
            // Record span count by operation name
            let metric_name = format!("nyx_span_count_{}", span.name.replace('-', "_"));
            nyx_telemetry::record_counter(&metric_name, 1);

            // Record span duration if available
            if let Some(end_time) = span.end_time {
                if let Ok(duration) = end_time.duration_since(span.start_time) {
                    let duration_ms = duration.as_millis() as u64;
                    let duration_metric =
                        format!("nyx_span_duration_ms_{}", span.name.replace('-', "_"));
                    nyx_telemetry::record_counter(&duration_metric, duration_ms);
                }
            }

            // Record error spans
            if span.status == SpanStatus::Error {
                let error_metric = format!("nyx_span_errors_{}", span.name.replace('-', "_"));
                nyx_telemetry::record_counter(&error_metric, 1);
            }

            stats.spans_recorded_prometheus += 1;
        }
    }

    /// Get bridge statistics
    pub async fn stats(&self) -> BridgeStats {
        self.stats.read().await.clone()
    }

    /// Shutdown bridge
    pub async fn shutdown(&mut self) -> Result<()> {
        if let Some(shutdown_tx) = self.shutdown_tx.take() {
            let _ = shutdown_tx.send(()).await;
        }

        // Shutdown OTLP exporter
        if let Some(exporter) = &self.otlp_exporter {
            let mut exporter_guard = exporter.write().await;
            exporter_guard.shutdown().await?;
        }

        info!("Telemetry bridge shutdown complete");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_span() -> TelemetrySpan {
        TelemetrySpan {
            span_id: 12345,
            parent_span_id: Some(67890),
            trace_id: 111213,
            name: "test-span".to_string(),
            start_time: SystemTime::now(),
            end_time: Some(SystemTime::now() + Duration::from_millis(100)),
            attributes: HashMap::from([
                ("key1".to_string(), "value1".to_string()),
                ("key2".to_string(), "value2".to_string()),
            ]),
            status: SpanStatus::Ok,
        }
    }

    #[test]
    fn test_convert_to_otlp_span() {
        let span = create_test_span();
        let otlp_span = TelemetryBridge::convert_to_otlp_span(&span, "test-service").unwrap();

        assert_eq!(otlp_span.name, "test-span");
        assert_eq!(otlp_span.status, OtlpSpanStatus::Ok);
        assert_eq!(otlp_span.trace_id, format!("{:016x}", 111213));
        assert_eq!(otlp_span.span_id, format!("{:016x}", 12345));
        assert_eq!(otlp_span.parent_span_id, Some(format!("{:016x}", 67890)));
        assert!(otlp_span.attributes.contains_key("service.name"));
        assert_eq!(
            otlp_span.attributes.get("service.name").unwrap(),
            "test-service"
        );
    }

    #[test]
    fn test_convert_span_status() {
        let mut span = create_test_span();

        // Test Ok status
        span.status = SpanStatus::Ok;
        let otlp_span = TelemetryBridge::convert_to_otlp_span(&span, "test").unwrap();
        assert_eq!(otlp_span.status, OtlpSpanStatus::Ok);

        // Test Error status
        span.status = SpanStatus::Error;
        let otlp_span = TelemetryBridge::convert_to_otlp_span(&span, "test").unwrap();
        assert_eq!(otlp_span.status, OtlpSpanStatus::Error);

        // Test Unset status
        span.status = SpanStatus::Unset;
        let otlp_span = TelemetryBridge::convert_to_otlp_span(&span, "test").unwrap();
        assert_eq!(otlp_span.status, OtlpSpanStatus::Unset);
    }

    #[test]
    fn test_convert_span_without_parent() {
        let mut span = create_test_span();
        span.parent_span_id = None;

        let otlp_span = TelemetryBridge::convert_to_otlp_span(&span, "test").unwrap();
        assert_eq!(otlp_span.parent_span_id, None);
    }

    #[tokio::test]
    async fn test_bridge_creation() {
        let config = TelemetryBridgeConfig {
            otlp_enabled: false, // Disable OTLP to avoid network calls in test
            prometheus_enabled: false,
            ..Default::default()
        };

        let bridge = TelemetryBridge::new(config).await;
        assert!(bridge.is_ok());
    }

    #[tokio::test]
    async fn test_bridge_stats() {
        let config = TelemetryBridgeConfig {
            otlp_enabled: false,
            prometheus_enabled: false,
            ..Default::default()
        };

        let bridge = TelemetryBridge::new(config).await.unwrap();
        let stats = bridge.stats().await;

        assert_eq!(stats.spans_collected, 0);
        assert_eq!(stats.spans_exported_otlp, 0);
        assert_eq!(stats.export_errors, 0);
    }

    #[tokio::test]
    async fn test_record_to_prometheus() {
        let span = create_test_span();
        let mut stats = BridgeStats::default();

        TelemetryBridge::record_to_prometheus(&[span], &mut stats);

        assert_eq!(stats.spans_recorded_prometheus, 1);
    }

    #[tokio::test]
    async fn test_bridge_shutdown() {
        let config = TelemetryBridgeConfig {
            otlp_enabled: false,
            prometheus_enabled: false,
            ..Default::default()
        };

        let mut bridge = TelemetryBridge::new(config).await.unwrap();
        let result = bridge.shutdown().await;
        assert!(result.is_ok());
    }
}
