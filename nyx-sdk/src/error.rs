#![forbid(unsafe_code)]

use std::fmt;
use thiserror::Error as ThisError;

pub type Result<T, E = Error> = std::result::Result<T, E>;

/// SDK error types with contextual information
#[derive(Debug, ThisError)]
pub enum Error {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("serialization error: {0}")]
    Serde(#[from] serde_json::Error),

    #[error("configuration error: {0}")]
    Config(String),

    #[error("protocol error: {0}")]
    Protocol(String),

    #[error("stream error: {0}")]
    Stream(String),

    #[error("timeout after {duration_ms}ms")]
    Timeout { duration_ms: u64 },

    #[error("disconnected: {reason}")]
    Disconnected { reason: String },

    #[error("not found: {0}")]
    NotFound(&'static str),

    #[error("authentication failed: {0}")]
    AuthenticationFailed(String),

    #[error("rate limited: {0}")]
    RateLimited(String),

    #[error("invalid state: {0}")]
    InvalidState(String),

    #[error("resource exhausted: {0}")]
    ResourceExhausted(String),

    /// Unsupported required capability error (CLOSE 0x07)
    ///
    /// Returned when the peer requires a capability that this endpoint does not support.
    /// The capability ID is included for debugging and error reporting.
    /// Reference: spec/Capability_Negotiation_Policy_EN.md §4.2
    #[error("unsupported required capability: 0x{0:08X}")]
    UnsupportedCapability(u32),

    /// Legacy gRPC error variant - kept for compatibility but gRPC is disabled
    /// in favor of pure Rust JSON-RPC communication to avoid C dependencies.
    #[cfg(feature = "grpc-backup")]
    #[error("grpc functionality is disabled (use JSON-RPC instead)")]
    GrpcDisabled,
}

impl Error {
    pub fn config(msg: impl Into<String>) -> Self {
        Self::Config(msg.into())
    }

    pub fn protocol(msg: impl Into<String>) -> Self {
        Self::Protocol(msg.into())
    }

    pub fn stream(msg: impl Into<String>) -> Self {
        Self::Stream(msg.into())
    }

    pub fn timeout(duration_ms: u64) -> Self {
        Self::Timeout { duration_ms }
    }

    pub fn disconnected(reason: impl Into<String>) -> Self {
        Self::Disconnected {
            reason: reason.into(),
        }
    }

    pub fn authentication_failed(msg: impl Into<String>) -> Self {
        Self::AuthenticationFailed(msg.into())
    }

    pub fn rate_limited(msg: impl Into<String>) -> Self {
        Self::RateLimited(msg.into())
    }

    pub fn invalid_state(msg: impl Into<String>) -> Self {
        Self::InvalidState(msg.into())
    }

    pub fn resource_exhausted(msg: impl Into<String>) -> Self {
        Self::ResourceExhausted(msg.into())
    }

    /// Check if error is retryable
    pub fn is_retryable(&self) -> bool {
        matches!(
            self,
            Error::Timeout { .. }
                | Error::Disconnected { .. }
                | Error::Io(_)
                | Error::RateLimited(_)
        )
    }

    /// Check if error is fatal (should not retry)
    pub fn is_fatal(&self) -> bool {
        matches!(
            self,
            Error::AuthenticationFailed(_)
                | Error::UnsupportedCapability(_)
                | Error::Config(_)
                | Error::InvalidState(_)
        )
    }

    /// Get error category for metrics/logging
    pub fn category(&self) -> ErrorCategory {
        match self {
            Error::Io(_) => ErrorCategory::Network,
            Error::Serde(_) => ErrorCategory::Serialization,
            Error::Config(_) => ErrorCategory::Configuration,
            Error::Protocol(_) => ErrorCategory::Protocol,
            Error::Stream(_) => ErrorCategory::Stream,
            Error::Timeout { .. } => ErrorCategory::Timeout,
            Error::Disconnected { .. } => ErrorCategory::Network,
            Error::NotFound(_) => ErrorCategory::NotFound,
            Error::AuthenticationFailed(_) => ErrorCategory::Authentication,
            Error::RateLimited(_) => ErrorCategory::RateLimit,
            Error::InvalidState(_) => ErrorCategory::State,
            Error::ResourceExhausted(_) => ErrorCategory::Resource,
            Error::UnsupportedCapability(_) => ErrorCategory::Capability,
            #[cfg(feature = "grpc-backup")]
            Error::GrpcDisabled => ErrorCategory::Configuration,
        }
    }
}

/// Error category for metrics and logging
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ErrorCategory {
    Network,
    Serialization,
    Configuration,
    Protocol,
    Stream,
    Timeout,
    NotFound,
    Authentication,
    RateLimit,
    State,
    Resource,
    Capability,
}

impl fmt::Display for ErrorCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorCategory::Network => write!(f, "network"),
            ErrorCategory::Serialization => write!(f, "serialization"),
            ErrorCategory::Configuration => write!(f, "configuration"),
            ErrorCategory::Protocol => write!(f, "protocol"),
            ErrorCategory::Stream => write!(f, "stream"),
            ErrorCategory::Timeout => write!(f, "timeout"),
            ErrorCategory::NotFound => write!(f, "not_found"),
            ErrorCategory::Authentication => write!(f, "authentication"),
            ErrorCategory::RateLimit => write!(f, "rate_limit"),
            ErrorCategory::State => write!(f, "state"),
            ErrorCategory::Resource => write!(f, "resource"),
            ErrorCategory::Capability => write!(f, "capability"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unsupported_capability_error_format() {
        // Test standard capability ID
        let err = Error::UnsupportedCapability(0x00000001);
        assert_eq!(
            err.to_string(),
            "unsupported required capability: 0x00000001"
        );

        // Test plugin framework capability ID
        let err = Error::UnsupportedCapability(0x00000002);
        assert_eq!(
            err.to_string(),
            "unsupported required capability: 0x00000002"
        );

        // Test arbitrary capability ID with hex formatting
        let err = Error::UnsupportedCapability(0x12345678);
        assert_eq!(
            err.to_string(),
            "unsupported required capability: 0x12345678"
        );

        // Test maximum capability ID
        let err = Error::UnsupportedCapability(0xFFFFFFFF);
        assert_eq!(
            err.to_string(),
            "unsupported required capability: 0xFFFFFFFF"
        );
    }

    #[test]
    fn test_error_variants() {
        // Verify all error variants compile and have proper Display impl
        let _errors = vec![
            Error::Config("test".into()),
            Error::Protocol("test".into()),
            Error::Stream("test".into()),
            Error::Timeout { duration_ms: 5000 },
            Error::Disconnected {
                reason: "test".into(),
            },
            Error::NotFound("test"),
            Error::UnsupportedCapability(0x1234),
            Error::AuthenticationFailed("test".into()),
            Error::RateLimited("test".into()),
            Error::InvalidState("test".into()),
            Error::ResourceExhausted("test".into()),
        ];
    }

    #[test]
    fn test_error_retryable() {
        assert!(Error::Timeout { duration_ms: 1000 }.is_retryable());
        assert!(Error::Disconnected {
            reason: "test".into()
        }
        .is_retryable());
        assert!(Error::RateLimited("test".into()).is_retryable());
        assert!(!Error::AuthenticationFailed("test".into()).is_retryable());
        assert!(!Error::Config("test".into()).is_retryable());
    }

    #[test]
    fn test_error_fatal() {
        assert!(Error::AuthenticationFailed("test".into()).is_fatal());
        assert!(Error::UnsupportedCapability(0x1234).is_fatal());
        assert!(Error::Config("test".into()).is_fatal());
        assert!(!Error::Timeout { duration_ms: 1000 }.is_fatal());
    }

    #[test]
    fn test_error_category() {
        assert_eq!(
            Error::Config("test".into()).category(),
            ErrorCategory::Configuration
        );
        assert_eq!(
            Error::Timeout { duration_ms: 1000 }.category(),
            ErrorCategory::Timeout
        );
        assert_eq!(
            Error::AuthenticationFailed("test".into()).category(),
            ErrorCategory::Authentication
        );
    }
}
