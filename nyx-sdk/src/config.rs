#![forbid(unsafe_code)]

use crate::error::{Error, Result};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

/// SDK configuration with comprehensive settings
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SdkConfig {
    /// Daemon endpoint (Unix socket path or Windows named pipe)
    #[serde(default = "SdkConfig::default_endpoint")]
    pub daemon_endpoint: String,

    /// Request timeout in milliseconds
    #[serde(default = "SdkConfig::default_timeout_ms")]
    pub request_timeout_ms: u64,

    /// Maximum request size in bytes
    #[serde(default = "SdkConfig::default_max_request_size")]
    pub max_request_size: usize,

    /// Maximum response size in bytes
    #[serde(default = "SdkConfig::default_max_response_size")]
    pub max_response_size: usize,

    /// Enable automatic reconnection
    #[serde(default = "SdkConfig::default_auto_reconnect")]
    pub auto_reconnect: bool,

    /// Maximum reconnection attempts (0 = infinite)
    #[serde(default = "SdkConfig::default_max_reconnect_attempts")]
    pub max_reconnect_attempts: u32,

    /// Initial reconnection delay in milliseconds
    #[serde(default = "SdkConfig::default_reconnect_delay_ms")]
    pub reconnect_delay_ms: u64,

    /// Enable request/response logging
    #[serde(default)]
    pub enable_logging: bool,
}

impl Default for SdkConfig {
    fn default() -> Self {
        Self {
            daemon_endpoint: Self::default_endpoint(),
            request_timeout_ms: Self::default_timeout_ms(),
            max_request_size: Self::default_max_request_size(),
            max_response_size: Self::default_max_response_size(),
            auto_reconnect: Self::default_auto_reconnect(),
            max_reconnect_attempts: Self::default_max_reconnect_attempts(),
            reconnect_delay_ms: Self::default_reconnect_delay_ms(),
            enable_logging: false,
        }
    }
}

impl SdkConfig {
    /// Create a new builder for SDK configuration
    pub fn builder() -> SdkConfigBuilder {
        SdkConfigBuilder::new()
    }

    /// Get default daemon endpoint based on platform
    pub fn default_endpoint() -> String {
        if cfg!(windows) {
            "\\\\.\\pipe\\nyx-daemon".to_string()
        } else {
            "/tmp/nyx.sock".to_string()
        }
    }

    fn default_timeout_ms() -> u64 {
        10000
    }

    fn default_max_request_size() -> usize {
        1024 * 1024 // 1MB
    }

    fn default_max_response_size() -> usize {
        10 * 1024 * 1024 // 10MB
    }

    fn default_auto_reconnect() -> bool {
        true
    }

    fn default_max_reconnect_attempts() -> u32 {
        5
    }

    fn default_reconnect_delay_ms() -> u64 {
        1000
    }

    /// Validate configuration
    pub fn validate(&self) -> Result<()> {
        if self.daemon_endpoint.is_empty() {
            return Err(Error::config("daemon_endpoint cannot be empty"));
        }

        if self.request_timeout_ms == 0 {
            return Err(Error::config("request_timeout_ms must be greater than 0"));
        }

        if self.max_request_size == 0 {
            return Err(Error::config("max_request_size must be greater than 0"));
        }

        if self.max_response_size == 0 {
            return Err(Error::config(
                "max_response_size must be greater than 0",
            ));
        }

        if self.reconnect_delay_ms == 0 {
            return Err(Error::config("reconnect_delay_ms must be greater than 0"));
        }

        Ok(())
    }

    /// Load configuration from file
    pub async fn from_file(path: impl Into<PathBuf>) -> Result<Self> {
        let path = path.into();
        let contents = tokio::fs::read_to_string(&path).await.map_err(|e| {
            Error::config(format!("Failed to read config file {:?}: {}", path, e))
        })?;

        let config: Self = toml::from_str(&contents)
            .map_err(|e| Error::config(format!("Failed to parse config: {}", e)))?;

        config.validate()?;
        Ok(config)
    }

    /// Save configuration to file
    pub async fn save_to_file(&self, path: impl Into<PathBuf>) -> Result<()> {
        self.validate()?;

        let path = path.into();
        let contents = toml::to_string_pretty(self)
            .map_err(|e| Error::config(format!("Failed to serialize config: {}", e)))?;

        tokio::fs::write(&path, contents).await.map_err(|e| {
            Error::config(format!("Failed to write config file {:?}: {}", path, e))
        })?;

        Ok(())
    }
}

/// Builder for SDK configuration
#[derive(Debug, Default)]
pub struct SdkConfigBuilder {
    daemon_endpoint: Option<String>,
    request_timeout_ms: Option<u64>,
    max_request_size: Option<usize>,
    max_response_size: Option<usize>,
    auto_reconnect: Option<bool>,
    max_reconnect_attempts: Option<u32>,
    reconnect_delay_ms: Option<u64>,
    enable_logging: Option<bool>,
}

impl SdkConfigBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn daemon_endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.daemon_endpoint = Some(endpoint.into());
        self
    }

    pub fn request_timeout_ms(mut self, timeout: u64) -> Self {
        self.request_timeout_ms = Some(timeout);
        self
    }

    pub fn max_request_size(mut self, size: usize) -> Self {
        self.max_request_size = Some(size);
        self
    }

    pub fn max_response_size(mut self, size: usize) -> Self {
        self.max_response_size = Some(size);
        self
    }

    pub fn auto_reconnect(mut self, enabled: bool) -> Self {
        self.auto_reconnect = Some(enabled);
        self
    }

    pub fn max_reconnect_attempts(mut self, attempts: u32) -> Self {
        self.max_reconnect_attempts = Some(attempts);
        self
    }

    pub fn reconnect_delay_ms(mut self, delay: u64) -> Self {
        self.reconnect_delay_ms = Some(delay);
        self
    }

    pub fn enable_logging(mut self, enabled: bool) -> Self {
        self.enable_logging = Some(enabled);
        self
    }

    pub fn build(self) -> Result<SdkConfig> {
        let config = SdkConfig {
            daemon_endpoint: self
                .daemon_endpoint
                .unwrap_or_else(SdkConfig::default_endpoint),
            request_timeout_ms: self
                .request_timeout_ms
                .unwrap_or_else(SdkConfig::default_timeout_ms),
            max_request_size: self
                .max_request_size
                .unwrap_or_else(SdkConfig::default_max_request_size),
            max_response_size: self
                .max_response_size
                .unwrap_or_else(SdkConfig::default_max_response_size),
            auto_reconnect: self
                .auto_reconnect
                .unwrap_or_else(SdkConfig::default_auto_reconnect),
            max_reconnect_attempts: self
                .max_reconnect_attempts
                .unwrap_or_else(SdkConfig::default_max_reconnect_attempts),
            reconnect_delay_ms: self
                .reconnect_delay_ms
                .unwrap_or_else(SdkConfig::default_reconnect_delay_ms),
            enable_logging: self.enable_logging.unwrap_or(false),
        };

        config.validate()?;
        Ok(config)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = SdkConfig::default();
        assert!(!config.daemon_endpoint.is_empty());
        assert!(config.request_timeout_ms > 0);
        assert!(config.validate().is_ok());
    }

    #[test]
    fn test_builder() {
        let config = SdkConfig::builder()
            .request_timeout_ms(5000)
            .auto_reconnect(false)
            .enable_logging(true)
            .build()
            .unwrap();

        assert_eq!(config.request_timeout_ms, 5000);
        assert!(!config.auto_reconnect);
        assert!(config.enable_logging);
    }

    #[test]
    fn test_validation() {
        let mut config = SdkConfig::default();
        config.daemon_endpoint = String::new();
        assert!(config.validate().is_err());

        config.daemon_endpoint = SdkConfig::default_endpoint();
        config.request_timeout_ms = 0;
        assert!(config.validate().is_err());
    }
}
