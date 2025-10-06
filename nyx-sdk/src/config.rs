#![forbid(unsafe_code)]

use crate::error::{Error, Result};
use serde::{Deserialize, Serialize};
use std::env;
use std::path::PathBuf;

/// Configuration profile for different environments
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ConfigProfile {
    /// Development profile with verbose logging
    Development,
    /// Production profile with optimized settings
    Production,
    /// Testing profile for integration tests
    Testing,
}

/// SDK configuration with comprehensive settings
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SdkConfig {
    /// Configuration profile
    #[serde(default)]
    pub profile: Option<ConfigProfile>,

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

    /// Connection pool size (0 = no pooling)
    #[serde(default)]
    pub pool_size: usize,

    /// Enable metrics collection
    #[serde(default)]
    pub enable_metrics: bool,

    /// Rate limit (requests per second, 0 = no limit)
    #[serde(default)]
    pub rate_limit: u32,
}

impl Default for SdkConfig {
    fn default() -> Self {
        Self {
            profile: None,
            daemon_endpoint: Self::default_endpoint(),
            request_timeout_ms: Self::default_timeout_ms(),
            max_request_size: Self::default_max_request_size(),
            max_response_size: Self::default_max_response_size(),
            auto_reconnect: Self::default_auto_reconnect(),
            max_reconnect_attempts: Self::default_max_reconnect_attempts(),
            reconnect_delay_ms: Self::default_reconnect_delay_ms(),
            enable_logging: false,
            pool_size: 0,
            enable_metrics: false,
            rate_limit: 0,
        }
    }
}

impl SdkConfig {
    /// Create a new builder for SDK configuration
    pub fn builder() -> SdkConfigBuilder {
        SdkConfigBuilder::new()
    }

    /// Create configuration from environment variables
    ///
    /// Supports the following environment variables:
    /// - NYX_PROFILE: Configuration profile (development/production/testing)
    /// - NYX_DAEMON_ENDPOINT: Daemon endpoint path
    /// - NYX_TIMEOUT_MS: Request timeout in milliseconds
    /// - NYX_MAX_REQUEST_SIZE: Maximum request size in bytes
    /// - NYX_MAX_RESPONSE_SIZE: Maximum response size in bytes
    /// - NYX_AUTO_RECONNECT: Enable auto reconnection (true/false)
    /// - NYX_MAX_RECONNECT_ATTEMPTS: Maximum reconnection attempts
    /// - NYX_RECONNECT_DELAY_MS: Reconnection delay in milliseconds
    /// - NYX_ENABLE_LOGGING: Enable logging (true/false)
    /// - NYX_POOL_SIZE: Connection pool size
    /// - NYX_ENABLE_METRICS: Enable metrics collection (true/false)
    /// - NYX_RATE_LIMIT: Rate limit in requests per second
    pub fn from_env() -> Result<Self> {
        let mut config = Self::default();

        // Load profile first
        if let Ok(profile) = env::var("NYX_PROFILE") {
            config.profile = Some(match profile.to_lowercase().as_str() {
                "development" | "dev" => ConfigProfile::Development,
                "production" | "prod" => ConfigProfile::Production,
                "testing" | "test" => ConfigProfile::Testing,
                _ => return Err(Error::config(format!("Invalid profile: {}", profile))),
            });

            // Apply profile defaults
            config = config.apply_profile();
        }

        // Override with environment variables
        if let Ok(endpoint) = env::var("NYX_DAEMON_ENDPOINT") {
            config.daemon_endpoint = endpoint;
        }

        if let Ok(timeout) = env::var("NYX_TIMEOUT_MS") {
            config.request_timeout_ms = timeout
                .parse()
                .map_err(|_| Error::config("Invalid NYX_TIMEOUT_MS value"))?;
        }

        if let Ok(size) = env::var("NYX_MAX_REQUEST_SIZE") {
            config.max_request_size = size
                .parse()
                .map_err(|_| Error::config("Invalid NYX_MAX_REQUEST_SIZE value"))?;
        }

        if let Ok(size) = env::var("NYX_MAX_RESPONSE_SIZE") {
            config.max_response_size = size
                .parse()
                .map_err(|_| Error::config("Invalid NYX_MAX_RESPONSE_SIZE value"))?;
        }

        if let Ok(reconnect) = env::var("NYX_AUTO_RECONNECT") {
            config.auto_reconnect = reconnect.to_lowercase() == "true";
        }

        if let Ok(attempts) = env::var("NYX_MAX_RECONNECT_ATTEMPTS") {
            config.max_reconnect_attempts = attempts
                .parse()
                .map_err(|_| Error::config("Invalid NYX_MAX_RECONNECT_ATTEMPTS value"))?;
        }

        if let Ok(delay) = env::var("NYX_RECONNECT_DELAY_MS") {
            config.reconnect_delay_ms = delay
                .parse()
                .map_err(|_| Error::config("Invalid NYX_RECONNECT_DELAY_MS value"))?;
        }

        if let Ok(logging) = env::var("NYX_ENABLE_LOGGING") {
            config.enable_logging = logging.to_lowercase() == "true";
        }

        if let Ok(pool_size) = env::var("NYX_POOL_SIZE") {
            config.pool_size = pool_size
                .parse()
                .map_err(|_| Error::config("Invalid NYX_POOL_SIZE value"))?;
        }

        if let Ok(metrics) = env::var("NYX_ENABLE_METRICS") {
            config.enable_metrics = metrics.to_lowercase() == "true";
        }

        if let Ok(rate_limit) = env::var("NYX_RATE_LIMIT") {
            config.rate_limit = rate_limit
                .parse()
                .map_err(|_| Error::config("Invalid NYX_RATE_LIMIT value"))?;
        }

        config.validate()?;
        Ok(config)
    }

    /// Apply profile-specific defaults
    pub fn apply_profile(mut self) -> Self {
        match self.profile {
            Some(ConfigProfile::Development) => {
                self.enable_logging = true;
                self.enable_metrics = true;
                self.request_timeout_ms = 30000; // 30 seconds for debugging
                self.pool_size = 1; // Minimal pooling for development
            }
            Some(ConfigProfile::Production) => {
                self.enable_logging = false; // Structured logging should be used instead
                self.enable_metrics = true;
                self.request_timeout_ms = 10000;
                self.pool_size = 10; // Aggressive pooling for production
                self.rate_limit = 100; // Rate limiting in production
            }
            Some(ConfigProfile::Testing) => {
                self.enable_logging = true;
                self.enable_metrics = false; // Reduce overhead in tests
                self.request_timeout_ms = 5000;
                self.pool_size = 2;
                self.auto_reconnect = false; // Fail fast in tests
            }
            None => {}
        }
        self
    }

    /// Load configuration with profile support
    ///
    /// File naming convention:
    /// - `config.toml` - Base configuration
    /// - `config.development.toml` - Development overrides
    /// - `config.production.toml` - Production overrides
    /// - `config.testing.toml` - Testing overrides
    pub async fn from_file_with_profile(
        base_path: impl Into<PathBuf>,
        profile: Option<ConfigProfile>,
    ) -> Result<Self> {
        let base_path = base_path.into();

        // Load base configuration
        let mut config = if base_path.exists() {
            Self::from_file(&base_path).await?
        } else {
            Self::default()
        };

        // Set profile
        config.profile = profile;

        // Load profile-specific configuration if it exists
        if let Some(profile) = profile {
            let profile_name = match profile {
                ConfigProfile::Development => "development",
                ConfigProfile::Production => "production",
                ConfigProfile::Testing => "testing",
            };

            let profile_path = base_path
                .parent()
                .unwrap_or(base_path.as_ref())
                .join(format!("config.{}.toml", profile_name));

            if profile_path.exists() {
                let profile_config = Self::from_file(&profile_path).await?;
                config = config.merge(profile_config);
            }

            // Apply profile defaults for unset values
            config = config.apply_profile();
        }

        config.validate()?;
        Ok(config)
    }

    /// Merge another configuration into this one (other takes precedence)
    fn merge(mut self, other: Self) -> Self {
        // Only override if the other value is explicitly set (non-default)
        if other.profile.is_some() {
            self.profile = other.profile;
        }
        if other.daemon_endpoint != Self::default_endpoint() {
            self.daemon_endpoint = other.daemon_endpoint;
        }
        if other.request_timeout_ms != Self::default_timeout_ms() {
            self.request_timeout_ms = other.request_timeout_ms;
        }
        if other.max_request_size != Self::default_max_request_size() {
            self.max_request_size = other.max_request_size;
        }
        if other.max_response_size != Self::default_max_response_size() {
            self.max_response_size = other.max_response_size;
        }
        // Simplified boolean comparison without double negation
        if other.auto_reconnect != Self::default_auto_reconnect() {
            self.auto_reconnect = other.auto_reconnect;
        }
        if other.max_reconnect_attempts != Self::default_max_reconnect_attempts() {
            self.max_reconnect_attempts = other.max_reconnect_attempts;
        }
        if other.reconnect_delay_ms != Self::default_reconnect_delay_ms() {
            self.reconnect_delay_ms = other.reconnect_delay_ms;
        }
        if other.enable_logging {
            self.enable_logging = other.enable_logging;
        }
        if other.pool_size > 0 {
            self.pool_size = other.pool_size;
        }
        if other.enable_metrics {
            self.enable_metrics = other.enable_metrics;
        }
        if other.rate_limit > 0 {
            self.rate_limit = other.rate_limit;
        }
        self
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
            return Err(Error::config("max_response_size must be greater than 0"));
        }

        if self.reconnect_delay_ms == 0 {
            return Err(Error::config("reconnect_delay_ms must be greater than 0"));
        }

        Ok(())
    }

    /// Load configuration from file
    pub async fn from_file(path: impl Into<PathBuf>) -> Result<Self> {
        let path = path.into();
        let contents = tokio::fs::read_to_string(&path)
            .await
            .map_err(|e| Error::config(format!("Failed to read config file {:?}: {}", path, e)))?;

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

        tokio::fs::write(&path, contents)
            .await
            .map_err(|e| Error::config(format!("Failed to write config file {:?}: {}", path, e)))?;

        Ok(())
    }
}

/// Builder for SDK configuration
#[derive(Debug, Default)]
pub struct SdkConfigBuilder {
    profile: Option<ConfigProfile>,
    daemon_endpoint: Option<String>,
    request_timeout_ms: Option<u64>,
    max_request_size: Option<usize>,
    max_response_size: Option<usize>,
    auto_reconnect: Option<bool>,
    max_reconnect_attempts: Option<u32>,
    reconnect_delay_ms: Option<u64>,
    enable_logging: Option<bool>,
    pool_size: Option<usize>,
    enable_metrics: Option<bool>,
    rate_limit: Option<u32>,
}

impl SdkConfigBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn profile(mut self, profile: ConfigProfile) -> Self {
        self.profile = Some(profile);
        self
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

    pub fn pool_size(mut self, size: usize) -> Self {
        self.pool_size = Some(size);
        self
    }

    pub fn enable_metrics(mut self, enabled: bool) -> Self {
        self.enable_metrics = Some(enabled);
        self
    }

    pub fn rate_limit(mut self, limit: u32) -> Self {
        self.rate_limit = Some(limit);
        self
    }

    pub fn build(self) -> Result<SdkConfig> {
        let mut config = SdkConfig {
            profile: self.profile,
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
            pool_size: self.pool_size.unwrap_or(0),
            enable_metrics: self.enable_metrics.unwrap_or(false),
            rate_limit: self.rate_limit.unwrap_or(0),
        };

        // Apply profile defaults if profile is set
        if config.profile.is_some() {
            config = config.apply_profile();
        }

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
        // Initialize config with empty daemon_endpoint directly to avoid field_reassign_with_default lint
        let mut config = SdkConfig {
            daemon_endpoint: String::new(),
            ..Default::default()
        };
        assert!(config.validate().is_err());

        config.daemon_endpoint = SdkConfig::default_endpoint();
        config.request_timeout_ms = 0;
        assert!(config.validate().is_err());
    }
}
