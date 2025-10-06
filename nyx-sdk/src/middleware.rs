//! Middleware and interceptor system for request/response processing.
//!
//! This module provides a flexible middleware system for:
//! - Request/response interception
//! - Retry policies with exponential backoff
//! - Rate limiting and throttling
//! - Request/response transformation
//! - Logging and metrics collection

use crate::error::{Error, Result};
use async_trait::async_trait;
use bytes::Bytes;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock};
use tokio::time::sleep;
use tracing::{debug, info, warn};

/// Request context passed through middleware chain
#[derive(Debug, Clone)]
pub struct RequestContext {
    /// Request identifier
    pub id: String,
    /// Request timestamp
    pub timestamp: Instant,
    /// Custom metadata
    pub metadata: std::collections::HashMap<String, String>,
    /// Attempt number (for retries)
    pub attempt: u32,
}

impl RequestContext {
    /// Create a new request context
    pub fn new() -> Self {
        Self {
            id: uuid::Uuid::new_v4().to_string(),
            timestamp: Instant::now(),
            metadata: std::collections::HashMap::new(),
            attempt: 0,
        }
    }

    /// Add metadata to the context
    pub fn with_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }
}

impl Default for RequestContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Response from a middleware or handler
#[derive(Debug)]
pub struct Response {
    /// Response data
    pub data: Bytes,
    /// Response timestamp
    pub timestamp: Instant,
    /// Custom metadata
    pub metadata: std::collections::HashMap<String, String>,
}

impl Response {
    /// Create a new response
    pub fn new(data: Bytes) -> Self {
        Self {
            data,
            timestamp: Instant::now(),
            metadata: std::collections::HashMap::new(),
        }
    }

    /// Add metadata to the response
    pub fn with_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }
}

/// Middleware trait for request/response processing
#[async_trait]
pub trait Middleware: Send + Sync {
    /// Process a request before it's sent
    async fn before_request(&self, ctx: &mut RequestContext, data: &mut Bytes) -> Result<()> {
        let _ = (ctx, data);
        Ok(())
    }

    /// Process a response after it's received
    async fn after_response(&self, ctx: &RequestContext, response: &mut Response) -> Result<()> {
        let _ = (ctx, response);
        Ok(())
    }

    /// Handle an error that occurred during request processing
    async fn on_error(&self, ctx: &RequestContext, error: &Error) -> Result<()> {
        let _ = (ctx, error);
        Ok(())
    }
}

/// Middleware chain that executes middleware in order
pub struct MiddlewareChain {
    middleware: Vec<Arc<dyn Middleware>>,
}

impl MiddlewareChain {
    /// Create a new middleware chain
    pub fn new() -> Self {
        Self {
            middleware: Vec::new(),
        }
    }

    /// Add middleware to the chain
    pub fn add<M: Middleware + 'static>(mut self, middleware: M) -> Self {
        self.middleware.push(Arc::new(middleware));
        self
    }

    /// Execute the before_request phase for all middleware
    pub async fn before_request(&self, ctx: &mut RequestContext, data: &mut Bytes) -> Result<()> {
        for mw in &self.middleware {
            mw.before_request(ctx, data).await?;
        }
        Ok(())
    }

    /// Execute the after_response phase for all middleware (in reverse order)
    pub async fn after_response(&self, ctx: &RequestContext, response: &mut Response) -> Result<()> {
        for mw in self.middleware.iter().rev() {
            mw.after_response(ctx, response).await?;
        }
        Ok(())
    }

    /// Execute the on_error phase for all middleware
    pub async fn on_error(&self, ctx: &RequestContext, error: &Error) -> Result<()> {
        for mw in &self.middleware {
            mw.on_error(ctx, error).await?;
        }
        Ok(())
    }
}

impl Default for MiddlewareChain {
    fn default() -> Self {
        Self::new()
    }
}

/// Retry policy configuration
#[derive(Debug, Clone)]
pub struct RetryPolicy {
    /// Maximum number of retry attempts
    pub max_attempts: u32,
    /// Initial delay before first retry
    pub initial_delay: Duration,
    /// Maximum delay between retries
    pub max_delay: Duration,
    /// Backoff multiplier (typically 2.0 for exponential backoff)
    pub backoff_multiplier: f64,
    /// Whether to retry on timeout errors
    pub retry_on_timeout: bool,
    /// Whether to retry on connection errors
    pub retry_on_connection: bool,
}

impl RetryPolicy {
    /// Create a new retry policy with default values
    pub fn new() -> Self {
        Self {
            max_attempts: 3,
            initial_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(10),
            backoff_multiplier: 2.0,
            retry_on_timeout: true,
            retry_on_connection: true,
        }
    }

    /// Calculate delay for the given attempt
    pub fn delay_for_attempt(&self, attempt: u32) -> Duration {
        let delay = self.initial_delay.as_secs_f64() 
            * self.backoff_multiplier.powi(attempt as i32);
        Duration::from_secs_f64(delay.min(self.max_delay.as_secs_f64()))
    }

    /// Check if the error should be retried
    pub fn should_retry(&self, error: &Error) -> bool {
        if !error.is_retryable() {
            return false;
        }

        match error {
            Error::Timeout { .. } => self.retry_on_timeout,
            Error::Disconnected { .. } | Error::ConnectionFailed { .. } => self.retry_on_connection,
            _ => error.is_retryable(),
        }
    }
}

impl Default for RetryPolicy {
    fn default() -> Self {
        Self::new()
    }
}

/// Retry middleware that automatically retries failed requests
pub struct RetryMiddleware {
    policy: RetryPolicy,
}

impl RetryMiddleware {
    /// Create a new retry middleware
    pub fn new(policy: RetryPolicy) -> Self {
        Self { policy }
    }

    /// Execute a request with retry logic
    pub async fn execute<F, Fut>(&self, mut ctx: RequestContext, f: F) -> Result<Response>
    where
        F: Fn(RequestContext) -> Fut,
        Fut: std::future::Future<Output = Result<Response>>,
    {
        let mut last_error = None;

        for attempt in 0..self.policy.max_attempts {
            ctx.attempt = attempt;

            match f(ctx.clone()).await {
                Ok(response) => {
                    if attempt > 0 {
                        info!("Request succeeded after {} retries", attempt);
                    }
                    return Ok(response);
                }
                Err(e) => {
                    if !self.policy.should_retry(&e) {
                        debug!("Error is not retryable: {}", e);
                        return Err(e);
                    }

                    if attempt + 1 < self.policy.max_attempts {
                        let delay = self.policy.delay_for_attempt(attempt);
                        warn!("Request failed (attempt {}), retrying after {:?}: {}", 
                              attempt + 1, delay, e);
                        sleep(delay).await;
                    }

                    last_error = Some(e);
                }
            }
        }

        Err(last_error.unwrap_or_else(|| 
            Error::request_failed("All retry attempts exhausted")))
    }
}

#[async_trait]
impl Middleware for RetryMiddleware {
    async fn on_error(&self, ctx: &RequestContext, error: &Error) -> Result<()> {
        if ctx.attempt > 0 {
            debug!("Retry attempt {} failed: {}", ctx.attempt, error);
        }
        Ok(())
    }
}

/// Rate limiter configuration
#[derive(Debug, Clone)]
pub struct RateLimiterConfig {
    /// Maximum number of requests per window
    pub max_requests: u32,
    /// Time window duration
    pub window: Duration,
    /// Whether to block or return error when rate limit is exceeded
    pub block_on_limit: bool,
}

impl RateLimiterConfig {
    /// Create a new rate limiter configuration
    pub fn new(max_requests: u32, window: Duration) -> Self {
        Self {
            max_requests,
            window,
            block_on_limit: true,
        }
    }
}

/// Token bucket rate limiter
pub struct RateLimiter {
    config: RateLimiterConfig,
    tokens: Arc<Mutex<f64>>,
    last_refill: Arc<Mutex<Instant>>,
}

impl RateLimiter {
    /// Create a new rate limiter
    pub fn new(config: RateLimiterConfig) -> Self {
        Self {
            tokens: Arc::new(Mutex::new(config.max_requests as f64)),
            last_refill: Arc::new(Mutex::new(Instant::now())),
            config,
        }
    }

    /// Try to acquire a token (returns true if successful)
    pub async fn try_acquire(&self) -> bool {
        self.refill_tokens().await;

        let mut tokens = self.tokens.lock().await;
        if *tokens >= 1.0 {
            *tokens -= 1.0;
            true
        } else {
            false
        }
    }

    /// Acquire a token, waiting if necessary
    pub async fn acquire(&self) -> Result<()> {
        loop {
            if self.try_acquire().await {
                return Ok(());
            }

            if !self.config.block_on_limit {
                return Err(Error::rate_limited("Rate limit exceeded"));
            }

            // Wait a bit before trying again
            sleep(Duration::from_millis(100)).await;
        }
    }

    /// Refill tokens based on elapsed time
    async fn refill_tokens(&self) {
        let now = Instant::now();
        let mut last_refill = self.last_refill.lock().await;
        let elapsed = now.duration_since(*last_refill);

        if elapsed >= Duration::from_millis(100) {
            let tokens_to_add = (elapsed.as_secs_f64() / self.config.window.as_secs_f64())
                * self.config.max_requests as f64;

            let mut tokens = self.tokens.lock().await;
            *tokens = (*tokens + tokens_to_add).min(self.config.max_requests as f64);
            *last_refill = now;
        }
    }

    /// Get current token count
    pub async fn available_tokens(&self) -> f64 {
        self.refill_tokens().await;
        *self.tokens.lock().await
    }
}

#[async_trait]
impl Middleware for RateLimiter {
    async fn before_request(&self, _ctx: &mut RequestContext, _data: &mut Bytes) -> Result<()> {
        self.acquire().await
    }
}

/// Logging middleware that logs requests and responses
pub struct LoggingMiddleware {
    log_request_body: bool,
    log_response_body: bool,
}

impl LoggingMiddleware {
    /// Create a new logging middleware
    pub fn new() -> Self {
        Self {
            log_request_body: false,
            log_response_body: false,
        }
    }

    /// Enable request body logging
    pub fn with_request_body(mut self) -> Self {
        self.log_request_body = true;
        self
    }

    /// Enable response body logging
    pub fn with_response_body(mut self) -> Self {
        self.log_response_body = true;
        self
    }
}

impl Default for LoggingMiddleware {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Middleware for LoggingMiddleware {
    async fn before_request(&self, ctx: &mut RequestContext, data: &mut Bytes) -> Result<()> {
        if self.log_request_body {
            debug!("Request {} (attempt {}): {} bytes", 
                   ctx.id, ctx.attempt, data.len());
        } else {
            debug!("Request {} (attempt {})", ctx.id, ctx.attempt);
        }
        Ok(())
    }

    async fn after_response(&self, ctx: &RequestContext, response: &mut Response) -> Result<()> {
        let duration = ctx.timestamp.elapsed();
        if self.log_response_body {
            info!("Response {} completed in {:?}: {} bytes", 
                  ctx.id, duration, response.data.len());
        } else {
            info!("Response {} completed in {:?}", ctx.id, duration);
        }
        Ok(())
    }

    async fn on_error(&self, ctx: &RequestContext, error: &Error) -> Result<()> {
        let duration = ctx.timestamp.elapsed();
        warn!("Request {} failed after {:?}: {}", ctx.id, duration, error);
        Ok(())
    }
}

/// Metrics collection middleware
pub struct MetricsMiddleware {
    requests_total: Arc<RwLock<u64>>,
    requests_success: Arc<RwLock<u64>>,
    requests_failed: Arc<RwLock<u64>>,
    total_duration: Arc<RwLock<Duration>>,
}

impl MetricsMiddleware {
    /// Create a new metrics middleware
    pub fn new() -> Self {
        Self {
            requests_total: Arc::new(RwLock::new(0)),
            requests_success: Arc::new(RwLock::new(0)),
            requests_failed: Arc::new(RwLock::new(0)),
            total_duration: Arc::new(RwLock::new(Duration::ZERO)),
        }
    }

    /// Get collected metrics
    pub async fn metrics(&self) -> Metrics {
        Metrics {
            requests_total: *self.requests_total.read().await,
            requests_success: *self.requests_success.read().await,
            requests_failed: *self.requests_failed.read().await,
            total_duration: *self.total_duration.read().await,
        }
    }
}

impl Default for MetricsMiddleware {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Middleware for MetricsMiddleware {
    async fn before_request(&self, _ctx: &mut RequestContext, _data: &mut Bytes) -> Result<()> {
        *self.requests_total.write().await += 1;
        Ok(())
    }

    async fn after_response(&self, ctx: &RequestContext, _response: &mut Response) -> Result<()> {
        *self.requests_success.write().await += 1;
        *self.total_duration.write().await += ctx.timestamp.elapsed();
        Ok(())
    }

    async fn on_error(&self, ctx: &RequestContext, _error: &Error) -> Result<()> {
        *self.requests_failed.write().await += 1;
        *self.total_duration.write().await += ctx.timestamp.elapsed();
        Ok(())
    }
}

/// Collected metrics
#[derive(Debug, Clone)]
pub struct Metrics {
    /// Total number of requests
    pub requests_total: u64,
    /// Number of successful requests
    pub requests_success: u64,
    /// Number of failed requests
    pub requests_failed: u64,
    /// Total duration of all requests
    pub total_duration: Duration,
}

impl Metrics {
    /// Calculate success rate
    pub fn success_rate(&self) -> f64 {
        if self.requests_total == 0 {
            0.0
        } else {
            self.requests_success as f64 / self.requests_total as f64
        }
    }

    /// Calculate average duration
    pub fn average_duration(&self) -> Duration {
        if self.requests_total == 0 {
            Duration::ZERO
        } else {
            self.total_duration / self.requests_total as u32
        }
    }
}
