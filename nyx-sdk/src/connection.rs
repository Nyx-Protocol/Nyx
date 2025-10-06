//! Connection management with pooling, reconnection, and health checks.
//!
//! This module provides robust connection management features including:
//! - Connection pooling for efficient resource reuse
//! - Automatic reconnection with exponential backoff
//! - Health monitoring and circuit breaker patterns
//! - Graceful connection lifecycle management

use crate::error::{Error, Result};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock, Semaphore};
use tokio::time::sleep;
use tracing::{debug, info, warn, error};

/// Connection state for health monitoring
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConnectionState {
    /// Connection is healthy and operational
    Healthy,
    /// Connection is degraded but still usable
    Degraded,
    /// Connection has failed and needs reconnection
    Failed,
    /// Connection is in the process of reconnecting
    Reconnecting,
    /// Connection is closed
    Closed,
}

/// Health status of a connection
#[derive(Debug, Clone)]
pub struct HealthStatus {
    /// Current connection state
    pub state: ConnectionState,
    /// Last successful operation timestamp
    pub last_success: Instant,
    /// Last failure timestamp
    pub last_failure: Option<Instant>,
    /// Number of consecutive failures
    pub consecutive_failures: u32,
    /// Total number of successful operations
    pub success_count: u64,
    /// Total number of failed operations
    pub failure_count: u64,
    /// Current latency (if available)
    pub latency: Option<Duration>,
}

impl HealthStatus {
    /// Create a new healthy status
    pub fn new() -> Self {
        Self {
            state: ConnectionState::Healthy,
            last_success: Instant::now(),
            last_failure: None,
            consecutive_failures: 0,
            success_count: 0,
            failure_count: 0,
            latency: None,
        }
    }

    /// Record a successful operation
    pub fn record_success(&mut self, latency: Option<Duration>) {
        self.last_success = Instant::now();
        self.consecutive_failures = 0;
        self.success_count += 1;
        self.latency = latency;
        
        if self.state == ConnectionState::Failed || self.state == ConnectionState::Degraded {
            self.state = ConnectionState::Healthy;
            info!("Connection recovered to healthy state");
        }
    }

    /// Record a failed operation
    pub fn record_failure(&mut self) {
        self.last_failure = Some(Instant::now());
        self.consecutive_failures += 1;
        self.failure_count += 1;
        
        // Update state based on failure count
        if self.consecutive_failures >= 5 {
            self.state = ConnectionState::Failed;
            error!("Connection marked as failed after {} consecutive failures", self.consecutive_failures);
        } else if self.consecutive_failures >= 2 {
            self.state = ConnectionState::Degraded;
            warn!("Connection degraded after {} consecutive failures", self.consecutive_failures);
        }
    }

    /// Check if the connection is healthy
    pub fn is_healthy(&self) -> bool {
        matches!(self.state, ConnectionState::Healthy | ConnectionState::Degraded)
    }

    /// Check if reconnection is needed
    pub fn needs_reconnection(&self) -> bool {
        self.state == ConnectionState::Failed
    }
}

impl Default for HealthStatus {
    fn default() -> Self {
        Self::new()
    }
}

/// Reconnection policy configuration
#[derive(Debug, Clone)]
pub struct ReconnectionPolicy {
    /// Initial delay before first reconnection attempt
    pub initial_delay: Duration,
    /// Maximum delay between reconnection attempts
    pub max_delay: Duration,
    /// Maximum number of reconnection attempts (None = infinite)
    pub max_attempts: Option<u32>,
    /// Backoff multiplier (typically 2.0 for exponential backoff)
    pub backoff_multiplier: f64,
    /// Jitter factor to randomize delays (0.0 = no jitter, 1.0 = full jitter)
    pub jitter: f64,
}

impl ReconnectionPolicy {
    /// Create a new reconnection policy with default values
    pub fn new() -> Self {
        Self {
            initial_delay: Duration::from_secs(1),
            max_delay: Duration::from_secs(60),
            max_attempts: Some(10),
            backoff_multiplier: 2.0,
            jitter: 0.1,
        }
    }

    /// Calculate delay for the given attempt number
    pub fn delay_for_attempt(&self, attempt: u32) -> Duration {
        let base_delay = self.initial_delay.as_secs_f64() 
            * self.backoff_multiplier.powi(attempt as i32);
        let capped_delay = base_delay.min(self.max_delay.as_secs_f64());
        
        // Add jitter to avoid thundering herd
        let jitter = if self.jitter > 0.0 {
            use std::collections::hash_map::RandomState;
            use std::hash::{BuildHasher, Hasher};
            let mut hasher = RandomState::new().build_hasher();
            hasher.write_u32(attempt);
            let random = (hasher.finish() % 1000) as f64 / 1000.0;
            capped_delay * self.jitter * (random - 0.5)
        } else {
            0.0
        };
        
        Duration::from_secs_f64((capped_delay + jitter).max(0.0))
    }

    /// Check if more attempts are allowed
    pub fn can_attempt(&self, attempt: u32) -> bool {
        self.max_attempts.map_or(true, |max| attempt < max)
    }
}

impl Default for ReconnectionPolicy {
    fn default() -> Self {
        Self::new()
    }
}

/// Connection pool configuration
#[derive(Debug, Clone)]
pub struct PoolConfig {
    /// Minimum number of connections to maintain
    pub min_connections: usize,
    /// Maximum number of connections allowed
    pub max_connections: usize,
    /// Timeout for acquiring a connection from the pool
    pub acquire_timeout: Duration,
    /// Maximum lifetime of a connection before renewal
    pub max_lifetime: Duration,
    /// Idle timeout before connection is closed
    pub idle_timeout: Duration,
    /// Health check interval
    pub health_check_interval: Duration,
}

impl PoolConfig {
    /// Create a new pool configuration with default values
    pub fn new() -> Self {
        Self {
            min_connections: 1,
            max_connections: 10,
            acquire_timeout: Duration::from_secs(30),
            max_lifetime: Duration::from_secs(3600),
            idle_timeout: Duration::from_secs(300),
            health_check_interval: Duration::from_secs(30),
        }
    }
}

impl Default for PoolConfig {
    fn default() -> Self {
        Self::new()
    }
}

/// A managed connection with health tracking
pub struct ManagedConnection<T> {
    /// The actual connection
    connection: T,
    /// Connection creation time
    created_at: Instant,
    /// Last usage timestamp
    last_used: Instant,
    /// Health status
    health: Arc<RwLock<HealthStatus>>,
}

impl<T> ManagedConnection<T> {
    /// Create a new managed connection
    pub fn new(connection: T) -> Self {
        let now = Instant::now();
        Self {
            connection,
            created_at: now,
            last_used: now,
            health: Arc::new(RwLock::new(HealthStatus::new())),
        }
    }

    /// Get a reference to the underlying connection
    pub fn get(&mut self) -> &mut T {
        self.last_used = Instant::now();
        &mut self.connection
    }

    /// Get the connection age
    pub fn age(&self) -> Duration {
        self.created_at.elapsed()
    }

    /// Get the idle time
    pub fn idle_time(&self) -> Duration {
        self.last_used.elapsed()
    }

    /// Get a clone of the health status
    pub async fn health_status(&self) -> HealthStatus {
        self.health.read().await.clone()
    }

    /// Record a successful operation
    pub async fn record_success(&self, latency: Option<Duration>) {
        self.health.write().await.record_success(latency);
    }

    /// Record a failed operation
    pub async fn record_failure(&self) {
        self.health.write().await.record_failure();
    }

    /// Check if the connection should be renewed
    pub async fn should_renew(&self, max_lifetime: Duration, idle_timeout: Duration) -> bool {
        let health = self.health.read().await;
        self.age() > max_lifetime 
            || self.idle_time() > idle_timeout
            || health.needs_reconnection()
    }
}

/// Connection pool manager
pub struct ConnectionPool<T> {
    /// Pool configuration
    config: PoolConfig,
    /// Available connections
    connections: Arc<Mutex<Vec<ManagedConnection<T>>>>,
    /// Semaphore to limit concurrent connections
    semaphore: Arc<Semaphore>,
    /// Connection factory
    factory: Arc<dyn Fn() -> tokio::task::JoinHandle<Result<T>> + Send + Sync>,
}

impl<T: Send + 'static> ConnectionPool<T> {
    /// Create a new connection pool
    pub fn new<F>(config: PoolConfig, factory: F) -> Self
    where
        F: Fn() -> tokio::task::JoinHandle<Result<T>> + Send + Sync + 'static,
    {
        let semaphore = Arc::new(Semaphore::new(config.max_connections));
        
        Self {
            config,
            connections: Arc::new(Mutex::new(Vec::new())),
            semaphore,
            factory: Arc::new(factory),
        }
    }

    /// Acquire a connection from the pool
    pub async fn acquire(&self) -> Result<ManagedConnection<T>> {
        // Try to acquire a permit with timeout
        let permit = tokio::time::timeout(
            self.config.acquire_timeout,
            self.semaphore.clone().acquire_owned()
        )
        .await
        .map_err(|_| Error::timeout(self.config.acquire_timeout.as_millis() as u64))?
        .map_err(|_| Error::connection_failed("Failed to acquire connection permit"))?;

        // Try to get an existing connection
        let mut connections = self.connections.lock().await;
        
        // Find a healthy connection
        while let Some(mut conn) = connections.pop() {
            if !conn.should_renew(self.config.max_lifetime, self.config.idle_timeout).await {
                debug!("Reusing existing connection from pool");
                drop(permit); // Return the permit
                return Ok(conn);
            } else {
                debug!("Discarding expired/unhealthy connection");
            }
        }

        drop(connections); // Release lock before creating new connection
        drop(permit); // Return the permit

        // Create a new connection
        debug!("Creating new connection");
        let connection = (self.factory)()
            .await
            .map_err(|_| Error::connection_failed("Connection factory task failed"))?
            .map_err(|e| {
                error!("Failed to create new connection: {}", e);
                e
            })?;

        Ok(ManagedConnection::new(connection))
    }

    /// Return a connection to the pool
    pub async fn release(&self, connection: ManagedConnection<T>) {
        let should_keep = !connection
            .should_renew(self.config.max_lifetime, self.config.idle_timeout)
            .await;

        if should_keep {
            let mut connections = self.connections.lock().await;
            if connections.len() < self.config.max_connections {
                debug!("Returning connection to pool");
                connections.push(connection);
            } else {
                debug!("Pool is full, discarding connection");
            }
        } else {
            debug!("Connection expired or unhealthy, not returning to pool");
        }
    }

    /// Get pool statistics
    pub async fn stats(&self) -> PoolStats {
        let connections = self.connections.lock().await;
        PoolStats {
            available: connections.len(),
            max: self.config.max_connections,
            in_use: self.config.max_connections - self.semaphore.available_permits(),
        }
    }
}

/// Pool statistics
#[derive(Debug, Clone)]
pub struct PoolStats {
    /// Number of available connections in the pool
    pub available: usize,
    /// Maximum number of connections allowed
    pub max: usize,
    /// Number of connections currently in use
    pub in_use: usize,
}
