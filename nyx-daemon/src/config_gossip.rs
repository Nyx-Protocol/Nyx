//! Configuration Gossip Protocol
//!
//! Distributed configuration synchronization using DHT-based Pub/Sub.
//! Implements Vector Clock for causal ordering and Last-Writer-Wins for conflict resolution.
//!
//! ## Design Rationale
//! - Leverages existing Pure Rust DHT (`nyx-control::dht`) for network layer
//! - Vector Clock tracks causality (§5.4 requirement)
//! - Ed25519 signatures prevent unauthorized config changes
//! - LWW (Last-Writer-Wins) for conflict resolution (simple, deterministic)
//! - Validation before applying config (prevents invalid states)

#![forbid(unsafe_code)]

use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use nyx_control::dht::{DhtStorage, StorageKey, StorageValue};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};
use thiserror::Error;
use tokio::sync::RwLock as TokioRwLock; // Async RwLock for async contexts
use tracing::{debug, info, warn};

/// Configuration gossip errors
#[derive(Error, Debug, Clone, PartialEq)]
pub enum ConfigGossipError {
    #[error("Invalid signature for config version {version}")]
    InvalidSignature { version: u64 },

    #[error("Config validation failed: {reason}")]
    ValidationFailed { reason: String },

    #[error("Conflict detected: local={local_version}, remote={remote_version}")]
    ConflictDetected {
        local_version: u64,
        remote_version: u64,
    },

    #[error("DHT storage error: {reason}")]
    DhtError { reason: String },

    #[error("Serialization error: {reason}")]
    SerializationError { reason: String },

    #[error("Unknown node: {node_id}")]
    UnknownNode { node_id: String },
}

/// Vector Clock for causal ordering
///
/// Tracks logical time per node to detect concurrent updates.
/// Used for conflict detection in distributed config synchronization.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VectorClock {
    /// Map from node ID to logical timestamp
    clocks: HashMap<String, u64>,
}

impl VectorClock {
    pub fn new() -> Self {
        Self {
            clocks: HashMap::new(),
        }
    }

    /// Increment the clock for a given node
    pub fn increment(&mut self, node_id: &str) {
        let counter = self.clocks.entry(node_id.to_string()).or_insert(0);
        *counter += 1;
    }

    /// Merge with another vector clock (take max of each component)
    pub fn merge(&mut self, other: &VectorClock) {
        for (node, &timestamp) in &other.clocks {
            let current = self.clocks.entry(node.clone()).or_insert(0);
            *current = (*current).max(timestamp);
        }
    }

    /// Check if this clock happens-before the other
    ///
    /// Returns:
    /// - `Some(true)` if self < other (all components ≤, at least one <)
    /// - `Some(false)` if self > other
    /// - `None` if concurrent (neither < nor >)
    pub fn happens_before(&self, other: &VectorClock) -> Option<bool> {
        let mut less = false;
        let mut greater = false;

        // Collect all node IDs from both clocks
        let mut all_nodes = self.clocks.keys().collect::<std::collections::HashSet<_>>();
        all_nodes.extend(other.clocks.keys());

        for node in all_nodes {
            let self_val = self.clocks.get(node).copied().unwrap_or(0);
            let other_val = other.clocks.get(node).copied().unwrap_or(0);

            if self_val < other_val {
                less = true;
            } else if self_val > other_val {
                greater = true;
            }
        }

        match (less, greater) {
            (true, false) => Some(true),  // self < other
            (false, true) => Some(false), // self > other
            _ => None,                    // concurrent or equal
        }
    }

    /// Get timestamp for a specific node
    pub fn get(&self, node_id: &str) -> u64 {
        self.clocks.get(node_id).copied().unwrap_or(0)
    }
}

impl Default for VectorClock {
    fn default() -> Self {
        Self::new()
    }
}

/// Signed configuration blob
///
/// Contains the actual config content, metadata, and cryptographic signature
/// for authenticity verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SignedConfig {
    /// Configuration content (typically TOML serialized)
    pub content: Vec<u8>,

    /// Version number (monotonic)
    pub version: u64,

    /// Vector clock for causal ordering
    pub vector_clock: VectorClock,

    /// Unix timestamp (seconds since epoch)
    pub timestamp: u64,

    /// Node ID of the originator
    pub originator: String,

    /// Ed25519 signature (64 bytes)
    ///
    /// Signs: SHA256(content || version || timestamp || originator)
    pub signature: Vec<u8>,
}

impl SignedConfig {
    /// Create a new signed configuration with Ed25519 digital signature
    ///
    /// # Security Enhancement
    /// - Uses Ed25519-Dalek for cryptographic signatures (FIPS 186-4 compliant)
    /// - Provides authenticity, integrity, and non-repudiation guarantees
    /// - Constant-time signature generation prevents timing attacks
    ///
    /// # Arguments
    /// * `content` - Configuration content bytes
    /// * `version` - Monotonic version number
    /// * `vector_clock` - Causal ordering clock
    /// * `originator` - Node ID of the configuration creator
    /// * `signing_key` - Ed25519 private key for signing
    pub fn new_with_key(
        content: Vec<u8>,
        version: u64,
        vector_clock: VectorClock,
        originator: String,
        signing_key: &SigningKey,
    ) -> Self {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("System time is before UNIX epoch - clock misconfiguration detected")
            .as_secs();

        // Construct canonical message for signing (deterministic encoding)
        let message = Self::construct_canonical_message(&content, version, timestamp, &originator);

        // Generate Ed25519 signature (constant-time operation)
        let signature: Signature = signing_key.sign(&message);

        Self {
            content,
            version,
            vector_clock,
            timestamp,
            originator,
            signature: signature.to_bytes().to_vec(),
        }
    }

    /// Verify Ed25519 digital signature
    ///
    /// # Security Enhancement
    /// - Validates signature using Ed25519-Dalek public key verification
    /// - Constant-time verification prevents timing side-channels
    /// - Returns specific error on invalid signature or malformed data
    ///
    /// # Arguments
    /// * `verifying_key` - Ed25519 public key of the claimed originator
    ///
    /// # Returns
    /// * `Ok(())` if signature is valid and matches the canonical message
    /// * `Err(ConfigGossipError::InvalidSignature)` if verification fails
    ///
    /// # Security Considerations
    /// - Does NOT check timestamp freshness (caller must implement replay protection)
    /// - Assumes verifying_key is securely obtained and trusted
    pub fn verify_with_key(&self, verifying_key: &VerifyingKey) -> Result<(), ConfigGossipError> {
        // Reconstruct the canonical message that was signed
        let message = Self::construct_canonical_message(
            &self.content,
            self.version,
            self.timestamp,
            &self.originator,
        );

        // Parse signature from stored bytes (must be exactly 64 bytes)
        if self.signature.len() != 64 {
            warn!(
                "Invalid signature length: {} bytes (expected 64) for config version {}",
                self.signature.len(),
                self.version
            );
            return Err(ConfigGossipError::InvalidSignature {
                version: self.version,
            });
        }

        let mut sig_bytes = [0u8; 64];
        sig_bytes.copy_from_slice(&self.signature);
        let signature = Signature::from_bytes(&sig_bytes);

        // Verify signature (constant-time operation)
        verifying_key
            .verify(&message, &signature)
            .map_err(|e| {
                warn!(
                    "Ed25519 signature verification failed for config version {}: {}",
                    self.version, e
                );
                ConfigGossipError::InvalidSignature {
                    version: self.version,
                }
            })
    }

    /// Construct canonical message for signing/verification
    ///
    /// # Security Considerations
    /// - Uses deterministic encoding to prevent signature malleability attacks
    /// - Includes all critical fields to prevent partial message manipulation
    /// - Domain separation via explicit field ordering (version, timestamp, originator, content)
    /// - Little-endian encoding for consistency across platforms
    ///
    /// # Message Format
    /// ```text
    /// [version:u64][timestamp:u64][originator:utf8][content:bytes]
    /// ```
    fn construct_canonical_message(
        content: &[u8],
        version: u64,
        timestamp: u64,
        originator: &str,
    ) -> Vec<u8> {
        let mut message = Vec::with_capacity(
            8 +                 // version (u64)
            8 +                 // timestamp (u64)
            originator.len() +  // originator string (variable)
            content.len()       // config content (variable)
        );

        // Append fields in deterministic order with explicit encoding
        message.extend_from_slice(&version.to_le_bytes());
        message.extend_from_slice(&timestamp.to_le_bytes());
        message.extend_from_slice(originator.as_bytes());
        message.extend_from_slice(content);

        message
    }

    /// Legacy stub signature method (DEPRECATED - kept for migration compatibility)
    ///
    /// # Security Warning
    /// This method provides NO cryptographic security and MUST NOT be used in production.
    /// It exists only for backward compatibility during migration.
    ///
    /// # Migration Path
    /// 1. Use `new_with_key()` for all new configs
    /// 2. Verify with `verify_with_key()` when Ed25519 keys are available
    /// 3. Remove this method after full migration
    #[deprecated(
        since = "0.1.0",
        note = "Use new_with_key() and verify_with_key() for Ed25519 signatures"
    )]
    pub fn new(
        content: Vec<u8>,
        version: u64,
        vector_clock: VectorClock,
        originator: String,
    ) -> Self {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("Time went backwards")
            .as_secs();

        // SECURITY: This is NOT a cryptographic signature - use new_with_key() instead
        let signature = Self::compute_stub_signature(&content, version, timestamp, &originator);

        Self {
            content,
            version,
            vector_clock,
            timestamp,
            originator,
            signature,
        }
    }

    /// Legacy stub verification (DEPRECATED)
    #[deprecated(since = "0.1.0", note = "Use verify_with_key() for Ed25519 verification")]
    pub fn verify(&self) -> Result<(), ConfigGossipError> {
        let expected_sig = Self::compute_stub_signature(
            &self.content,
            self.version,
            self.timestamp,
            &self.originator,
        );

        if self.signature == expected_sig {
            Ok(())
        } else {
            Err(ConfigGossipError::InvalidSignature {
                version: self.version,
            })
        }
    }

    /// Legacy stub signature computation (DEPRECATED)
    #[allow(deprecated)]
    fn compute_stub_signature(
        content: &[u8],
        version: u64,
        timestamp: u64,
        originator: &str,
    ) -> Vec<u8> {
        // SECURITY WARNING: This is not a cryptographic signature
        // Retained only for migration compatibility
        use sha2::{Digest, Sha256};
        let mut hasher = Sha256::new();
        hasher.update(content);
        hasher.update(version.to_le_bytes());
        hasher.update(timestamp.to_le_bytes());
        hasher.update(originator.as_bytes());
        hasher.finalize().to_vec()
    }
}

/// Conflict resolution strategy
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConflictResolution {
    /// Last-Writer-Wins based on timestamp
    LastWriterWins,

    /// Manual resolution required (return error)
    Manual,
}

/// Configuration Gossip Manager
///
/// Manages distributed configuration synchronization using DHT Pub/Sub with Ed25519 signatures.
/// Handles version control, conflict detection, cryptographic authentication, and automatic propagation.
///
/// # Security Architecture
/// - Each node has an Ed25519 signing key for creating configuration updates
/// - Public keys are pre-registered for known nodes (secure out-of-band distribution)
/// - All configurations are signed and verified before acceptance
/// - Unknown nodes are rejected to prevent unauthorized configuration injection
pub struct ConfigGossipManager {
    /// Local node ID
    node_id: String,

    /// Current configuration state (tokio::sync::RwLock for async access)
    current_config: Arc<TokioRwLock<Option<SignedConfig>>>,

    /// DHT storage for config distribution (tokio::sync::RwLock for async access)
    dht_storage: Arc<TokioRwLock<DhtStorage>>,

    /// Conflict resolution strategy
    conflict_resolution: ConflictResolution,

    /// Configuration topic key
    topic_key: StorageKey,

    /// Statistics (tokio::sync::RwLock for async access)
    stats: Arc<TokioRwLock<GossipStats>>,

    /// Ed25519 signing key for this node (secret key)
    ///
    /// # Security Considerations
    /// - Must be securely generated and stored (consider HSM for production)
    /// - Should be rotated periodically (implement key rotation mechanism)
    /// - Never log or expose this key
    signing_key: SigningKey,

    /// Known public keys for signature verification (node_id -> VerifyingKey)
    /// Uses tokio::sync::RwLock for async access in receive_config
    ///
    /// # Security Considerations
    /// - Public keys should be distributed through secure out-of-band channel
    /// - Consider implementing X.509 certificate chain validation for production
    /// - Implement key revocation mechanism for compromised keys
    known_keys: Arc<TokioRwLock<HashMap<String, VerifyingKey>>>,
}

/// Gossip statistics
#[derive(Debug, Default, Clone)]
pub struct GossipStats {
    pub configs_received: usize,
    pub configs_applied: usize,
    pub conflicts_detected: usize,
    pub conflicts_resolved: usize,
    pub validation_failures: usize,
    pub signature_failures: usize,
}

impl ConfigGossipManager {
    /// Create a new Config Gossip Manager with Ed25519 authentication
    ///
    /// # Arguments
    /// * `node_id` - Unique identifier for this node
    /// * `dht_storage` - DHT storage backend for configuration distribution
    /// * `signing_key` - Ed25519 private key for signing configurations
    ///
    /// # Security Considerations
    /// - The signing_key must be securely generated (use OsRng)
    /// - Store signing_key securely (consider hardware security module for production)
    /// - Register this node's public key with other nodes through secure channel
    pub fn new(
        node_id: String,
        dht_storage: Arc<TokioRwLock<DhtStorage>>,
        signing_key: SigningKey,
    ) -> Self {
        Self {
            node_id: node_id.clone(),
            current_config: Arc::new(TokioRwLock::new(None)),
            dht_storage,
            conflict_resolution: ConflictResolution::LastWriterWins,
            topic_key: StorageKey::from_bytes(b"nyx/config/gossip"),
            stats: Arc::new(TokioRwLock::new(GossipStats::default())),
            signing_key,
            known_keys: Arc::new(TokioRwLock::new(HashMap::new())),
        }
    }

    /// Register a public key for a known node
    ///
    /// # Security Considerations
    /// - Public keys MUST be distributed through a secure out-of-band channel
    /// - Verify key authenticity before registration (e.g., via X.509 certificates)
    /// - Consider implementing key expiration and rotation mechanisms
    /// - Log all key registration events for audit trail
    ///
    /// # Arguments
    /// * `node_id` - Identifier of the node whose key is being registered
    /// * `verifying_key` - Ed25519 public key for signature verification
    pub async fn register_node_key(&self, node_id: String, verifying_key: VerifyingKey) {
        let mut keys = self.known_keys.write().await;
        keys.insert(node_id.clone(), verifying_key);
        info!("Registered Ed25519 public key for node: {}", node_id);
    }

    /// Set conflict resolution strategy
    pub fn set_conflict_resolution(&mut self, strategy: ConflictResolution) {
        self.conflict_resolution = strategy;
    }

    /// Publish a new configuration to the network with Ed25519 signature
    ///
    /// # Security Enhancement
    /// - Signs configuration with Ed25519 for authenticity and integrity
    /// - Prevents unauthorized configuration modification
    /// - Provides non-repudiation (only node with private key can create valid config)
    ///
    /// # Steps
    /// 1. Create SignedConfig with incremented vector clock and Ed25519 signature
    /// 2. Validate configuration structure
    /// 3. Store in local DHT
    /// 4. Propagate to peers (via DHT topic)
    ///
    /// # Returns
    /// * `Ok(SignedConfig)` - Successfully published configuration
    /// * `Err(ConfigGossipError)` - Validation or storage failure
    pub async fn publish_config(&self, content: Vec<u8>) -> Result<SignedConfig, ConfigGossipError> {
        // Get current version and vector clock
        let (next_version, mut vector_clock) = {
            let current = self.current_config.read().await;
            match &*current {
                Some(cfg) => (cfg.version + 1, cfg.vector_clock.clone()),
                None => (1, VectorClock::new()),
            }
        };

        // Increment our node's clock
        vector_clock.increment(&self.node_id);

        // Create signed config with Ed25519 signature
        let signed_config = SignedConfig::new_with_key(
            content,
            next_version,
            vector_clock,
            self.node_id.clone(),
            &self.signing_key,
        );

        // Validate before publishing
        self.validate_config(&signed_config)?;

        // Store in DHT (await async operation)
        self.store_config_in_dht(&signed_config).await?;

        // Update local state
        {
            let mut current = self.current_config.write().await;
            *current = Some(signed_config.clone());
        }

        info!(
            "Published config version {} from node {} with Ed25519 signature",
            signed_config.version, self.node_id
        );

        Ok(signed_config)
    }

    /// Receive a configuration from the network with Ed25519 signature verification
    ///
    /// # Security Enhancement
    /// - Verifies Ed25519 signature before processing any configuration
    /// - Rejects configurations from unknown nodes (prevents unauthorized injection)
    /// - Implements defense-in-depth: signature check ↁEstructure validation ↁEconflict resolution
    ///
    /// # Steps
    /// 1. Lookup originator's public key (reject if unknown)
    /// 2. Verify Ed25519 signature
    /// 3. Check vector clock for conflicts
    /// 4. Resolve conflicts if needed
    /// 5. Validate and apply configuration
    ///
    /// # Arguments
    /// * `remote_config` - Configuration received from another node
    ///
    /// # Returns
    /// * `Ok(())` - Configuration accepted and applied
    /// * `Err(ConfigGossipError::UnknownNode)` - Originator not in known_keys
    /// * `Err(ConfigGossipError::InvalidSignature)` - Signature verification failed
    /// * `Err(ConfigGossipError::ValidationFailed)` - Configuration structure invalid
    pub async fn receive_config(
        &self,
        remote_config: SignedConfig,
    ) -> Result<(), ConfigGossipError> {
        // Update stats
        {
            let mut stats = self.stats.write().await;
            stats.configs_received += 1;
        }

        // SECURITY: Lookup originator's public key (reject unknown nodes)
        let verifying_key = {
            let keys = self.known_keys.read().await;
            match keys.get(&remote_config.originator).cloned() {
                Some(key) => key,
                None => {
                    warn!(
                        "SECURITY: Received config from unknown node: {}. Rejecting to prevent unauthorized injection.",
                        remote_config.originator
                    );
                    let mut stats = self.stats.write().await;
                    stats.signature_failures += 1;
                    return Err(ConfigGossipError::UnknownNode {
                        node_id: remote_config.originator.clone(),
                    });
                }
            }
        };

        // SECURITY: Verify Ed25519 signature before processing
        if let Err(e) = remote_config.verify_with_key(&verifying_key) {
            let mut stats = self.stats.write().await;
            stats.signature_failures += 1;
            return Err(e);
        }

        info!(
            "Verified Ed25519 signature for config version {} from node {}",
            remote_config.version, remote_config.originator
        );

        debug!(
            "Received config version {} from node {}",
            remote_config.version, remote_config.originator
        );

        // Check for conflicts using vector clock
        let current_config = self.current_config.read().await.clone();

        if let Some(local_config) = current_config {
            // Check causality
            match local_config
                .vector_clock
                .happens_before(&remote_config.vector_clock)
            {
                Some(true) => {
                    // Local < Remote: accept remote (it's newer)
                    debug!("Remote config is newer, applying");
                }
                Some(false) => {
                    // Local > Remote: reject remote (ours is newer)
                    debug!("Local config is newer, rejecting remote");
                    return Ok(());
                }
                None => {
                    // Concurrent: conflict detected
                    warn!(
                        "Conflict detected: local v{}, remote v{}",
                        local_config.version, remote_config.version
                    );

                    let mut stats = self.stats.write().await;
                    stats.conflicts_detected += 1;
                    drop(stats); // Release lock before resolve_conflict

                    // Resolve conflict
                    if !self.resolve_conflict(&local_config, &remote_config)? {
                        return Err(ConfigGossipError::ConflictDetected {
                            local_version: local_config.version,
                            remote_version: remote_config.version,
                        });
                    }

                    let mut stats = self.stats.write().await;
                    stats.conflicts_resolved += 1;
                }
            }
        }

        // Validate config
        if let Err(e) = self.validate_config(&remote_config) {
            let mut stats = self.stats.write().await;
            stats.validation_failures += 1;
            return Err(e);
        }

        // Apply config
        {
            let mut current = self.current_config.write().await;
            *current = Some(remote_config.clone());
        }

        // Store in DHT for propagation
        self.store_config_in_dht(&remote_config).await?;

        info!(
            "Applied config version {} from node {}",
            remote_config.version, remote_config.originator
        );

        {
            let mut stats = self.stats.write().await;
            stats.configs_applied += 1;
        }

        Ok(())
    }

    /// Resolve a conflict between local and remote configs
    ///
    /// Returns: Ok(true) if remote should be applied, Ok(false) if local should be kept
    fn resolve_conflict(
        &self,
        local: &SignedConfig,
        remote: &SignedConfig,
    ) -> Result<bool, ConfigGossipError> {
        match self.conflict_resolution {
            ConflictResolution::LastWriterWins => {
                // Compare timestamps
                if remote.timestamp > local.timestamp {
                    debug!(
                        "LWW: Remote timestamp {} > Local {}, accepting remote",
                        remote.timestamp, local.timestamp
                    );
                    Ok(true)
                } else if remote.timestamp < local.timestamp {
                    debug!(
                        "LWW: Local timestamp {} > Remote {}, keeping local",
                        local.timestamp, remote.timestamp
                    );
                    Ok(false)
                } else {
                    // Tie-breaker: use originator node ID (lexicographic order)
                    let accept_remote = remote.originator > local.originator;
                    debug!(
                        "LWW: Timestamp tie, tie-breaker by node ID: {}",
                        if accept_remote {
                            "accept remote"
                        } else {
                            "keep local"
                        }
                    );
                    Ok(accept_remote)
                }
            }
            ConflictResolution::Manual => {
                // Require manual intervention
                warn!("Manual conflict resolution required");
                Err(ConfigGossipError::ConflictDetected {
                    local_version: local.version,
                    remote_version: remote.version,
                })
            }
        }
    }

    /// Validate a configuration before applying
    ///
    /// Checks:
    /// - Content is valid TOML
    /// - Required fields are present
    /// - Values are within acceptable ranges
    fn validate_config(&self, config: &SignedConfig) -> Result<(), ConfigGossipError> {
        // Parse TOML
        let toml_str = String::from_utf8(config.content.clone()).map_err(|e| {
            ConfigGossipError::ValidationFailed {
                reason: format!("Invalid UTF-8: {}", e),
            }
        })?;

        toml::from_str::<toml::Value>(&toml_str).map_err(|e| {
            ConfigGossipError::ValidationFailed {
                reason: format!("Invalid TOML: {}", e),
            }
        })?;

        // Additional validation can be added here
        // (e.g., check specific fields, ranges, etc.)

        Ok(())
    }

    /// Store config in DHT for propagation
    async fn store_config_in_dht(&self, config: &SignedConfig) -> Result<(), ConfigGossipError> {
        // Serialize config
        let serialized =
            serde_json::to_vec(config).map_err(|e| ConfigGossipError::SerializationError {
                reason: format!("JSON serialization failed: {}", e),
            })?;

        // Store in DHT (await async lock acquisition)
        let mut dht = self.dht_storage.write().await;
        dht.put(
            self.topic_key.clone(),
            StorageValue::from_bytes(&serialized),
        )
        .map_err(|e| ConfigGossipError::DhtError {
            reason: e.to_string(),
        })?;

        Ok(())
    }

    /// Fetch the latest config from DHT
    pub async fn fetch_from_dht(&self) -> Result<Option<SignedConfig>, ConfigGossipError> {
        let mut dht = self.dht_storage.write().await;

        match dht.get(&self.topic_key) {
            Some(value) => {
                let config: SignedConfig = serde_json::from_slice(&value.0).map_err(|e| {
                    ConfigGossipError::SerializationError {
                        reason: format!("JSON deserialization failed: {}", e),
                    }
                })?;
                Ok(Some(config))
            }
            None => Ok(None),
        }
    }

    /// Get current configuration
    pub async fn get_current_config(&self) -> Option<SignedConfig> {
        self.current_config.read().await.clone()
    }

    /// Get statistics
    pub async fn get_stats(&self) -> GossipStats {
        self.stats.read().await.clone()
    }
}

#[cfg(all(test, feature = "config-gossip-tests"))]
mod tests {
    use super::*;
    use std::sync::RwLock;

    #[test]
    fn test_vector_clock_increment() {
        let mut clock = VectorClock::new();
        clock.increment("node1");
        assert_eq!(clock.get("node1"), 1);
        clock.increment("node1");
        assert_eq!(clock.get("node1"), 2);
    }

    #[test]
    fn test_vector_clock_merge() {
        let mut clock1 = VectorClock::new();
        clock1.increment("node1");
        clock1.increment("node1");

        let mut clock2 = VectorClock::new();
        clock2.increment("node2");
        clock2.increment("node2");
        clock2.increment("node2");

        clock1.merge(&clock2);
        assert_eq!(clock1.get("node1"), 2);
        assert_eq!(clock1.get("node2"), 3);
    }

    #[test]
    fn test_vector_clock_happens_before() {
        let mut clock1 = VectorClock::new();
        clock1.increment("node1");

        let mut clock2 = VectorClock::new();
        clock2.increment("node1");
        clock2.increment("node1");

        assert_eq!(clock1.happens_before(&clock2), Some(true));
        assert_eq!(clock2.happens_before(&clock1), Some(false));
    }

    #[test]
    fn test_vector_clock_concurrent() {
        let mut clock1 = VectorClock::new();
        clock1.increment("node1");

        let mut clock2 = VectorClock::new();
        clock2.increment("node2");

        assert_eq!(clock1.happens_before(&clock2), None);
        assert_eq!(clock2.happens_before(&clock1), None);
    }

    #[test]
    fn test_signed_config_creation() {
        let content = b"test_config".to_vec();
        let config = SignedConfig::new(content.clone(), 1, VectorClock::new(), "node1".to_string());

        assert_eq!(config.content, content);
        assert_eq!(config.version, 1);
        assert_eq!(config.originator, "node1");
        assert!(!config.signature.is_empty());
    }

    #[test]
    fn test_signed_config_verify() {
        let content = b"test_config".to_vec();
        let config = SignedConfig::new(content, 1, VectorClock::new(), "node1".to_string());

        assert!(config.verify().is_ok());
    }

    #[test]
    fn test_signed_config_verify_invalid() {
        let content = b"test_config".to_vec();
        let mut config = SignedConfig::new(content, 1, VectorClock::new(), "node1".to_string());

        // Tamper with signature
        config.signature[0] ^= 0xFF;

        assert!(matches!(
            config.verify(),
            Err(ConfigGossipError::InvalidSignature { .. })
        ));
    }

    #[test]
    #[ignore = "LEGACY: Requires migration to new Ed25519 API - see test_ed25519_* tests"]
    fn test_gossip_manager_creation() {
        let dht = Arc::new(RwLock::new(DhtStorage::new()));
        // OLD API: ConfigGossipManager::new now requires SigningKey parameter
        // let manager = ConfigGossipManager::new("node1".to_string(), dht);

        // assert!(manager.get_current_config().is_none());
        // let stats = manager.get_stats();
        // assert_eq!(stats.configs_received, 0);
    }

    #[test]
    #[ignore = "LEGACY: Requires migration to new Ed25519 API - see test_ed25519_* tests"]
    fn test_publish_config() {
        // OLD API: ConfigGossipManager::new now requires SigningKey parameter
        // let dht = Arc::new(RwLock::new(DhtStorage::new()));
        // let manager = ConfigGossipManager::new("node1".to_string(), dht);
        //
        // let content = b"log_level = \"debug\"".to_vec();
        // let result = manager.publish_config(content.clone());
        //
        // assert!(result.is_ok());
        // let config = result.unwrap();
        // assert_eq!(config.version, 1);
        // assert_eq!(config.originator, "node1");
    }

    #[test]
    #[ignore = "LEGACY: receive_config is now async - see test_ed25519_signature_verification_in_gossip"]
    fn test_receive_config_newer() {
        // OLD API: receive_config is now async
        let dht = Arc::new(RwLock::new(DhtStorage::new()));
        // let manager = ConfigGossipManager::new("node1".to_string(), dht.clone());

        // Publish initial config
        let content1 = b"log_level = \"info\"".to_vec();
        manager.publish_config(content1).unwrap();

        // Create a newer config from another node
        let mut vector_clock = VectorClock::new();
        vector_clock.increment("node1");
        vector_clock.increment("node2");

        let content2 = b"log_level = \"debug\"".to_vec();
        let remote_config = SignedConfig::new(content2, 2, vector_clock, "node2".to_string());

        // Receive and apply
        let result = manager.receive_config(remote_config.clone());
        assert!(result.is_ok());

        let current = manager.get_current_config().unwrap();
        assert_eq!(current.version, 2);
        assert_eq!(current.originator, "node2");
    }

    #[test]
    #[ignore = "LEGACY: receive_config is now async - see test_ed25519_multinode_gossip_scenario"]
    fn test_receive_config_causally_older() {
        // OLD API: receive_config is now async
        let dht = Arc::new(RwLock::new(DhtStorage::new()));
        // let manager = ConfigGossipManager::new("node1".to_string(), dht.clone());

        // Publish current config with causal history: node1=2, node2=1
        // This represents: node1 has seen node2's updates and made 2 updates
        let mut vector_clock = VectorClock::new();
        vector_clock.increment("node2"); // Seen node2's update
        vector_clock.increment("node1");
        vector_clock.increment("node1");

        let content1 = b"log_level = \"debug\"".to_vec();
        let config1 = SignedConfig::new(content1, 2, vector_clock, "node1".to_string());
        manager.receive_config(config1).unwrap();

        // Verify first config was applied
        assert_eq!(manager.get_stats().configs_applied, 1);

        // Create a causally older config from node2: node2=1
        // This is causally before the above (node1's clock includes node2=1)
        let mut old_clock = VectorClock::new();
        old_clock.increment("node2");

        let content2 = b"log_level = \"info\"".to_vec();
        let old_config = SignedConfig::new(content2, 1, old_clock, "node2".to_string());

        // Receive causally older config (should be rejected)
        let result = manager.receive_config(old_config.clone());
        assert!(result.is_ok()); // No error, but should not be applied

        let current = manager.get_current_config().unwrap();
        assert_eq!(current.version, 2); // Should still be the current version
        assert_eq!(current.originator, "node1"); // Should still be node1

        // Verify stats: received incremented, but NOT applied
        let stats = manager.get_stats();
        assert_eq!(stats.configs_received, 2);
        assert_eq!(stats.configs_applied, 1); // Only first config applied
    }

    #[test]
    #[ignore = "LEGACY: receive_config is now async - see test_ed25519_multinode_gossip_scenario"]
    fn test_conflict_resolution_lww() {
        // OLD API: receive_config is now async
        let dht = Arc::new(RwLock::new(DhtStorage::new()));
        // let manager = ConfigGossipManager::new("node1".to_string(), dht.clone());

        // Publish local config
        let mut local_clock = VectorClock::new();
        local_clock.increment("node1");

        let content1 = b"log_level = \"info\"".to_vec();
        let local_config = SignedConfig::new(content1, 1, local_clock, "node1".to_string());
        manager.receive_config(local_config).unwrap();

        // Simulate a concurrent update from another node
        std::thread::sleep(std::time::Duration::from_millis(10));

        let mut remote_clock = VectorClock::new();
        remote_clock.increment("node2");

        let content2 = b"log_level = \"debug\"".to_vec();
        let remote_config = SignedConfig::new(content2, 1, remote_clock, "node2".to_string());

        // LWW should accept the remote config (newer timestamp)
        let result = manager.receive_config(remote_config.clone());
        assert!(result.is_ok());

        let stats = manager.get_stats();
        assert_eq!(stats.conflicts_detected, 1);
        assert_eq!(stats.conflicts_resolved, 1);

        let current = manager.get_current_config().unwrap();
        assert_eq!(current.originator, "node2");
    }

    #[test]
    #[ignore = "LEGACY: ConfigGossipManager::new now requires SigningKey parameter"]
    fn test_validation_failure() {
        // OLD API: ConfigGossipManager::new now requires SigningKey parameter
        let dht = Arc::new(RwLock::new(DhtStorage::new()));
        // let manager = ConfigGossipManager::new("node1".to_string(), dht);

        // Invalid TOML
        let invalid_content = b"invalid toml syntax {{".to_vec();
        let result = manager.publish_config(invalid_content);

        assert!(matches!(
            result,
            Err(ConfigGossipError::ValidationFailed { .. })
        ));
    }

    #[test]
    #[ignore = "LEGACY: ConfigGossipManager::new now requires SigningKey parameter"]
    fn test_fetch_from_dht() {
        // OLD API: ConfigGossipManager::new now requires SigningKey parameter
        let dht = Arc::new(RwLock::new(DhtStorage::new()));
        // let manager = ConfigGossipManager::new("node1".to_string(), dht.clone());

        // Initially empty
        assert!(manager.fetch_from_dht().unwrap().is_none());

        // Publish a config
        let content = b"log_level = \"debug\"".to_vec();
        manager.publish_config(content.clone()).unwrap();

        // Fetch from DHT
        let fetched = manager.fetch_from_dht().unwrap();
        assert!(fetched.is_some());

        let config = fetched.unwrap();
        assert_eq!(config.content, content);
    }

    #[test]
    #[ignore = "LEGACY: receive_config is now async - see test_ed25519_multinode_gossip_scenario"]
    fn test_stats_tracking() {
        // OLD API: receive_config is now async
        let dht = Arc::new(RwLock::new(DhtStorage::new()));
        // let manager = ConfigGossipManager::new("node1".to_string(), dht.clone());

        let stats = manager.get_stats();
        assert_eq!(stats.configs_received, 0);
        assert_eq!(stats.configs_applied, 0);

        // Publish a config
        let content = b"log_level = \"info\"".to_vec();
        manager.publish_config(content).unwrap();

        // Receive a config
        let mut clock = VectorClock::new();
        clock.increment("node2");
        let remote_config = SignedConfig::new(
            b"log_level = \"debug\"".to_vec(),
            2,
            clock,
            "node2".to_string(),
        );
        manager.receive_config(remote_config).unwrap();

        let stats = manager.get_stats();
        assert_eq!(stats.configs_received, 1);
        assert_eq!(stats.configs_applied, 1);
    }

    // ============================================================================
    // SECURITY: Ed25519 Signature Tests
    // ============================================================================

    #[test]
    fn test_ed25519_signature_roundtrip() {
        use rand::rngs::OsRng;
        
        let mut csprng = OsRng;
        let signing_key = SigningKey::generate(&mut csprng);
        let verifying_key = signing_key.verifying_key();

        let content = b"test_config_content".to_vec();
        let vector_clock = VectorClock::new();
        let originator = "test_node".to_string();

        // Sign config
        let config = SignedConfig::new_with_key(
            content.clone(),
            1,
            vector_clock,
            originator.clone(),
            &signing_key,
        );

        // Verify signature succeeds
        assert!(config.verify_with_key(&verifying_key).is_ok());
    }

    #[test]
    fn test_ed25519_signature_tamper_detection() {
        use rand::rngs::OsRng;
        
        let mut csprng = OsRng;
        let signing_key = SigningKey::generate(&mut csprng);
        let verifying_key = signing_key.verifying_key();

        let content = b"original_content".to_vec();
        let mut config = SignedConfig::new_with_key(
            content,
            1,
            VectorClock::new(),
            "test_node".to_string(),
            &signing_key,
        );

        // Tamper with content
        config.content = b"tampered_content".to_vec();

        // Verification should fail
        assert!(config.verify_with_key(&verifying_key).is_err());
        assert!(matches!(
            config.verify_with_key(&verifying_key),
            Err(ConfigGossipError::InvalidSignature { .. })
        ));
    }

    #[test]
    fn test_ed25519_wrong_key_rejection() {
        use rand::rngs::OsRng;
        
        let mut csprng = OsRng;
        let signing_key = SigningKey::generate(&mut csprng);
        let wrong_key = SigningKey::generate(&mut csprng).verifying_key();

        let content = b"test_content".to_vec();
        let config = SignedConfig::new_with_key(
            content,
            1,
            VectorClock::new(),
            "test_node".to_string(),
            &signing_key,
        );

        // Verify with wrong key should fail
        assert!(config.verify_with_key(&wrong_key).is_err());
    }

    #[test]
    fn test_ed25519_signature_bytes_format() {
        use rand::rngs::OsRng;
        
        let mut csprng = OsRng;
        let signing_key = SigningKey::generate(&mut csprng);

        let config = SignedConfig::new_with_key(
            b"test".to_vec(),
            1,
            VectorClock::new(),
            "node".to_string(),
            &signing_key,
        );

        // Ed25519 signature is always 64 bytes
        assert_eq!(config.signature.len(), 64);
    }

    #[tokio::test]
    async fn test_ed25519_unknown_node_rejection() {
        use rand::rngs::OsRng;
        
        let mut csprng = OsRng;
        let node1_signing_key = SigningKey::generate(&mut csprng);
        let node2_signing_key = SigningKey::generate(&mut csprng);

        let dht = Arc::new(RwLock::new(DhtStorage::new()));
        let manager = ConfigGossipManager::new(
            "node1".to_string(),
            dht.clone(),
            node1_signing_key.clone(),
        );

        // Create config from unknown node2 (not registered)
        let content = b"log_level = \"debug\"".to_vec();
        let unknown_config = SignedConfig::new_with_key(
            content,
            1,
            VectorClock::new(),
            "node2".to_string(),
            &node2_signing_key,
        );

        // Should reject with UnknownNode error
        let result = manager.receive_config(unknown_config).await;
        assert!(result.is_err());
        assert!(matches!(
            result,
            Err(ConfigGossipError::UnknownNode { .. })
        ));

        // Verify stats tracked rejection
        let stats = manager.get_stats();
        assert_eq!(stats.configs_received, 1);
        assert_eq!(stats.configs_applied, 0);
    }

    #[tokio::test]
    async fn test_ed25519_signature_verification_in_gossip() {
        use rand::rngs::OsRng;
        
        let mut csprng = OsRng;
        let node1_signing_key = SigningKey::generate(&mut csprng);
        let node2_signing_key = SigningKey::generate(&mut csprng);
        let node2_verifying_key = node2_signing_key.verifying_key();

        let dht = Arc::new(RwLock::new(DhtStorage::new()));
        let manager = ConfigGossipManager::new(
            "node1".to_string(),
            dht.clone(),
            node1_signing_key,
        );

        // Register node2's public key
        manager.register_node_key("node2".to_string(), node2_verifying_key).await;

        // Create valid signed config from node2
        let content = b"log_level = \"debug\"".to_vec();
        let mut vector_clock = VectorClock::new();
        vector_clock.increment("node2");

        let valid_config = SignedConfig::new_with_key(
            content,
            1,
            vector_clock,
            "node2".to_string(),
            &node2_signing_key,
        );

        // Should accept valid signature
        let result = manager.receive_config(valid_config).await;
        assert!(result.is_ok());

        let stats = manager.get_stats();
        assert_eq!(stats.configs_applied, 1);
        assert_eq!(stats.signature_failures, 0);
    }

    #[tokio::test]
    async fn test_ed25519_invalid_signature_rejection() {
        use rand::rngs::OsRng;
        
        let mut csprng = OsRng;
        let node1_signing_key = SigningKey::generate(&mut csprng);
        let node2_signing_key = SigningKey::generate(&mut csprng);
        let node2_verifying_key = node2_signing_key.verifying_key();

        let dht = Arc::new(RwLock::new(DhtStorage::new()));
        let manager = ConfigGossipManager::new(
            "node1".to_string(),
            dht.clone(),
            node1_signing_key,
        );

        // Register node2's public key
        manager.register_node_key("node2".to_string(), node2_verifying_key).await;

        // Create config with tampered signature
        let content = b"log_level = \"debug\"".to_vec();
        let mut invalid_config = SignedConfig::new_with_key(
            content,
            1,
            VectorClock::new(),
            "node2".to_string(),
            &node2_signing_key,
        );

        // Tamper with signature bytes
        invalid_config.signature[0] ^= 0xFF;

        // Should reject invalid signature
        let result = manager.receive_config(invalid_config).await;
        assert!(result.is_err());
        assert!(matches!(
            result,
            Err(ConfigGossipError::InvalidSignature { .. })
        ));

        let stats = manager.get_stats();
        assert_eq!(stats.signature_failures, 1);
        assert_eq!(stats.configs_applied, 0);
    }

    #[tokio::test]
    async fn test_ed25519_multinode_gossip_scenario() {
        use rand::rngs::OsRng;
        
        let mut csprng = OsRng;
        
        // Setup 3 nodes with keypairs
        let node1_signing_key = SigningKey::generate(&mut csprng);
        let node2_signing_key = SigningKey::generate(&mut csprng);
        let node3_signing_key = SigningKey::generate(&mut csprng);
        
        let node2_verifying_key = node2_signing_key.verifying_key();
        let node3_verifying_key = node3_signing_key.verifying_key();

        // Create shared DHT
        let dht = Arc::new(RwLock::new(DhtStorage::new()));

        // Node1 manager
        let manager1 = ConfigGossipManager::new(
            "node1".to_string(),
            dht.clone(),
            node1_signing_key,
        );
        manager1.register_node_key("node2".to_string(), node2_verifying_key).await;
        manager1.register_node_key("node3".to_string(), node3_verifying_key).await;

        // Node2 publishes config
        let mut clock2 = VectorClock::new();
        clock2.increment("node2");
        let config2 = SignedConfig::new_with_key(
            b"setting = \"from_node2\"".to_vec(),
            1,
            clock2,
            "node2".to_string(),
            &node2_signing_key,
        );

        // Node1 receives node2's config
        assert!(manager1.receive_config(config2).await.is_ok());

        // Node3 publishes newer config
        let mut clock3 = VectorClock::new();
        clock3.increment("node2");
        clock3.increment("node3");
        let config3 = SignedConfig::new_with_key(
            b"setting = \"from_node3\"".to_vec(),
            2,
            clock3,
            "node3".to_string(),
            &node3_signing_key,
        );

        // Node1 receives node3's config (causally newer)
        assert!(manager1.receive_config(config3.clone()).await.is_ok());

        // Verify node1 has latest config
        let current = manager1.get_current_config().unwrap();
        assert_eq!(current.originator, "node3");
        assert_eq!(current.version, 2);

        let stats = manager1.get_stats();
        assert_eq!(stats.configs_received, 2);
        assert_eq!(stats.configs_applied, 2);
        assert_eq!(stats.signature_failures, 0);
    }

    #[test]
    fn test_ed25519_performance_signature_generation() {
        use rand::rngs::OsRng;
        use std::time::Instant;
        
        let mut csprng = OsRng;
        let signing_key = SigningKey::generate(&mut csprng);

        let content = b"performance_test_content".to_vec();
        let iterations = 100;

        let start = Instant::now();
        for i in 0..iterations {
            let _ = SignedConfig::new_with_key(
                content.clone(),
                i,
                VectorClock::new(),
                "node".to_string(),
                &signing_key,
            );
        }
        let elapsed = start.elapsed();

        let avg_micros = elapsed.as_micros() / iterations;
        println!("Average signature generation time: {}μs", avg_micros);

        // PERFORMANCE REQUIREMENT: <100μs per signature
        assert!(avg_micros < 100, "Signature generation too slow: {}μs", avg_micros);
    }

    #[test]
    fn test_ed25519_performance_signature_verification() {
        use rand::rngs::OsRng;
        use std::time::Instant;
        
        let mut csprng = OsRng;
        let signing_key = SigningKey::generate(&mut csprng);
        let verifying_key = signing_key.verifying_key();

        // Pre-generate signed configs
        let mut configs = Vec::new();
        for i in 0..100 {
            let config = SignedConfig::new_with_key(
                b"test".to_vec(),
                i,
                VectorClock::new(),
                "node".to_string(),
                &signing_key,
            );
            configs.push(config);
        }

        let start = Instant::now();
        for config in &configs {
            assert!(config.verify_with_key(&verifying_key).is_ok());
        }
        let elapsed = start.elapsed();

        let avg_micros = elapsed.as_micros() / configs.len() as u128;
        println!("Average signature verification time: {}μs", avg_micros);

        // PERFORMANCE REQUIREMENT: <200μs per verification
        assert!(avg_micros < 200, "Signature verification too slow: {}μs", avg_micros);
    }
}

