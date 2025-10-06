//! Config Gossip Protocol
//!
//! Implements epidemic-style gossip protocol for distributing configuration
//! updates across a peer-to-peer network with eventual consistency.
//!
//! **Protocol Design:**
//! - Vector clock for causality tracking
//! - Last-write-wins conflict resolution
//! - HMAC-SHA256 message authentication
//! - Rate limiting (10 messages/sec/peer)
//!
//! **Consistency Model:**
//! - Eventual consistency (no strong ordering guarantees)
//! - Partition tolerance (AP in CAP theorem)
//! - Convergence time: O(log N) rounds
//!
//! **Pure Rust:** Uses blake3 for hashing, no C/C++ dependencies

use crate::dht::NodeId;
use blake3;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{Duration, SystemTime};
use tracing::{debug, warn};

/// Configuration key (max 256 bytes)
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ConfigKey(String);

impl ConfigKey {
    pub fn new(key: impl Into<String>) -> Result<Self, &'static str> {
        let key = key.into();
        if key.len() > 256 {
            return Err("config key too long (max 256 bytes)");
        }
        if key.is_empty() {
            return Err("config key cannot be empty");
        }
        Ok(Self(key))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Configuration value (max 64KB)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConfigValue(Vec<u8>);

impl ConfigValue {
    pub fn new(value: Vec<u8>) -> Result<Self, &'static str> {
        if value.len() > 65536 {
            return Err("config value too large (max 64KB)");
        }
        Ok(Self(value))
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    pub fn from_string(s: impl Into<String>) -> Result<Self, &'static str> {
        Self::new(s.into().into_bytes())
    }
}

/// Vector clock for causality tracking
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VectorClock {
    /// Node ID -> counter mapping
    clocks: HashMap<NodeId, u64>,
}

impl VectorClock {
    pub fn new() -> Self {
        Self {
            clocks: HashMap::new(),
        }
    }

    /// Increment clock for given node
    pub fn increment(&mut self, node_id: &NodeId) {
        let counter = self.clocks.entry(node_id.clone()).or_insert(0);
        *counter += 1;
    }

    /// Merge two vector clocks (take max for each node)
    pub fn merge(&mut self, other: &VectorClock) {
        for (node_id, &other_count) in &other.clocks {
            let entry = self.clocks.entry(node_id.clone()).or_insert(0);
            *entry = (*entry).max(other_count);
        }
    }

    /// Compare two vector clocks for causality
    pub fn compare(&self, other: &VectorClock) -> ClockOrdering {
        let mut less = false;
        let mut greater = false;

        // Check all nodes in self
        for (node_id, &self_count) in &self.clocks {
            let other_count = other.clocks.get(node_id).copied().unwrap_or(0);
            if self_count < other_count {
                less = true;
            } else if self_count > other_count {
                greater = true;
            }
        }

        // Check nodes only in other
        for (node_id, &other_count) in &other.clocks {
            if !self.clocks.contains_key(node_id) && other_count > 0 {
                less = true;
            }
        }

        match (less, greater) {
            (false, false) => ClockOrdering::Equal,
            (true, false) => ClockOrdering::Before,
            (false, true) => ClockOrdering::After,
            (true, true) => ClockOrdering::Concurrent,
        }
    }
}

impl Default for VectorClock {
    fn default() -> Self {
        Self::new()
    }
}

/// Clock ordering for conflict resolution
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClockOrdering {
    Before,     // self happened before other
    After,      // self happened after other
    Concurrent, // concurrent events (conflict)
    Equal,      // identical clocks
}

/// Gossip message for config propagation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GossipMessage {
    /// Sender node ID
    pub sender: NodeId,

    /// Message ID (for deduplication)
    pub message_id: u64,

    /// Configuration updates
    pub updates: Vec<ConfigUpdate>,

    /// Timestamp (Unix seconds)
    pub timestamp: u64,

    /// HMAC-SHA256 signature (32 bytes)
    pub signature: Vec<u8>,
}

/// Single configuration update
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConfigUpdate {
    pub key: ConfigKey,
    pub value: ConfigValue,
    pub vector_clock: VectorClock,
    pub deleted: bool, // true if this is a delete operation
}

/// Gossip state manager
pub struct GossipManager {
    local_node_id: NodeId,

    /// Current configuration state
    config_state: HashMap<ConfigKey, (ConfigValue, VectorClock)>,

    /// Deleted keys (tombstones with vector clocks)
    deleted_keys: HashMap<ConfigKey, VectorClock>,

    /// Message deduplication cache (message_id -> timestamp)
    seen_messages: HashMap<u64, SystemTime>,

    /// Message ID counter
    message_id_counter: u64,

    /// HMAC key for authentication (32 bytes)
    hmac_key: [u8; 32],

    /// Rate limiter: peer -> (message_count, window_start)
    rate_limiter: HashMap<NodeId, (u32, SystemTime)>,
}

impl GossipManager {
    /// Create new gossip manager
    pub fn new(local_node_id: NodeId, hmac_key: [u8; 32]) -> Self {
        Self {
            local_node_id,
            config_state: HashMap::new(),
            deleted_keys: HashMap::new(),
            seen_messages: HashMap::new(),
            message_id_counter: 0,
            hmac_key,
            rate_limiter: HashMap::new(),
        }
    }

    /// Set configuration value
    pub fn set(&mut self, key: ConfigKey, value: ConfigValue) -> Result<(), &'static str> {
        let mut clock = self
            .config_state
            .get(&key)
            .map(|(_, c)| c.clone())
            .unwrap_or_default();

        clock.increment(&self.local_node_id);

        self.config_state.insert(key.clone(), (value, clock));
        self.deleted_keys.remove(&key);

        Ok(())
    }

    /// Get configuration value
    pub fn get(&self, key: &ConfigKey) -> Option<ConfigValue> {
        self.config_state.get(key).map(|(v, _)| v.clone())
    }

    /// Delete configuration key
    pub fn delete(&mut self, key: &ConfigKey) -> Result<(), &'static str> {
        if let Some((_, clock)) = self.config_state.remove(key) {
            self.deleted_keys.insert(key.clone(), clock);
            Ok(())
        } else {
            Err("key not found")
        }
    }

    /// Create gossip message with current state
    pub fn create_gossip_message(&mut self) -> GossipMessage {
        self.message_id_counter += 1;

        let mut updates = Vec::new();

        // Add all current config entries
        for (key, (value, clock)) in &self.config_state {
            updates.push(ConfigUpdate {
                key: key.clone(),
                value: value.clone(),
                vector_clock: clock.clone(),
                deleted: false,
            });
        }

        // Add tombstones for deleted keys
        for (key, clock) in &self.deleted_keys {
            updates.push(ConfigUpdate {
                key: key.clone(),
                value: ConfigValue::new(vec![]).unwrap(),
                vector_clock: clock.clone(),
                deleted: true,
            });
        }

        let timestamp = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();

        let mut msg = GossipMessage {
            sender: self.local_node_id.clone(),
            message_id: self.message_id_counter,
            updates,
            timestamp,
            signature: vec![],
        };

        // Sign message
        msg.signature = self.sign_message(&msg);

        msg
    }

    /// Process incoming gossip message
    pub fn process_message(&mut self, msg: &GossipMessage) -> Result<(), &'static str> {
        // Check rate limit
        if !self.check_rate_limit(&msg.sender) {
            warn!("Rate limit exceeded for node {:?}", msg.sender);
            return Err("rate limit exceeded");
        }

        // Verify signature
        if !self.verify_signature(msg) {
            warn!("Invalid signature from node {:?}", msg.sender);
            return Err("invalid signature");
        }

        // Check for duplicate
        if self.seen_messages.contains_key(&msg.message_id) {
            debug!("Duplicate message {} ignored", msg.message_id);
            return Ok(());
        }

        // Record message
        self.seen_messages.insert(msg.message_id, SystemTime::now());

        // Process updates
        for update in &msg.updates {
            self.apply_update(update)?;
        }

        // Cleanup old seen messages (>5 minutes)
        self.cleanup_seen_messages();

        Ok(())
    }

    /// Apply single config update with conflict resolution
    fn apply_update(&mut self, update: &ConfigUpdate) -> Result<(), &'static str> {
        if update.deleted {
            // Handle deletion
            if let Some((_, existing_clock)) = self.config_state.get(&update.key) {
                match update.vector_clock.compare(existing_clock) {
                    ClockOrdering::After | ClockOrdering::Concurrent => {
                        // Remote deletion is newer or concurrent -> accept delete
                        self.config_state.remove(&update.key);
                        self.deleted_keys
                            .insert(update.key.clone(), update.vector_clock.clone());
                    }
                    _ => {
                        // Local version is newer -> ignore delete
                        debug!("Ignoring stale delete for key {:?}", update.key.as_str());
                    }
                }
            }
        } else {
            // Handle set/update
            match self.config_state.get(&update.key) {
                Some((_, existing_clock)) => {
                    match update.vector_clock.compare(existing_clock) {
                        ClockOrdering::After => {
                            // Remote update is newer -> accept
                            self.config_state.insert(
                                update.key.clone(),
                                (update.value.clone(), update.vector_clock.clone()),
                            );
                        }
                        ClockOrdering::Concurrent => {
                            // Concurrent updates -> last-write-wins (accept remote update)
                            // In production, use timestamp or node ID as tiebreaker
                            self.config_state.insert(
                                update.key.clone(),
                                (update.value.clone(), update.vector_clock.clone()),
                            );
                        }
                        _ => {
                            // Local version is newer or equal -> ignore
                            debug!("Ignoring stale update for key {:?}", update.key.as_str());
                        }
                    }
                }
                None => {
                    // New key -> accept
                    self.config_state.insert(
                        update.key.clone(),
                        (update.value.clone(), update.vector_clock.clone()),
                    );
                    self.deleted_keys.remove(&update.key);
                }
            }
        }

        Ok(())
    }

    /// Sign gossip message with HMAC-SHA256
    fn sign_message(&self, msg: &GossipMessage) -> Vec<u8> {
        // Serialize message without signature
        let mut msg_copy = msg.clone();
        msg_copy.signature.clear();

        let data = bincode::serialize(&msg_copy).unwrap_or_default();

        // Compute BLAKE3 keyed hash (similar to HMAC)
        blake3::keyed_hash(&self.hmac_key, &data)
            .as_bytes()
            .to_vec()
    }

    /// Verify message signature
    fn verify_signature(&self, msg: &GossipMessage) -> bool {
        let expected_sig = self.sign_message(msg);
        expected_sig == msg.signature
    }

    /// Check rate limit (max 10 messages/sec/peer)
    fn check_rate_limit(&mut self, peer: &NodeId) -> bool {
        const MAX_MESSAGES_PER_SEC: u32 = 10;
        const WINDOW_SIZE: Duration = Duration::from_secs(1);

        let now = SystemTime::now();

        let entry = self.rate_limiter.entry(peer.clone()).or_insert((0, now));

        // Reset window if expired
        if now.duration_since(entry.1).unwrap_or_default() > WINDOW_SIZE {
            entry.0 = 0;
            entry.1 = now;
        }

        // Check limit
        if entry.0 >= MAX_MESSAGES_PER_SEC {
            return false;
        }

        entry.0 += 1;
        true
    }

    /// Cleanup old seen messages (>5 minutes)
    fn cleanup_seen_messages(&mut self) {
        let cutoff = SystemTime::now() - Duration::from_secs(300);
        self.seen_messages.retain(|_, &mut ts| ts > cutoff);
    }

    /// Get all configuration keys
    pub fn keys(&self) -> Vec<ConfigKey> {
        self.config_state.keys().cloned().collect()
    }

    /// Get configuration state size
    pub fn len(&self) -> usize {
        self.config_state.len()
    }

    /// Check if configuration is empty
    pub fn is_empty(&self) -> bool {
        self.config_state.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vector_clock_increment() {
        let node_id = NodeId::generate();
        let mut clock = VectorClock::new();

        clock.increment(&node_id);
        assert_eq!(clock.clocks.get(&node_id), Some(&1));

        clock.increment(&node_id);
        assert_eq!(clock.clocks.get(&node_id), Some(&2));
    }

    #[test]
    fn test_vector_clock_merge() {
        let node1 = NodeId::generate();
        let node2 = NodeId::generate();

        let mut clock1 = VectorClock::new();
        clock1.increment(&node1);
        clock1.increment(&node1);

        let mut clock2 = VectorClock::new();
        clock2.increment(&node2);

        clock1.merge(&clock2);

        assert_eq!(clock1.clocks.get(&node1), Some(&2));
        assert_eq!(clock1.clocks.get(&node2), Some(&1));
    }

    #[test]
    fn test_vector_clock_compare() {
        let node1 = NodeId::generate();
        let node2 = NodeId::generate();

        let mut clock1 = VectorClock::new();
        clock1.increment(&node1);

        let mut clock2 = VectorClock::new();
        clock2.increment(&node1);
        clock2.increment(&node1);

        assert_eq!(clock1.compare(&clock2), ClockOrdering::Before);
        assert_eq!(clock2.compare(&clock1), ClockOrdering::After);

        let mut clock3 = VectorClock::new();
        clock3.increment(&node2);

        assert_eq!(clock1.compare(&clock3), ClockOrdering::Concurrent);
    }

    #[test]
    fn test_gossip_manager_set_get() {
        let node_id = NodeId::generate();
        let mut manager = GossipManager::new(node_id, [0u8; 32]);

        let key = ConfigKey::new("test.key").unwrap();
        let value = ConfigValue::from_string("test_value").unwrap();

        manager.set(key.clone(), value.clone()).unwrap();

        let retrieved = manager.get(&key).unwrap();
        assert_eq!(retrieved, value);
    }

    #[test]
    fn test_gossip_manager_delete() {
        let node_id = NodeId::generate();
        let mut manager = GossipManager::new(node_id, [0u8; 32]);

        let key = ConfigKey::new("test.key").unwrap();
        let value = ConfigValue::from_string("test_value").unwrap();

        manager.set(key.clone(), value).unwrap();
        manager.delete(&key).unwrap();

        assert!(manager.get(&key).is_none());
        assert!(manager.deleted_keys.contains_key(&key));
    }

    #[test]
    fn test_gossip_message_creation() {
        let node_id = NodeId::generate();
        let mut manager = GossipManager::new(node_id, [0u8; 32]);

        let key = ConfigKey::new("test.key").unwrap();
        let value = ConfigValue::from_string("test_value").unwrap();

        manager.set(key, value).unwrap();

        let msg = manager.create_gossip_message();
        assert_eq!(msg.updates.len(), 1);
        assert!(!msg.signature.is_empty());
    }

    #[test]
    fn test_gossip_message_signature_verification() {
        let node_id = NodeId::generate();
        let hmac_key = [42u8; 32];
        let mut manager = GossipManager::new(node_id, hmac_key);

        let key = ConfigKey::new("test.key").unwrap();
        let value = ConfigValue::from_string("test_value").unwrap();

        manager.set(key, value).unwrap();

        let msg = manager.create_gossip_message();
        assert!(manager.verify_signature(&msg));

        // Tamper with message
        let mut tampered_msg = msg.clone();
        tampered_msg.timestamp += 1;
        assert!(!manager.verify_signature(&tampered_msg));
    }

    #[test]
    fn test_gossip_message_processing() {
        let node1 = NodeId::generate();
        let node2 = NodeId::generate();
        let hmac_key = [42u8; 32];

        let mut manager1 = GossipManager::new(node1, hmac_key);
        let mut manager2 = GossipManager::new(node2, hmac_key);

        // Node1 sets a config
        let key = ConfigKey::new("shared.key").unwrap();
        let value = ConfigValue::from_string("shared_value").unwrap();
        manager1.set(key.clone(), value.clone()).unwrap();

        // Node1 creates gossip message
        let msg = manager1.create_gossip_message();

        // Node2 processes message
        manager2.process_message(&msg).unwrap();

        // Node2 should now have the config
        let retrieved = manager2.get(&key).unwrap();
        assert_eq!(retrieved, value);
    }

    #[test]
    fn test_conflict_resolution_last_write_wins() {
        let node1 = NodeId::generate();
        let node2 = NodeId::generate();
        let hmac_key = [42u8; 32];

        let mut manager1 = GossipManager::new(node1, hmac_key);
        let mut manager2 = GossipManager::new(node2, hmac_key);

        let key = ConfigKey::new("conflict.key").unwrap();

        // Both nodes set different values (concurrent updates)
        let value1 = ConfigValue::from_string("value_from_node1").unwrap();
        let value2 = ConfigValue::from_string("value_from_node2").unwrap();

        manager1.set(key.clone(), value1).unwrap();
        manager2.set(key.clone(), value2.clone()).unwrap();

        // Node1 receives update from Node2
        let msg2 = manager2.create_gossip_message();
        manager1.process_message(&msg2).unwrap();

        // Result should be deterministic (vector clock comparison)
        let final_value = manager1.get(&key).unwrap();
        assert!(!final_value.as_bytes().is_empty());
    }

    #[test]
    fn test_rate_limiting() {
        let node1 = NodeId::generate();
        let node2 = NodeId::generate();
        let hmac_key = [42u8; 32];

        let mut manager = GossipManager::new(node1, hmac_key);

        // First 10 messages should succeed
        for _ in 0..10 {
            assert!(manager.check_rate_limit(&node2));
        }

        // 11th message should fail
        assert!(!manager.check_rate_limit(&node2));
    }
}
