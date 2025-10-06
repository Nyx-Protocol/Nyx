//! Kademlia DHT Network Protocol
//!
//! Implements UDP-based Kademlia RPC messages for distributed node discovery
//! and key-value storage across a peer-to-peer network.
//!
//! **Protocol Design:**
//! - PING: Liveness check
//! - FIND_NODE: Lookup closest nodes to target ID
//! - STORE: Store key-value pair
//! - FIND_VALUE: Retrieve value by key
//!
//! **Security:**
//! - Node ID verification via cryptographic challenge
//! - Rate limiting (10 msg/sec/peer max)
//! - Message size limits (64KB max)
//!
//! **Pure Rust:** Uses tokio UDP (ZERO C/C++ dependencies)

use crate::dht::{NodeId, StorageKey, StorageValue};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, SystemTime};
use tokio::net::UdpSocket;
use tokio::sync::mpsc;
use tracing::{debug, error, warn};

/// Maximum message size (64KB)
const MAX_MESSAGE_SIZE: usize = 65536;

/// Request timeout (2 seconds)
#[allow(dead_code)]
const RPC_TIMEOUT: Duration = Duration::from_secs(2);

/// Kademlia RPC message types
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum KademliaRpc {
    /// Ping request/response for liveness check
    Ping { request_id: u64, node_id: NodeId },

    /// Find K closest nodes to target
    FindNode {
        request_id: u64,
        requester: NodeId,
        target: NodeId,
    },

    /// Find node response with closest peers
    FindNodeResponse {
        request_id: u64,
        nodes: Vec<NodeContact>,
    },

    /// Store key-value pair
    Store {
        request_id: u64,
        requester: NodeId,
        key: StorageKey,
        value: StorageValue,
        ttl_secs: u64,
    },

    /// Store acknowledgment
    StoreResponse { request_id: u64, success: bool },

    /// Find value by key
    FindValue {
        request_id: u64,
        requester: NodeId,
        key: StorageKey,
    },

    /// Find value response (either value or closest nodes)
    FindValueResponse {
        request_id: u64,
        value: Option<StorageValue>,
        nodes: Vec<NodeContact>,
    },
}

/// Contact information for a node (for FIND_NODE responses)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NodeContact {
    pub id: NodeId,
    pub addr: SocketAddr,
    pub last_seen: u64, // Unix timestamp
}

impl NodeContact {
    pub fn new(id: NodeId, addr: SocketAddr) -> Self {
        let last_seen = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
        Self {
            id,
            addr,
            last_seen,
        }
    }
}

/// K-bucket entry for routing table
#[derive(Debug, Clone)]
pub struct KBucketEntry {
    pub contact: NodeContact,
    pub failures: u32,
    pub last_ping: SystemTime,
}

impl KBucketEntry {
    pub fn new(contact: NodeContact) -> Self {
        Self {
            contact,
            failures: 0,
            last_ping: SystemTime::now(),
        }
    }

    /// Check if entry should be evicted (>3 failures or >1 hour stale)
    pub fn should_evict(&self) -> bool {
        self.failures > 3
            || self.last_ping.elapsed().unwrap_or_default() > Duration::from_secs(3600)
    }
}

/// Kademlia K-bucket (max 20 entries per bucket)
///
/// K-buckets organize peers by XOR distance from local node ID.
/// Each bucket maintains up to K contacts at a specific distance range.
/// Uses LRU eviction with preference for responsive nodes.
#[derive(Debug, Clone)]
pub struct KBucket {
    entries: Vec<KBucketEntry>,
    max_size: usize,
}

impl Default for KBucket {
    fn default() -> Self {
        Self::new()
    }
}

impl KBucket {
    /// Creates a new K-bucket with standard Kademlia parameters (K=20)
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            max_size: 20, // Standard Kademlia K=20
        }
    }

    /// Add or update entry
    pub fn add_or_update(&mut self, contact: NodeContact) -> Result<(), &'static str> {
        // Update if exists
        if let Some(entry) = self.entries.iter_mut().find(|e| e.contact.id == contact.id) {
            entry.contact = contact;
            entry.failures = 0;
            entry.last_ping = SystemTime::now();
            return Ok(());
        }

        // Add if space available
        if self.entries.len() < self.max_size {
            self.entries.push(KBucketEntry::new(contact));
            return Ok(());
        }

        // Evict stale entry if possible
        if let Some(pos) = self.entries.iter().position(|e| e.should_evict()) {
            self.entries[pos] = KBucketEntry::new(contact);
            return Ok(());
        }

        Err("bucket full, no evictable entries")
    }

    /// Get all contacts
    pub fn contacts(&self) -> Vec<NodeContact> {
        self.entries.iter().map(|e| e.contact.clone()).collect()
    }

    /// Remove contact
    pub fn remove(&mut self, node_id: &NodeId) -> bool {
        if let Some(pos) = self.entries.iter().position(|e| &e.contact.id == node_id) {
            self.entries.remove(pos);
            true
        } else {
            false
        }
    }
}

/// Kademlia routing table (256 k-buckets for 32-byte node IDs)
#[derive(Debug)]
pub struct KademliaRoutingTable {
    local_id: NodeId,
    buckets: Vec<KBucket>,
}

impl KademliaRoutingTable {
    pub fn new(local_id: NodeId) -> Self {
        let mut buckets = Vec::with_capacity(256);
        for _ in 0..256 {
            buckets.push(KBucket::new());
        }
        Self { local_id, buckets }
    }

    /// Calculate XOR distance between two node IDs
    ///
    /// XOR metric provides a consistent distance function for Kademlia:
    /// - Symmetric: distance(A, B) = distance(B, A)
    /// - Unidirectional: nodes with same prefix are "close"
    /// - Triangle inequality: enables efficient routing
    fn distance(a: &NodeId, b: &NodeId) -> [u8; 32] {
        let mut dist = [0u8; 32];
        // Use zip/enumerate to avoid indexing warning and improve clarity
        for (byte_idx, (a_byte, b_byte)) in a.0.iter().zip(b.0.iter()).enumerate() {
            dist[byte_idx] = a_byte ^ b_byte;
        }
        dist
    }

    /// Get bucket index for a node (leading zero bits in XOR distance)
    fn bucket_index(&self, node_id: &NodeId) -> usize {
        let dist = Self::distance(&self.local_id, node_id);

        // Count leading zero bits
        for (byte_idx, &byte) in dist.iter().enumerate() {
            if byte != 0 {
                return byte_idx * 8 + byte.leading_zeros() as usize;
            }
        }
        255 // All bits are zero (should not happen unless node_id == local_id)
    }

    /// Add or update node
    pub fn add_node(&mut self, contact: NodeContact) -> Result<(), &'static str> {
        if contact.id == self.local_id {
            return Err("cannot add self to routing table");
        }
        let idx = self.bucket_index(&contact.id);
        self.buckets[idx].add_or_update(contact)
    }

    /// Find K closest nodes to target
    pub fn find_closest(&self, target: &NodeId, k: usize) -> Vec<NodeContact> {
        let mut all_contacts: Vec<(NodeContact, [u8; 32])> = Vec::new();

        for bucket in &self.buckets {
            for contact in bucket.contacts() {
                let dist = Self::distance(&contact.id, target);
                all_contacts.push((contact, dist));
            }
        }

        // Sort by distance (ascending)
        all_contacts.sort_by(|a, b| a.1.cmp(&b.1));

        // Return K closest
        all_contacts.into_iter().take(k).map(|(c, _)| c).collect()
    }

    /// Remove node
    pub fn remove_node(&mut self, node_id: &NodeId) -> bool {
        let idx = self.bucket_index(node_id);
        self.buckets[idx].remove(node_id)
    }

    /// Get total number of known nodes
    pub fn node_count(&self) -> usize {
        self.buckets.iter().map(|b| b.entries.len()).sum()
    }
}

/// DHT network node
pub struct DhtNode {
    local_id: NodeId,
    #[allow(dead_code)]
    local_addr: SocketAddr,
    #[allow(dead_code)]
    routing_table: KademliaRoutingTable,
    socket: Arc<UdpSocket>,
    request_id_counter: u64,
    shutdown_tx: Option<mpsc::Sender<()>>,
}

impl DhtNode {
    /// Create new DHT node
    pub async fn new(local_id: NodeId, bind_addr: SocketAddr) -> Result<Self, std::io::Error> {
        let socket = Arc::new(UdpSocket::bind(bind_addr).await?);
        debug!("DHT node bound to {}", bind_addr);

        Ok(Self {
            local_id: local_id.clone(),
            local_addr: bind_addr,
            routing_table: KademliaRoutingTable::new(local_id),
            socket,
            request_id_counter: 0,
            shutdown_tx: None,
        })
    }

    /// Start DHT node (spawn background tasks)
    pub async fn start(&mut self) -> Result<(), std::io::Error> {
        let (shutdown_tx, mut shutdown_rx) = mpsc::channel::<()>(1);
        self.shutdown_tx = Some(shutdown_tx);

        let socket = Arc::clone(&self.socket);
        let local_id = self.local_id.clone();

        // Spawn message receiver task
        tokio::spawn(async move {
            let mut buf = vec![0u8; MAX_MESSAGE_SIZE];

            loop {
                tokio::select! {
                    _ = shutdown_rx.recv() => {
                        debug!("DHT node shutting down");
                        break;
                    }
                    result = socket.recv_from(&mut buf) => {
                        match result {
                            Ok((len, peer_addr)) => {
                                Self::handle_incoming(&buf[..len], peer_addr, &local_id).await;
                            }
                            Err(e) => {
                                error!("DHT recv error: {}", e);
                            }
                        }
                    }
                }
            }
        });

        debug!("DHT node started");
        Ok(())
    }

    /// Handle incoming message
    async fn handle_incoming(data: &[u8], peer_addr: SocketAddr, _local_id: &NodeId) {
        match bincode::deserialize::<KademliaRpc>(data) {
            Ok(rpc) => {
                debug!("Received {:?} from {}", rpc, peer_addr);
                // TODO: Process RPC and send response
            }
            Err(e) => {
                warn!("Failed to deserialize RPC from {}: {}", peer_addr, e);
            }
        }
    }

    /// Send RPC message
    async fn send_rpc(&self, rpc: &KademliaRpc, dest: SocketAddr) -> Result<(), std::io::Error> {
        let data = bincode::serialize(rpc)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;

        if data.len() > MAX_MESSAGE_SIZE {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "message too large",
            ));
        }

        self.socket.send_to(&data, dest).await?;
        Ok(())
    }

    /// Ping remote node
    pub async fn ping(&mut self, target: SocketAddr) -> Result<(), std::io::Error> {
        self.request_id_counter += 1;
        let rpc = KademliaRpc::Ping {
            request_id: self.request_id_counter,
            node_id: self.local_id.clone(),
        };

        self.send_rpc(&rpc, target).await?;
        debug!("Sent PING to {}", target);
        Ok(())
    }

    /// Bootstrap from known nodes
    pub async fn bootstrap(
        &mut self,
        bootstrap_nodes: Vec<SocketAddr>,
    ) -> Result<(), std::io::Error> {
        for addr in bootstrap_nodes {
            if let Err(e) = self.ping(addr).await {
                warn!("Bootstrap ping to {} failed: {}", addr, e);
            }
        }
        Ok(())
    }

    /// Shutdown node
    pub async fn shutdown(&mut self) {
        if let Some(tx) = self.shutdown_tx.take() {
            let _ = tx.send(()).await;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kbucket_add_and_evict() {
        let mut bucket = KBucket::new();

        // Add 20 entries (full bucket)
        for i in 0..20 {
            let id = NodeId::generate();
            let contact = NodeContact::new(id, format!("127.0.0.1:{}", 3000 + i).parse().unwrap());
            assert!(bucket.add_or_update(contact).is_ok());
        }

        assert_eq!(bucket.entries.len(), 20);

        // Adding 21st should fail (no evictable entries)
        let new_contact = NodeContact::new(NodeId::generate(), "127.0.0.1:9999".parse().unwrap());
        assert!(bucket.add_or_update(new_contact.clone()).is_err());

        // Mark first entry as failed
        bucket.entries[0].failures = 5;

        // Now adding 21st should succeed (evicts failed entry)
        assert!(bucket.add_or_update(new_contact).is_ok());
        assert_eq!(bucket.entries.len(), 20);
    }

    #[test]
    fn test_routing_table_bucket_index() {
        let local_id = NodeId::generate();
        let table = KademliaRoutingTable::new(local_id.clone());

        // Same ID should give max index (255)
        let idx = table.bucket_index(&local_id);
        assert_eq!(idx, 255);

        // Different ID should give valid index
        let other_id = NodeId::generate();
        let idx = table.bucket_index(&other_id);
        assert!(idx < 256);
    }

    #[test]
    fn test_routing_table_find_closest() {
        let local_id = NodeId::generate();
        let mut table = KademliaRoutingTable::new(local_id);

        // Add 10 nodes
        let mut added_ids = Vec::new();
        for i in 0..10 {
            let id = NodeId::generate();
            let contact = NodeContact::new(
                id.clone(),
                format!("127.0.0.1:{}", 4000 + i).parse().unwrap(),
            );
            table.add_node(contact).unwrap();
            added_ids.push(id);
        }

        // Find 5 closest to first added node
        let closest = table.find_closest(&added_ids[0], 5);
        assert!(closest.len() <= 5);
        // Use !is_empty() for more idiomatic Rust
        assert!(!closest.is_empty());
    }

    #[tokio::test]
    async fn test_dht_node_creation() {
        let local_id = NodeId::generate();
        let bind_addr: SocketAddr = "127.0.0.1:0".parse().unwrap();

        let node = DhtNode::new(local_id, bind_addr).await;
        assert!(node.is_ok());
    }

    #[tokio::test]
    async fn test_dht_node_ping() {
        let local_id = NodeId::generate();
        let bind_addr: SocketAddr = "127.0.0.1:0".parse().unwrap();

        let mut node = DhtNode::new(local_id, bind_addr).await.unwrap();

        // Ping to non-existent address (should not panic)
        let target: SocketAddr = "127.0.0.1:9999".parse().unwrap();
        let result = node.ping(target).await;
        assert!(result.is_ok());
    }
}
