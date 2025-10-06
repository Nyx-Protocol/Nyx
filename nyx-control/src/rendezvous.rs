use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, SystemTime};
use tokio::net::UdpSocket;
use tokio::sync::RwLock;
use tokio::time::{interval, sleep};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Registration {
    pub _node_id: String,
    pub __public_addr: String,
    pub __private_addr: String,
    pub __timestamp: i64,
}

/// Rendezvous RPC message types
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RendezvousRpc {
    Register { signed_registration: Vec<u8> },
    RegisterResponse { success: bool, message: String },
    QueryPeers { max_peers: usize },
    QueryPeersResponse { peers: Vec<PeerInfo> },
}

/// Peer information stored in registry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PeerInfo {
    pub node_id: String,
    pub public_addr: String,
    pub private_addr: String,
    pub last_seen: u64, // Unix timestamp
}

#[derive(thiserror::Error, Debug)]
pub enum RvError {
    #[error("sign: {0}")]
    Sign(String),
    #[error("verify failed")]
    Verify,
}

pub type Result<T> = std::result::Result<T, RvError>;

/// Sign registration payload using Ed25519.
pub fn sign_registration(sk: &SigningKey, reg: &Registration) -> Result<Vec<u8>> {
    let __msg = serde_json::to_vec(reg).map_err(|e| RvError::Sign(e.to_string()))?;
    let sig: Signature = sk.sign(&__msg);
    let mut out = Vec::with_capacity(32 + 64 + __msg.len());
    out.extend_from_slice(sk.verifying_key().as_bytes());
    out.extend_from_slice(&sig.to_bytes());
    out.extend_from_slice(&__msg);
    Ok(out)
}

/// Verify signed registration, returning payload if valid.
pub fn verify_registration(signed: &[u8]) -> Result<Registration> {
    if signed.len() < 96 {
        return Err(RvError::Verify);
    }
    let mut pk_byte_s = [0u8; 32];
    pk_byte_s.copy_from_slice(&signed[..32]);
    let __pk = VerifyingKey::from_bytes(&pk_byte_s).map_err(|_| RvError::Verify)?;
    let mut sig_byte_s = [0u8; 64];
    sig_byte_s.copy_from_slice(&signed[32..96]);
    let __sig = Signature::from_bytes(&sig_byte_s);
    let __msg = &signed[96..];
    __pk.verify_strict(__msg, &__sig)
        .map_err(|_| RvError::Verify)?;
    serde_json::from_slice(__msg).map_err(|_| RvError::Verify)
}

/// Rendezvous service for peer discovery and registration
pub struct RendezvousService {
    local_addr: SocketAddr,
    socket: Arc<UdpSocket>,
    peer_registry: Arc<RwLock<HashMap<String, PeerInfo>>>,
    gossip_manager: Option<Arc<RwLock<crate::gossip::GossipManager>>>,
}

impl RendezvousService {
    /// Create new RendezvousService bound to specified address
    pub async fn new(addr: SocketAddr) -> std::io::Result<Self> {
        let socket = UdpSocket::bind(addr).await?;
        let local_addr = socket.local_addr()?;

        Ok(Self {
            local_addr,
            socket: Arc::new(socket),
            peer_registry: Arc::new(RwLock::new(HashMap::new())),
            gossip_manager: None,
        })
    }

    /// Set gossip manager for periodic config propagation
    pub fn set_gossip_manager(
        &mut self,
        gossip_manager: Arc<RwLock<crate::gossip::GossipManager>>,
    ) {
        self.gossip_manager = Some(gossip_manager);
    }

    /// Get local bound address
    pub fn local_addr(&self) -> SocketAddr {
        self.local_addr
    }

    /// Start rendezvous service (message handling + gossip rounds)
    pub async fn start(self: Arc<Self>) {
        // Spawn message handler
        let handler_service = Arc::clone(&self);
        tokio::spawn(async move {
            handler_service.handle_messages().await;
        });

        // Spawn periodic gossip task if gossip_manager is configured
        if self.gossip_manager.is_some() {
            let gossip_service = Arc::clone(&self);
            tokio::spawn(async move {
                gossip_service.periodic_gossip_rounds().await;
            });
        }
    }

    /// Handle incoming UDP messages
    async fn handle_messages(&self) {
        let mut buf = vec![0u8; 65536];
        loop {
            match self.socket.recv_from(&mut buf).await {
                Ok((len, peer_addr)) => {
                    let data = &buf[..len];
                    if let Err(e) = self.process_message(data, peer_addr).await {
                        eprintln!("Failed to process message from {}: {:?}", peer_addr, e);
                    }
                }
                Err(e) => {
                    eprintln!("UDP recv error: {:?}", e);
                    sleep(Duration::from_millis(100)).await;
                }
            }
        }
    }

    /// Process a single RPC message
    async fn process_message(&self, data: &[u8], peer_addr: SocketAddr) -> std::io::Result<()> {
        let rpc: RendezvousRpc = bincode::deserialize(data)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;

        let response = match rpc {
            RendezvousRpc::Register {
                signed_registration,
            } => self.handle_register(&signed_registration).await,
            RendezvousRpc::QueryPeers { max_peers } => self.handle_query_peers(max_peers).await,
            _ => {
                // Ignore response messages
                return Ok(());
            }
        };

        // Send response
        let response_bytes = bincode::serialize(&response)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        self.socket.send_to(&response_bytes, peer_addr).await?;

        Ok(())
    }

    /// Handle peer registration
    async fn handle_register(&self, signed_registration: &[u8]) -> RendezvousRpc {
        match verify_registration(signed_registration) {
            Ok(reg) => {
                let peer_info = PeerInfo {
                    node_id: reg._node_id.clone(),
                    public_addr: reg.__public_addr,
                    private_addr: reg.__private_addr,
                    last_seen: SystemTime::now()
                        .duration_since(SystemTime::UNIX_EPOCH)
                        .unwrap_or_default()
                        .as_secs(),
                };

                let mut registry = self.peer_registry.write().await;
                registry.insert(reg._node_id, peer_info);

                RendezvousRpc::RegisterResponse {
                    success: true,
                    message: "Registration successful".to_string(),
                }
            }
            Err(e) => RendezvousRpc::RegisterResponse {
                success: false,
                message: format!("Registration failed: {:?}", e),
            },
        }
    }

    /// Handle peer query (returns up to max_peers random peers)
    async fn handle_query_peers(&self, max_peers: usize) -> RendezvousRpc {
        let registry = self.peer_registry.read().await;
        let mut peers: Vec<PeerInfo> = registry.values().cloned().collect();

        // Shuffle and truncate to max_peers using Send-safe RNG
        use rand::rngs::StdRng;
        use rand::seq::SliceRandom;
        use rand::SeedableRng;
        let seed = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
        let mut rng = StdRng::seed_from_u64(seed);
        peers.shuffle(&mut rng);
        peers.truncate(max_peers);

        RendezvousRpc::QueryPeersResponse { peers }
    }

    /// Periodic gossip rounds (every 5 seconds)
    async fn periodic_gossip_rounds(&self) {
        let mut ticker = interval(Duration::from_secs(5));
        loop {
            ticker.tick().await;

            if let Some(gossip_mgr) = &self.gossip_manager {
                // Get random K peers (K=3 for gossip fanout)
                let peer_addrs: Vec<SocketAddr> = {
                    let registry = self.peer_registry.read().await;
                    let mut peers: Vec<&PeerInfo> = registry.values().collect();

                    // Shuffle peers using Send-safe RNG
                    use rand::rngs::StdRng;
                    use rand::seq::SliceRandom;
                    use rand::SeedableRng;
                    let seed = SystemTime::now()
                        .duration_since(SystemTime::UNIX_EPOCH)
                        .unwrap_or_default()
                        .as_secs();
                    let mut rng = StdRng::seed_from_u64(seed);
                    peers.shuffle(&mut rng);
                    peers.truncate(3);

                    // Parse addresses before releasing lock
                    peers
                        .iter()
                        .filter_map(|p| p.public_addr.parse::<SocketAddr>().ok())
                        .collect()
                };

                // Create gossip message (needs write lock for message_id increment)
                let gossip_msg = {
                    let mut mgr = gossip_mgr.write().await;
                    mgr.create_gossip_message()
                };

                // Send to selected peers
                let msg_bytes = bincode::serialize(&gossip_msg).unwrap_or_default();
                for peer_addr in peer_addrs {
                    let _ = self.socket.send_to(&msg_bytes, peer_addr).await;
                }
            }
        }
    }

    /// Register this node with a remote rendezvous service
    pub async fn register_with(
        &self,
        remote_addr: SocketAddr,
        signing_key: &SigningKey,
        node_id: String,
        public_addr: String,
        private_addr: String,
    ) -> std::io::Result<bool> {
        let reg = Registration {
            _node_id: node_id,
            __public_addr: public_addr,
            __private_addr: private_addr,
            __timestamp: SystemTime::now()
                .duration_since(SystemTime::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64,
        };

        let signed_registration = sign_registration(signing_key, &reg)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;

        let rpc = RendezvousRpc::Register {
            signed_registration,
        };
        let request_bytes = bincode::serialize(&rpc)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;

        // Send request
        self.socket.send_to(&request_bytes, remote_addr).await?;

        // Wait for response (with 5s timeout)
        let mut buf = vec![0u8; 65536];
        match tokio::time::timeout(Duration::from_secs(5), self.socket.recv_from(&mut buf)).await {
            Ok(Ok((len, _))) => {
                let response: RendezvousRpc = bincode::deserialize(&buf[..len])
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;

                if let RendezvousRpc::RegisterResponse { success, .. } = response {
                    Ok(success)
                } else {
                    Ok(false)
                }
            }
            _ => Err(std::io::Error::new(
                std::io::ErrorKind::TimedOut,
                "Registration timeout",
            )),
        }
    }

    /// Query peers from a remote rendezvous service
    pub async fn query_peers(
        &self,
        remote_addr: SocketAddr,
        max_peers: usize,
    ) -> std::io::Result<Vec<PeerInfo>> {
        let rpc = RendezvousRpc::QueryPeers { max_peers };
        let request_bytes = bincode::serialize(&rpc)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;

        // Send request
        self.socket.send_to(&request_bytes, remote_addr).await?;

        // Wait for response (with 5s timeout)
        let mut buf = vec![0u8; 65536];
        match tokio::time::timeout(Duration::from_secs(5), self.socket.recv_from(&mut buf)).await {
            Ok(Ok((len, _))) => {
                let response: RendezvousRpc = bincode::deserialize(&buf[..len])
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;

                if let RendezvousRpc::QueryPeersResponse { peers } = response {
                    Ok(peers)
                } else {
                    Ok(vec![])
                }
            }
            _ => Err(std::io::Error::new(
                std::io::ErrorKind::TimedOut,
                "Query peers timeout",
            )),
        }
    }
}

#[cfg(test)]
mod test_s {
    use super::*;
    use rand::rngs::OsRng;

    #[test]
    fn sign_and_verify() -> super::Result<()> {
        let __sk = SigningKey::generate(&mut OsRng);
        let __reg = Registration {
            _node_id: "n1".into(),
            __public_addr: "1.2.3.4:5".into(),
            __private_addr: "10.0.0.1:5".into(),
            __timestamp: 12345,
        };
        let __s = sign_registration(&__sk, &__reg)?;
        let __out = verify_registration(&__s)?;
        assert_eq!(__out, __reg);
        Ok(())
    }

    #[tokio::test]
    async fn test_rendezvous_service_creation() {
        let addr = "127.0.0.1:0".parse().unwrap();
        let service = RendezvousService::new(addr).await;
        assert!(service.is_ok());
    }

    #[tokio::test]
    async fn test_peer_registration() {
        // Create rendezvous service
        let service = Arc::new(
            RendezvousService::new("127.0.0.1:0".parse().unwrap())
                .await
                .unwrap(),
        );
        let service_addr = service.local_addr();

        // Start service in background
        let service_clone = Arc::clone(&service);
        tokio::spawn(async move {
            service_clone.start().await;
        });

        // Give service time to start
        tokio::time::sleep(Duration::from_millis(100)).await;

        // Create client to register with service
        let client = RendezvousService::new("127.0.0.1:0".parse().unwrap())
            .await
            .unwrap();
        let sk = SigningKey::generate(&mut OsRng);

        let success = client
            .register_with(
                service_addr,
                &sk,
                "node1".to_string(),
                "192.168.1.1:8080".to_string(),
                "10.0.0.1:8080".to_string(),
            )
            .await;

        assert!(success.is_ok());
        assert!(success.unwrap());

        // Verify peer is in registry
        let registry = service.peer_registry.read().await;
        assert!(registry.contains_key("node1"));
    }

    #[tokio::test]
    async fn test_peer_query() {
        // Create rendezvous service and register 3 peers
        let service = Arc::new(
            RendezvousService::new("127.0.0.1:0".parse().unwrap())
                .await
                .unwrap(),
        );
        let service_addr = service.local_addr();

        let service_clone = Arc::clone(&service);
        tokio::spawn(async move {
            service_clone.start().await;
        });

        tokio::time::sleep(Duration::from_millis(100)).await;

        // Register 3 peers
        for i in 1..=3 {
            let client = RendezvousService::new("127.0.0.1:0".parse().unwrap())
                .await
                .unwrap();
            let sk = SigningKey::generate(&mut OsRng);
            let _ = client
                .register_with(
                    service_addr,
                    &sk,
                    format!("node{}", i),
                    format!("192.168.1.{}:8080", i),
                    format!("10.0.0.{}:8080", i),
                )
                .await;
        }

        tokio::time::sleep(Duration::from_millis(100)).await;

        // Query peers
        let client = RendezvousService::new("127.0.0.1:0".parse().unwrap())
            .await
            .unwrap();
        let peers = client.query_peers(service_addr, 2).await;

        assert!(peers.is_ok());
        let peer_list = peers.unwrap();
        assert_eq!(peer_list.len(), 2); // Should return max 2 peers
    }
}
