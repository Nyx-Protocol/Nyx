# NyxNet システムアーキテクチャ設計ドキュメント

**最終更新**: 2025年10月6日  
**対象バージョン**: v1.0

---

## 概要

NyxNetは、レイヤードアーキテクチャに基づく分散型プライバシーネットワークスタックです。各レイヤーは明確な責務を持ち、下位レイヤーに依存せず独立してテスト可能です。

---

## アーキテクチャ図（テキスト表現）

```
┌─────────────────────────────────────────────────────────────┐
│                    Application Layer                         │
│  (User Apps, Browser Extensions, Mobile Apps)                │
└────────────────┬────────────────────────────────────────────┘
                 │
                 ▼
┌─────────────────────────────────────────────────────────────┐
│                   SDK Layer (nyx-sdk)                        │
│  - Stream API                                                │
│  - Daemon Client (gRPC/JSON-RPC)                             │
│  - Reconnection & Error Handling                             │
└────────────────┬────────────────────────────────────────────┘
                 │
                 ▼
┌─────────────────────────────────────────────────────────────┐
│              Control Plane (nyx-daemon)                      │
│  - gRPC Service (20+ RPCs)                                   │
│  - JSON-RPC 2.0 (IPC: Unix socket / Named pipe)             │
│  - Configuration Management                                  │
│  - Node Lifecycle Management                                 │
└────────┬────────┬────────┬────────┬────────┬────────────────┘
         │        │        │        │        │
         ▼        ▼        ▼        ▼        ▼
┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌───────────┐
│ Stream  │ │   Mix   │ │Transport│ │  Crypto │ │Telemetry  │
│ Manager │ │ Network │ │  Layer  │ │  Layer  │ │  Layer    │
│(nyx-    │ │(nyx-mix)│ │(nyx-    │ │(nyx-    │ │(nyx-      │
│stream)  │ │         │ │transport│ │crypto)  │ │telemetry) │
└────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘ └─────┬─────┘
     │           │           │           │            │
     └───────────┴───────────┴───────────┴────────────┘
                         │
                         ▼
            ┌──────────────────────────┐
            │   Core Utilities         │
            │   (nyx-core)             │
            │  - Types                 │
            │  - Config                │
            │  - Error Handling        │
            └──────────────────────────┘

External Services:
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│ Prometheus  │◄────┤ OpenTelemetry├────►│   Jaeger    │
│  Metrics    │     │   Collector  │     │  Tracing    │
└─────────────┘     └─────────────┘     └─────────────┘
```

---

## 主要コンポーネントと責務

### 1. アプリケーション層

**責務**: エンドユーザーインターフェース

**コンポーネント**:
- Webブラウザ（SOCKS5/HTTP CONNECTプロキシ経由）
- モバイルアプリ（nyx-mobile-ffi使用）
- デスクトップアプリ（nyx-sdk使用）
- CLIツール（nyx-cli）

**インターフェース**:
- SOCKS5プロトコル（RFC 1928）: `localhost:9050`
- HTTP CONNECTプロキシ: `localhost:8080`
- gRPC API（nyx-sdk経由）: `localhost:50051`
- JSON-RPC 2.0（IPC）: Unix socket `/tmp/nyx-daemon.sock` または Named pipe `\\.\pipe\nyx-daemon`

---

### 2. SDK層（nyx-sdk）

**責務**: アプリケーション開発者向けの高レベルAPI提供

**主要モジュール**:

#### DaemonClient (`src/client.rs`)
```rust
pub struct DaemonClient {
    endpoint: String,
    channel: Channel, // tonic gRPC channel
    reconnect: bool,
}

// 主要メソッド
impl DaemonClient {
    pub async fn connect(endpoint: &str) -> Result<Self>
    pub async fn get_node_info(&self) -> Result<NodeInfo>
    pub async fn open_stream(&self, peer_id: &str) -> Result<StreamHandle>
    pub async fn close_stream(&self, stream_id: StreamId) -> Result<()>
}
```

#### StreamHandle (`src/stream.rs`)
```rust
pub struct StreamHandle {
    stream_id: StreamId,
    tx: mpsc::Sender<Bytes>,
    rx: mpsc::Receiver<Bytes>,
}

impl StreamHandle {
    pub async fn send(&self, data: Bytes) -> Result<()>
    pub async fn recv(&self) -> Result<Option<Bytes>>
}
```

**依存関係**:
- `nyx-core`: 型定義
- `tonic`: gRPCクライアント（Pure Rust、TLSなし）
- `tokio`: 非同期ランタイム

**設計パターン**:
- **Builder Pattern**: クライアント設定
- **Factory Pattern**: ストリーム作成
- **Observer Pattern**: イベント通知

---

### 3. 制御プレーン（nyx-daemon）

**責務**: システム全体の調整、API提供、ライフサイクル管理

**主要構造体**:

```rust
struct DaemonState {
    config: Arc<RwLock<Config>>,
    streams: Arc<DashMap<StreamId, StreamState>>,
    peers: Arc<DashMap<PeerId, PeerInfo>>,
    mix_manager: Arc<MixManager>,
    transport: Arc<UdpTransport>,
    telemetry: Arc<TelemetryExporter>,
}
```

**API仕様**:

#### gRPC Service (Pure Rust、TLSなし)
```protobuf
service NyxControl {
  rpc GetNodeInfo(Empty) returns (NodeInfoResponse);
  rpc OpenStream(OpenStreamRequest) returns (StreamResponse);
  rpc CloseStream(CloseStreamRequest) returns (Empty);
  rpc ListStreams(Empty) returns (StreamListResponse);
  rpc GetMetrics(Empty) returns (MetricsResponse);
  // ... 計20+ RPCs
}
```

#### JSON-RPC 2.0 (IPC経由)
```json
// Request
{
  "jsonrpc": "2.0",
  "id": "req-123",
  "method": "get_info",
  "params": {}
}

// Response
{
  "jsonrpc": "2.0",
  "id": "req-123",
  "result": {
    "node_id": "12D3KooW...",
    "version": "1.0.0",
    "capabilities": ["multipath", "hybrid_pq", "low_power"]
  }
}
```

**設計選択**:
- gRPC（Rust SDK向け）とJSON-RPC（Go proxy、外部ツール向け）の両対応
- Pure Rust実装（ring/OpenSSL依存なし）でクロスプラットフォーム互換性確保
- 状態管理に`DashMap`使用（ロックフリー並行HashMap）

---

### 4. ストリーム層（nyx-stream）

**責務**: ストリームライフサイクル管理、フレーム処理

**フレーム定義**:

```rust
pub enum FrameType {
    Data = 0x00,        // データフレーム
    Control = 0x01,     // 制御フレーム
    Crypto = 0x02,      // 暗号化ハンドシェイク
    Settings = 0x03,    // 設定交換
    Ping = 0x04,        // キープアライブ
    Pong = 0x05,        // Pingレスポンス
    Close = 0x06,       // ストリームクローズ
    Plugin = 0x50,      // プラグインフレーム（0x50-0x5F予約）
}

pub struct Frame {
    connection_id: ConnectionId,  // 12バイト
    frame_type: u8,               // 1バイト（上位2bit=type、下位6bit=flags）
    path_id: u8,                  // 1バイト（マルチパス用）
    length: u16,                  // 2バイト（ペイロード長）
    payload: Vec<u8>,             // 可変長
}
```

**ストリーム状態機械**:

```
     [IDLE]
        │
        │ open_stream()
        ▼
   [HANDSHAKE]
        │
        │ crypto_complete()
        ▼
   [ESTABLISHED]
        │
        │ send/recv data
        ▼
   [ACTIVE]
        │
        │ close() or timeout
        ▼
    [CLOSING]
        │
        │ flush buffers
        ▼
    [CLOSED]
```

**プラグインフレームワーク**:

```rust
pub trait Plugin: Send + Sync {
    fn id(&self) -> u32;
    fn handle_frame(&self, frame: &PluginFrame) -> Result<Vec<u8>>;
    fn capabilities(&self) -> Vec<String>;
}

pub struct PluginFrame {
    plugin_id: u32,
    flags: u8,
    data: Vec<u8>,
}
```

---

### 5. ミックスネットワーク層（nyx-mix）

**責務**: 匿名性保証、トラフィック分析耐性

#### Sphinxオニオンルーティング

**暗号化フロー**:

```
送信者 → [Hop1暗号化] → [Hop2暗号化] → [Hop3暗号化] → 送信

Hop1受信:
  Decrypt Layer1 → 得た情報: Next=Hop2, Payload
  Forward to Hop2

Hop2受信:
  Decrypt Layer2 → 得た情報: Next=Hop3, Payload
  Forward to Hop3

Hop3受信（Exit Node）:
  Decrypt Layer3 → 得た情報: Destination, Plaintext
  Forward to destination
```

**実装**:

```rust
pub struct SphinxPacket {
    header: SphinxHeader,      // ルーティングヘッダ
    payload: Vec<u8>,          // ペイロード（最大512バイト）
}

pub struct SphinxHeader {
    version: u8,
    public_keys: Vec<[u8; 32]>,  // 各ホップの公開鍵
    routing_info: Vec<u8>,        // ルーティング情報（暗号化済み）
    mac: [u8; 16],                // HMAC-SHA256
}

impl SphinxPacket {
    pub fn encrypt(
        payload: &[u8],
        route: &[NodeId],
        keys: &[PublicKey],
    ) -> Result<Self>;
    
    pub fn decrypt(&self, private_key: &PrivateKey) -> Result<(NodeId, Vec<u8>)>;
}
```

#### カバートラフィック生成

**アルゴリズム**: Poissonプロセスに基づく適応的レート制御

```rust
pub struct CoverTrafficGenerator {
    base_lambda: f32,           // 基本レート（packets/sec）
    current_utilization: f32,   // 現在のネットワーク利用率
    low_power_mode: bool,       // Low Powerモード
}

impl CoverTrafficGenerator {
    // 効果的レート = base_lambda × (1 + utilization)
    // Low Power時は 0.4x に削減
    fn effective_rate(&self) -> f32 {
        let ratio = if self.low_power_mode { 0.4 } else { 1.0 };
        self.base_lambda * ratio * (1.0 + self.current_utilization)
    }
}
```

**設定例**:
```toml
[mix]
mode = "default"
base_cover_lambda = 5.0  # 5 packets/sec基本レート
low_power_ratio = 0.4    # Low Power時は60%削減
```

---

### 6. トランスポート層（nyx-transport）

**責務**: パケット送受信、NAT Traversal、マルチパスルーティング

#### Pure Rust UDPトランスポート

```rust
pub struct UdpTransport {
    socket: UdpSocket,           // tokio::net::UdpSocket
    local_addr: SocketAddr,
    peers: Arc<DashMap<PeerId, PeerState>>,
}

impl UdpTransport {
    pub async fn send_to(&self, data: &[u8], addr: SocketAddr) -> Result<usize>;
    pub async fn recv_from(&self, buf: &mut [u8]) -> Result<(usize, SocketAddr)>;
}
```

#### NAT Traversal（ICE Lite）

**STUNバインディングリクエスト**:

```
Client → STUN Server: BINDING REQUEST
STUN Server → Client: BINDING RESPONSE
  - XOR-MAPPED-ADDRESS: public IP + port
  - SOFTWARE: "nyx-transport/1.0"
```

**実装**:

```rust
pub struct StunClient {
    server_addr: SocketAddr,
    transaction_id: [u8; 12],
}

impl StunClient {
    pub async fn get_mapped_address(&self) -> Result<SocketAddr> {
        let request = StunMessage::binding_request(self.transaction_id);
        // Send UDP packet...
        let response = self.recv_response().await?;
        response.extract_xor_mapped_address()
    }
}
```

#### マルチパスルーティング

**経路選択アルゴリズム**: Weighted Round Robin

```rust
pub struct PathScheduler {
    paths: Vec<Path>,
    weights: Vec<f32>,  // weight = 1.0 / RTT
    current_index: usize,
}

impl PathScheduler {
    fn select_path(&mut self) -> &Path {
        // Weighted Round Robin with RTT-based weights
        let total_weight: f32 = self.weights.iter().sum();
        let mut cumulative = 0.0;
        let random = rand::random::<f32>() * total_weight;
        
        for (i, &weight) in self.weights.iter().enumerate() {
            cumulative += weight;
            if random < cumulative {
                return &self.paths[i];
            }
        }
        &self.paths[0] // fallback
    }
}
```

---

### 7. 暗号化層（nyx-crypto）

**責務**: ハイブリッドポスト量子暗号、鍵管理、セッション暗号

#### ハイブリッドハンドシェイク（ML-KEM + X25519）

**プロトコルフロー**:

```
Client                                Server
------                                ------
1. Generate ML-KEM-768 keypair (pk_kyber, sk_kyber)
2. Generate X25519 keypair (pk_x25519, sk_x25519)

   --- [pk_kyber || pk_x25519] --->

3.                                  Generate own keypairs
4.                                  Perform ML-KEM encapsulation
5.                                  Perform X25519 key exchange

   <--- [ciphertext_kyber || pk_server_x25519] ---

6. Decrypt ML-KEM ciphertext → ss_kyber
7. Perform X25519 DH → ss_x25519
8. Derive final key: HKDF-Extract(ss_kyber || ss_x25519)

Both parties now share: shared_secret (32 bytes)
```

**実装**:

```rust
pub struct HybridHandshake;

impl HybridHandshake {
    // クライアント側
    pub fn client_init() -> Result<(HybridPublicKey, HybridKeyPair)> {
        let (kyber_pk, kyber_sk) = ml_kem::MlKem768::generate(&mut OsRng);
        let x25519_sk = EphemeralSecret::random_from_rng(&mut OsRng);
        let x25519_pk = x25519_dalek::PublicKey::from(&x25519_sk);
        
        let public = HybridPublicKey {
            kyber: kyber_pk.into_bytes(),
            x25519: x25519_pk.to_bytes(),
        };
        
        Ok((public, HybridKeyPair { kyber_sk, x25519_sk }))
    }
    
    // サーバー側
    pub fn server_encapsulate(client_pk: &HybridPublicKey) 
        -> Result<(HybridCiphertext, SharedSecret)> {
        // ML-KEM encapsulation
        let (ct_kyber, ss_kyber) = client_pk.kyber.encapsulate(&mut OsRng)?;
        
        // X25519 key exchange
        let server_sk = EphemeralSecret::random_from_rng(&mut OsRng);
        let server_pk = x25519_dalek::PublicKey::from(&server_sk);
        let ss_x25519 = server_sk.diffie_hellman(&client_pk.x25519);
        
        // Combine secrets
        let shared = Self::derive_key(&ss_kyber, &ss_x25519)?;
        
        Ok((HybridCiphertext { ct_kyber, server_pk }, shared))
    }
    
    // 鍵導出
    fn derive_key(ss_kyber: &[u8], ss_x25519: &[u8]) -> Result<SharedSecret> {
        let mut combined = Vec::with_capacity(64);
        combined.extend_from_slice(ss_kyber);
        combined.extend_from_slice(ss_x25519.as_bytes());
        
        let hkdf = Hkdf::<Sha256>::new(None, &combined);
        let mut output = [0u8; 32];
        hkdf.expand(b"nyx-hybrid-v1", &mut output)?;
        
        Ok(SharedSecret(output))
    }
}
```

**セキュリティプロパティ**:
- **量子耐性**: ML-KEM-768はNIST標準化済み、AES-192相当のセキュリティ
- **クラシカルセキュリティ**: X25519でフォールバック保証
- **前方秘匿性**: エフェメラル鍵使用
- **ハイブリッドセキュリティ**: 一方が破られても他方で保護

---

### 8. テレメトリ層（nyx-telemetry）

**責務**: 監視、メトリクス収集、トレーシング

#### Prometheusメトリクス

**エクスポートエンドポイント**: `http://localhost:9090/metrics`

**主要メトリクス**:

```
# HELP nyx_active_connections Current number of active connections
# TYPE nyx_active_connections gauge
nyx_active_connections 42

# HELP nyx_packets_sent_total Total packets sent
# TYPE nyx_packets_sent_total counter
nyx_packets_sent_total{path_id="0"} 1234567

# HELP nyx_packet_latency_seconds Packet round-trip latency
# TYPE nyx_packet_latency_seconds histogram
nyx_packet_latency_seconds_bucket{le="0.01"} 100
nyx_packet_latency_seconds_bucket{le="0.05"} 450
nyx_packet_latency_seconds_bucket{le="0.1"} 800
nyx_packet_latency_seconds_sum 45.2
nyx_packet_latency_seconds_count 1000
```

#### OpenTelemetry Tracing

**Span例**:

```json
{
  "name": "nyx.stream.send",
  "trace_id": "a1b2c3d4e5f6...",
  "span_id": "1234abcd",
  "parent_span_id": "5678efgh",
  "start_time": "2025-10-06T12:34:56.789Z",
  "end_time": "2025-10-06T12:34:56.823Z",
  "attributes": {
    "nyx.stream_id": "str_123456",
    "nyx.connection_id": "conn_abcdef",
    "nyx.path_id": 0,
    "nyx.payload_size": 1400
  }
}
```

**設定**:

```toml
[telemetry]
enabled = true
prometheus_addr = "127.0.0.1:9090"
otlp_endpoint = "http://localhost:4317"  # gRPC endpoint
sampling_ratio = 0.1  # 10%サンプリング
```

---

## データフロー

### 送信フロー（Application → Network）

```
1. Application
   └─ SDK.send(data)
       │
2. SDK Layer
   └─ DaemonClient.send_data(stream_id, data)
       │ [gRPC/JSON-RPC]
       ▼
3. Control Plane (nyx-daemon)
   └─ StreamManager.write(stream_id, data)
       │
4. Stream Layer
   └─ Frame.encode(data) → FrameType::Data
       │
5. Mix Layer
   └─ SphinxPacket.encrypt(frame, route)
       │ [3-hop onion encryption]
       ▼
6. Transport Layer
   └─ UdpTransport.send_to(encrypted_packet, peer_addr)
       │ [UDP datagram]
       ▼
7. Network
   └─ Internet → Mix Node 1 → Mix Node 2 → Exit Node → Destination
```

### 受信フロー（Network → Application）

```
1. Network
   └─ UDP packet received
       │
2. Transport Layer
   └─ UdpTransport.recv_from()
       │
3. Mix Layer
   └─ SphinxPacket.decrypt(private_key)
       │ [Remove one onion layer]
       ▼
4. Stream Layer
   └─ Frame.decode(payload)
       │
5. Control Plane
   └─ StreamManager.dispatch(frame)
       │ [Match stream_id]
       ▼
6. SDK Layer
   └─ StreamHandle.recv() → data
       │
7. Application
   └─ Process received data
```

---

## 外部連携ポイント

### 1. ブラウザ統合（HTTPプロキシ経由）

```
Browser ─── SOCKS5/HTTP CONNECT ──► nyx-http-proxy (Go)
                                           │
                                           │ [IPC: Unix socket]
                                           ▼
                                    nyx-daemon (Rust)
                                           │
                                           ▼
                                    Mix Network
```

### 2. モバイル統合（FFI経由）

```
iOS/Android App
      │
      │ [C-ABI]
      ▼
nyx-mobile-ffi
      │
      │ [Rust internal]
      ▼
nyx-daemon
```

**FFI関数例**:

```rust
#[no_mangle]
pub extern "C" fn nyx_init(config_path: *const c_char) -> *mut c_void;

#[no_mangle]
pub extern "C" fn nyx_open_stream(
    handle: *mut c_void,
    peer_id: *const c_char,
) -> i32;

#[no_mangle]
pub extern "C" fn nyx_send_data(
    handle: *mut c_void,
    stream_id: u64,
    data: *const u8,
    len: usize,
) -> i32;
```

### 3. Kubernetes統合

**Helm Chart構成**:

```yaml
# charts/nyx/values.yaml
replicaCount: 3

image:
  repository: ghcr.io/seleniaproject/nyx
  tag: "1.0.0"

service:
  type: LoadBalancer
  grpcPort: 50051
  metricsPort: 9090

autoscaling:
  enabled: true
  minReplicas: 3
  maxReplicas: 10
  targetCPUUtilizationPercentage: 70

podDisruptionBudget:
  enabled: true
  minAvailable: 2

monitoring:
  prometheus:
    enabled: true
  grafana:
    enabled: true
```

### 4. 監視統合

**Grafanaダッシュボード設定**:

```json
{
  "dashboard": {
    "title": "Nyx Network Metrics",
    "panels": [
      {
        "title": "Active Connections",
        "targets": [{
          "expr": "nyx_active_connections"
        }]
      },
      {
        "title": "Packet Latency P99",
        "targets": [{
          "expr": "histogram_quantile(0.99, nyx_packet_latency_seconds)"
        }]
      }
    ]
  }
}
```

---

## 採用パターンと選定理由

### 1. Actorモデル（nyx-daemon）

**選定理由**:
- 各ストリームが独立したアクター（tokio task）として動作
- メッセージパッシングで状態共有を最小化
- デッドロックリスクの低減

**実装**:
```rust
async fn stream_actor(
    stream_id: StreamId,
    mut rx: mpsc::Receiver<StreamCommand>,
) {
    loop {
        select! {
            Some(cmd) = rx.recv() => {
                match cmd {
                    StreamCommand::Send(data) => { /* handle */ }
                    StreamCommand::Close => break,
                }
            }
            _ = tokio::time::sleep(Duration::from_secs(30)) => {
                // Keepalive timeout
            }
        }
    }
}
```

### 2. Repository Pattern（設定管理）

**選定理由**:
- 設定のロード・保存ロジックを抽象化
- テスト時にモック実装と差し替え可能
- 将来的な永続化バックエンド変更に対応

**実装**:
```rust
#[async_trait]
pub trait ConfigRepository {
    async fn load(&self) -> Result<Config>;
    async fn save(&self, config: &Config) -> Result<()>;
}

pub struct TomlConfigRepository {
    path: PathBuf,
}
```

### 3. Strategy Pattern（暗号化アルゴリズム選択）

**選定理由**:
- Classic（X25519のみ）、Hybrid（X25519 + ML-KEM）、PQ-Only（ML-KEMのみ）を実行時選択
- Capability Negotiationでノード間で最適なモード自動選択

**実装**:
```rust
pub trait HandshakeStrategy {
    fn client_init(&self) -> Result<(PublicKey, PrivateKey)>;
    fn server_respond(&self, client_pk: &PublicKey) -> Result<SharedSecret>;
}

pub struct HybridStrategy;  // ML-KEM + X25519
pub struct ClassicStrategy; // X25519 only
pub struct PqOnlyStrategy;  // ML-KEM only
```

### 4. Circuit Breaker Pattern（ピア接続管理）

**選定理由**:
- 不安定なピアへの繰り返し接続を防止
- ネットワークリソースの保護

**実装**:
```rust
pub struct CircuitBreaker {
    state: CircuitState,
    failure_count: usize,
    threshold: usize,
    timeout: Duration,
}

enum CircuitState {
    Closed,   // 正常
    Open,     // 遮断中
    HalfOpen, // テスト中
}
```

---

## スケーラビリティ設計

### 水平スケーリング

- **ステートレス設計**: nyx-daemonはピア情報以外永続状態を持たない
- **DHT分散**: Kademlia DHTでピア発見を分散化
- **ロードバランサ対応**: gRPC endpointはL4/L7ロードバランサ配置可能

### 垂直スケーリング

- **非同期I/O**: tokioによる効率的なスレッド利用
- **ゼロコピー**: `Bytes`型で不要なメモリコピー削減
- **並行処理**: `DashMap`によるロックフリーデータ構造

---

## セキュリティ境界

### 信頼境界

```
[Trusted Zone]
  - nyx-daemon (local process)
  - nyx-cli (same user)
  - SDK (same process or localhost)

[Semi-Trusted Zone]
  - Known peers (authenticated)
  - Mix nodes (protocol-level trust)

[Untrusted Zone]
  - Internet traffic
  - Exit node destinations
  - Unknown peers
```

### 認証・認可

**ピア認証**:
- Ed25519署名ベースのピアID検証
- ハンドシェイク時の相互認証

**API認証**（将来実装予定）:
- JWT/PASETO tokenベース
- 現状はlocalhost bindingで暗黙的な認証

---

## パフォーマンス最適化

### 実測値（benchmarks/results/参照）

- **ファイル転送スループット**: 82.5 MB/s（1MBファイル）
- **メッセージングレイテンシ**: 12.5 ms（1KBメッセージ）
- **VoIPジッター**: < 5 ms（Opus 64kbps）
- **並行接続**: 500接続で平均37 msレイテンシ

### 最適化手法

1. **コンパイラ最適化**:
```toml
[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
```

2. **SIMD利用**（暗号化処理）:
- ChaCha20のSIMD実装（AVX2対応）
- Blake3の並列ハッシュ

3. **メモリプール**:
```rust
use bytes::BytesMut;
let mut buf = BytesMut::with_capacity(8192);
// Reuse buffer for multiple operations
```

---

## 補足: 推測箇所の明示

以下の情報はコードベースと既存ドキュメントから合理的に推測しています：

- **JWT認証**: コード内にPASETO実装があるが、現状未使用と判断
- **将来実装**: TODOコメントやissue trackerから推測
- **監視統合設定**: 標準的なPrometheus/Grafana構成を想定
