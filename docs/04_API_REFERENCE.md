# NyxNet API / 外部インターフェース リファレンス

**最終更新**: 2025年10月6日  
**対象バージョン**: v1.0

---

## 概要

NyxNetは以下の3種類のAPIを提供します：

1. **gRPC API** (Pure Rust): アプリケーション統合用（nyx-sdk経由）
2. **JSON-RPC 2.0 API** (IPC): CLIツール・外部ツール用
3. **SOCKS5/HTTP CONNECT Proxy**: ブラウザ・既存アプリケーション用

---

## 1. gRPC API

### エンドポイント

**デフォルトアドレス**: `localhost:50051`  
**プロトコル**: HTTP/2 over TCP  
**認証**: なし（localhost binding前提）  
**TLS**: 無効（Pure Rust実装、TLSは将来追加予定）

### サービス定義

```protobuf
syntax = "proto3";
package nyx.control.v1;

service NyxControl {
  // ノード情報取得
  rpc GetNodeInfo(Empty) returns (NodeInfoResponse);
  
  // ストリーム管理
  rpc OpenStream(OpenStreamRequest) returns (StreamResponse);
  rpc CloseStream(CloseStreamRequest) returns (Empty);
  rpc ListStreams(Empty) returns (StreamListResponse);
  rpc SendData(SendDataRequest) returns (Empty);
  
  // ピア管理
  rpc ListPeers(Empty) returns (PeerListResponse);
  rpc ConnectPeer(ConnectPeerRequest) returns (Empty);
  rpc DisconnectPeer(DisconnectPeerRequest) returns (Empty);
  
  // 設定管理
  rpc GetConfig(Empty) returns (ConfigResponse);
  rpc UpdateConfig(UpdateConfigRequest) returns (Empty);
  rpc ReloadConfig(Empty) returns (Empty);
  
  // メトリクス・診断
  rpc GetMetrics(Empty) returns (MetricsResponse);
  rpc GetHealth(Empty) returns (HealthResponse);
  
  // 高度な機能
  rpc GetRouteInfo(GetRouteInfoRequest) returns (RouteInfoResponse);
  rpc SetLowPowerMode(LowPowerModeRequest) returns (Empty);
}
```

---

### 主要RPC詳細

#### GetNodeInfo

**用途**: ノード情報とケイパビリティの取得

**リクエスト**:
```protobuf
message Empty {}
```

**レスポンス**:
```protobuf
message NodeInfoResponse {
  string node_id = 1;           // "12D3KooW..." (libp2p peer ID形式)
  string version = 2;           // "1.0.0"
  repeated string capabilities = 3; // ["multipath", "hybrid_pq", "low_power"]
  string compliance_level = 4;  // "Core" | "Plus" | "Full"
  uint64 uptime_seconds = 5;
  NetworkInfo network = 6;
}

message NetworkInfo {
  string bind_addr = 1;         // "127.0.0.1:43300"
  uint32 active_connections = 2;
  uint32 peer_count = 3;
}
```

**リクエスト例** (grpcurl):
```bash
grpcurl -plaintext localhost:50051 nyx.control.v1.NyxControl/GetNodeInfo
```

**レスポンス例**:
```json
{
  "node_id": "12D3KooWRm8J7NXy...",
  "version": "1.0.0",
  "capabilities": [
    "multipath",
    "hybrid_pq",
    "sphinx_routing",
    "low_power"
  ],
  "compliance_level": "Full",
  "uptime_seconds": 3600,
  "network": {
    "bind_addr": "127.0.0.1:43300",
    "active_connections": 42,
    "peer_count": 15
  }
}
```

**エラー**:
- `UNAVAILABLE`: デーモンが起動していない
- `INTERNAL`: 内部エラー

---

#### OpenStream

**用途**: 新しいストリームの開始

**リクエスト**:
```protobuf
message OpenStreamRequest {
  string peer_id = 1;           // 接続先ピアID（必須）
  StreamOptions options = 2;    // オプション設定
}

message StreamOptions {
  bool multipath = 1;           // マルチパス有効化
  uint32 priority = 2;          // 優先度 (0=低, 10=高)
  repeated string route_hints = 3; // 経路ヒント（ノードID配列）
}
```

**レスポンス**:
```protobuf
message StreamResponse {
  string stream_id = 1;         // "str_a1b2c3d4..."
  StreamStatus status = 2;
}

enum StreamStatus {
  STREAM_STATUS_UNSPECIFIED = 0;
  STREAM_STATUS_HANDSHAKE = 1;
  STREAM_STATUS_ESTABLISHED = 2;
  STREAM_STATUS_CLOSING = 3;
  STREAM_STATUS_CLOSED = 4;
}
```

**リクエスト例**:
```bash
grpcurl -plaintext -d '{
  "peer_id": "12D3KooWPeerAbc...",
  "options": {
    "multipath": true,
    "priority": 5
  }
}' localhost:50051 nyx.control.v1.NyxControl/OpenStream
```

**レスポンス例**:
```json
{
  "stream_id": "str_a1b2c3d4e5f6",
  "status": "STREAM_STATUS_ESTABLISHED"
}
```

**エラー**:
- `INVALID_ARGUMENT`: peer_idが不正
- `NOT_FOUND`: 指定ピアが見つからない
- `RESOURCE_EXHAUSTED`: 同時接続数上限
- `DEADLINE_EXCEEDED`: ハンドシェイクタイムアウト（30秒）

---

#### SendData

**用途**: ストリームへのデータ送信

**リクエスト**:
```protobuf
message SendDataRequest {
  string stream_id = 1;         // ストリームID（必須）
  bytes data = 2;               // 送信データ（最大8MB）
}
```

**レスポンス**:
```protobuf
message Empty {}
```

**リクエスト例** (Rust SDK):
```rust
use nyx_sdk::DaemonClient;

let client = DaemonClient::connect("http://localhost:50051").await?;
let stream_id = "str_a1b2c3d4e5f6";
let data = b"Hello, Nyx!";

client.send_data(stream_id, data).await?;
```

**エラー**:
- `INVALID_ARGUMENT`: stream_idが不正またはデータサイズ超過
- `NOT_FOUND`: ストリームが存在しない
- `FAILED_PRECONDITION`: ストリームが確立されていない

---

#### GetMetrics

**用途**: リアルタイムメトリクス取得

**リクエスト**:
```protobuf
message Empty {}
```

**レスポンス**:
```protobuf
message MetricsResponse {
  uint64 packets_sent = 1;
  uint64 packets_received = 2;
  uint64 bytes_sent = 3;
  uint64 bytes_received = 4;
  uint32 active_streams = 5;
  repeated PathMetrics paths = 6;
}

message PathMetrics {
  uint32 path_id = 1;
  uint32 rtt_ms = 2;
  uint32 packet_loss = 3;       // per 10000
  uint64 bandwidth_bps = 4;
}
```

**レスポンス例**:
```json
{
  "packets_sent": 123456,
  "packets_received": 98765,
  "bytes_sent": 104857600,
  "bytes_received": 83886080,
  "active_streams": 5,
  "paths": [
    {
      "path_id": 0,
      "rtt_ms": 25,
      "packet_loss": 5,
      "bandwidth_bps": 10485760
    },
    {
      "path_id": 1,
      "rtt_ms": 50,
      "packet_loss": 10,
      "bandwidth_bps": 5242880
    }
  ]
}
```

---

## 2. JSON-RPC 2.0 API (IPC)

### エンドポイント

**Unix socket**: `/tmp/nyx-daemon.sock` (Linux/macOS)  
**Named pipe**: `\\.\pipe\nyx-daemon` (Windows)  
**プロトコル**: JSON-RPC 2.0 over line-delimited JSON  
**認証**: なし（ファイルシステムパーミッション）

### メソッド一覧

| メソッド | 説明 |
|---------|------|
| `get_info` | ノード情報取得 |
| `open_stream` | ストリーム開始 |
| `close_stream` | ストリーム終了 |
| `list_streams` | ストリーム一覧 |
| `send_data` | データ送信 |
| `get_metrics` | メトリクス取得 |
| `update_config` | 設定更新 |
| `reload_config` | 設定リロード |
| `subscribe_events` | イベント購読 |

---

### リクエスト・レスポンス形式

#### 基本構造

**リクエスト**:
```json
{
  "jsonrpc": "2.0",
  "id": "req-123",
  "method": "method_name",
  "params": {
    "param1": "value1"
  }
}
```

**成功レスポンス**:
```json
{
  "jsonrpc": "2.0",
  "id": "req-123",
  "result": {
    "field1": "value1"
  }
}
```

**エラーレスポンス**:
```json
{
  "jsonrpc": "2.0",
  "id": "req-123",
  "error": {
    "code": -32600,
    "message": "Invalid Request",
    "data": {
      "details": "Missing required field: peer_id"
    }
  }
}
```

---

### 主要メソッド詳細

#### get_info

**パラメータ**: なし

**リクエスト例**:
```json
{
  "jsonrpc": "2.0",
  "id": "1",
  "method": "get_info",
  "params": {}
}
```

**レスポンス例**:
```json
{
  "jsonrpc": "2.0",
  "id": "1",
  "result": {
    "node_id": "12D3KooWRm8J7NXy...",
    "version": "1.0.0",
    "capabilities": ["multipath", "hybrid_pq"],
    "uptime_seconds": 3600
  }
}
```

---

#### open_stream

**パラメータ**:
- `peer_id` (string, 必須): 接続先ピアID
- `multipath` (boolean, オプション): マルチパス有効化（デフォルト: false）

**リクエスト例**:
```json
{
  "jsonrpc": "2.0",
  "id": "2",
  "method": "open_stream",
  "params": {
    "peer_id": "12D3KooWPeerAbc...",
    "multipath": true
  }
}
```

**レスポンス例**:
```json
{
  "jsonrpc": "2.0",
  "id": "2",
  "result": {
    "stream_id": "str_a1b2c3d4e5f6",
    "status": "established"
  }
}
```

---

#### subscribe_events

**パラメータ**:
- `event_types` (array of string): 購読イベントタイプ

**イベントタイプ**:
- `stream_opened`: ストリーム開始
- `stream_closed`: ストリーム終了
- `peer_connected`: ピア接続
- `peer_disconnected`: ピア切断
- `config_updated`: 設定更新

**リクエスト例**:
```json
{
  "jsonrpc": "2.0",
  "id": "3",
  "method": "subscribe_events",
  "params": {
    "event_types": ["stream_opened", "stream_closed"]
  }
}
```

**レスポンス（購読確認）**:
```json
{
  "jsonrpc": "2.0",
  "id": "3",
  "result": {
    "subscription_id": "sub_xyz123"
  }
}
```

**イベント通知** (id = null):
```json
{
  "jsonrpc": "2.0",
  "method": "event",
  "params": {
    "subscription_id": "sub_xyz123",
    "event_type": "stream_opened",
    "data": {
      "stream_id": "str_new123",
      "peer_id": "12D3KooW...",
      "timestamp": "2025-10-06T12:34:56Z"
    }
  }
}
```

---

### エラーコード

| コード | 名称 | 説明 |
|-------|------|------|
| -32700 | Parse error | 不正なJSON |
| -32600 | Invalid Request | JSON-RPC仕様違反 |
| -32601 | Method not found | 未知のメソッド |
| -32602 | Invalid params | パラメータ不正 |
| -32603 | Internal error | サーバー内部エラー |
| -32000 | Stream not found | ストリームが存在しない |
| -32001 | Peer not found | ピアが見つからない |
| -32002 | Connection failed | 接続失敗 |
| -32003 | Authentication failed | 認証失敗（将来用） |

---

### 使用例 (CLI実装)

```rust
// nyx-cli/src/ipc_client.rs
use tokio::net::UnixStream;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};

pub struct IpcClient {
    stream: UnixStream,
    next_id: AtomicU64,
}

impl IpcClient {
    pub async fn connect(path: &str) -> Result<Self> {
        let stream = UnixStream::connect(path).await?;
        Ok(Self {
            stream,
            next_id: AtomicU64::new(1),
        })
    }
    
    pub async fn call(&mut self, method: &str, params: serde_json::Value) 
        -> Result<serde_json::Value> {
        
        let id = self.next_id.fetch_add(1, Ordering::Relaxed);
        
        let request = serde_json::json!({
            "jsonrpc": "2.0",
            "id": id.to_string(),
            "method": method,
            "params": params,
        });
        
        // リクエスト送信（改行区切り）
        let request_str = serde_json::to_string(&request)?;
        self.stream.write_all(request_str.as_bytes()).await?;
        self.stream.write_all(b"\n").await?;
        
        // レスポンス受信
        let mut reader = BufReader::new(&mut self.stream);
        let mut line = String::new();
        reader.read_line(&mut line).await?;
        
        let response: serde_json::Value = serde_json::from_str(&line)?;
        
        // エラーチェック
        if let Some(error) = response.get("error") {
            return Err(Error::RpcError(error.clone()));
        }
        
        Ok(response["result"].clone())
    }
}
```

---

## 3. SOCKS5/HTTP CONNECT Proxy API

### エンドポイント

**SOCKS5**: `localhost:9050`  
**HTTP CONNECT**: `localhost:8080`  
**Health Check**: `http://localhost:8081/health`

### SOCKS5プロトコル（RFC 1928）

#### 接続フロー

```
1. クライアント → サーバー: 認証方法ネゴシエーション
   [VER=0x05, NMETHODS=0x01, METHODS=[0x00]]
   
2. サーバー → クライアント: 認証方法選択
   [VER=0x05, METHOD=0x00]  (0x00 = 認証なし)
   
3. クライアント → サーバー: 接続リクエスト
   [VER=0x05, CMD=0x01, RSV=0x00, ATYP=0x03, DST.ADDR, DST.PORT]
   
4. サーバー → クライアント: 接続レスポンス
   [VER=0x05, REP=0x00, RSV=0x00, ATYP=0x01, BND.ADDR, BND.PORT]
   
5. データ転送（透過的TCPリレー）
```

#### サポート機能

- **コマンド**:
  - `CONNECT (0x01)`: TCP接続（サポート）
  - `BIND (0x02)`: 未サポート
  - `UDP ASSOCIATE (0x03)`: 未サポート

- **アドレスタイプ**:
  - `IPv4 (0x01)`: サポート
  - `DOMAINNAME (0x03)`: サポート
  - `IPv6 (0x04)`: サポート

- **認証方式**:
  - `NO AUTHENTICATION (0x00)`: サポート
  - `USERNAME/PASSWORD (0x02)`: 未サポート

---

### HTTP CONNECTプロトコル

#### 接続フロー

```
1. クライアント → プロキシ: CONNECT リクエスト
   CONNECT example.com:443 HTTP/1.1
   Host: example.com:443
   User-Agent: curl/7.68.0
   
2. プロキシ → クライアント: 成功レスポンス
   HTTP/1.1 200 Connection Established
   
3. TLSハンドシェイク（プロキシは透過的に転送）
   
4. データ転送（透過的TCPリレー）
```

#### エラーレスポンス

```http
# 接続失敗
HTTP/1.1 502 Bad Gateway
Content-Type: text/plain

Failed to connect to example.com:443

# タイムアウト
HTTP/1.1 504 Gateway Timeout
Content-Type: text/plain

Connection timeout after 30s
```

---

### ブラウザ設定例

#### Firefox

1. Settings → Network Settings
2. Manual proxy configuration
3. SOCKS Host: `localhost`, Port: `9050`
4. SOCKS v5: チェック
5. Proxy DNS when using SOCKS v5: チェック

#### Chrome/Chromium

```bash
# Linux/macOS
chromium --proxy-server="socks5://localhost:9050"

# Windows PowerShell
chrome.exe --proxy-server="socks5://localhost:9050"
```

#### curl

```bash
# SOCKS5
curl --socks5 localhost:9050 https://example.com

# HTTP CONNECT
curl --proxy http://localhost:8080 https://example.com

# DNS解決もプロキシ経由
curl --socks5-hostname localhost:9050 https://example.com
```

---

### 統計API（HTTP）

**エンドポイント**: `http://localhost:8081/stats`

**レスポンス例**:
```json
{
  "total_connections": 1234,
  "socks5_connections": 890,
  "http_connections": 344,
  "active_connections": 12,
  "bytes_transferred": 104857600,
  "errors": 5,
  "uptime_seconds": 7200
}
```

---

## レート制限

### グローバル制限

- **接続数**: 1000 concurrent connections (設定可能)
- **リクエストレート**: 100 requests/sec/peer（デフォルト）
- **帯域幅**: 10 MB/sec/peer（デフォルト）

### 制限超過時の動作

**gRPC**:
```
Status: RESOURCE_EXHAUSTED
Message: "Rate limit exceeded: 100 requests/sec"
```

**JSON-RPC**:
```json
{
  "jsonrpc": "2.0",
  "id": "123",
  "error": {
    "code": -32004,
    "message": "Rate limit exceeded"
  }
}
```

**SOCKS5/HTTP**:
- 新規接続拒否（TCPコネクションクローズ）
- 既存接続は影響なし

---

## 認証・認可（将来実装予定）

### JWT/PASETO Token認証

**現在のステータス**: 未実装（localhost bindingで暗黙的に認証）

**計画中の実装**:

```json
// リクエストヘッダ
{
  "jsonrpc": "2.0",
  "id": "1",
  "method": "open_stream",
  "params": { "peer_id": "12D3KooW..." },
  "auth": {
    "type": "bearer",
    "token": "v4.local.Gdh5kiOTyyaQ3_..."
  }
}
```

---

## エラーフォーマット

### gRPCステータスコード

| コード | 名称 | HTTPステータス |
|-------|------|---------------|
| OK | 成功 | 200 |
| CANCELLED | キャンセル | 499 |
| INVALID_ARGUMENT | 不正な引数 | 400 |
| DEADLINE_EXCEEDED | タイムアウト | 504 |
| NOT_FOUND | 見つからない | 404 |
| ALREADY_EXISTS | すでに存在 | 409 |
| PERMISSION_DENIED | 権限なし | 403 |
| RESOURCE_EXHAUSTED | リソース不足 | 429 |
| FAILED_PRECONDITION | 前提条件エラー | 400 |
| UNAVAILABLE | 利用不可 | 503 |
| INTERNAL | 内部エラー | 500 |

---

## SDK使用例

### Rust SDK

```rust
use nyx_sdk::{DaemonClient, StreamHandle};

#[tokio::main]
async fn main() -> Result<()> {
    // 1. デーモン接続
    let client = DaemonClient::connect("http://localhost:50051").await?;
    
    // 2. ノード情報取得
    let info = client.get_node_info().await?;
    println!("Node ID: {}", info.node_id);
    
    // 3. ストリーム開始
    let stream = client.open_stream("12D3KooWPeer...").await?;
    
    // 4. データ送信
    stream.send(b"Hello, Nyx!").await?;
    
    // 5. データ受信
    if let Some(data) = stream.recv().await? {
        println!("Received: {:?}", data);
    }
    
    // 6. ストリームクローズ
    stream.close().await?;
    
    Ok(())
}
```

### Python SDK（計画中）

```python
import asyncio
from nyx_sdk import DaemonClient

async def main():
    # デーモン接続
    async with DaemonClient("localhost:50051") as client:
        # ストリーム開始
        stream = await client.open_stream("12D3KooWPeer...")
        
        # データ送受信
        await stream.send(b"Hello, Nyx!")
        data = await stream.recv()
        print(f"Received: {data}")

asyncio.run(main())
```

---

## 補足: 推測箇所の明示

以下の情報は既存コード・プロトタイプから合理的に推測しています：

- **Python SDK**: 計画中として記載、実装は未確認
- **認証機能**: コードにPASETO実装があるが、現在未使用と判断
- **一部のエラーコード**: 標準的なJSON-RPC/gRPCエラーコードを想定
