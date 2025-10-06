# Nyx SDK 完全ガイド (日本語)

## 目次

1. [はじめに](#はじめに)
2. [インストール](#インストール)
3. [クイックスタート](#クイックスタート)
4. [中核概念](#中核概念)
5. [設定](#設定)
6. [ストリームAPI](#ストリームapi)
7. [デーモンクライアント](#デーモンクライアント)
8. [エラーハンドリング](#エラーハンドリング)
9. [高度な使用法](#高度な使用法)
10. [ベストプラクティス](#ベストプラクティス)
11. [トラブルシューティング](#トラブルシューティング)
12. [APIリファレンス](#apiリファレンス)

## はじめに

Nyx SDKは、Nyx匿名化ネットワークと統合するアプリケーションを構築するためのRustネイティブAPIを提供します。

### 主な機能

- **純粋なRust実装**: C/C++依存関係ゼロ、完全なメモリ安全性
- **Async/Awaitサポート**: 高性能な非同期I/OのためにTokioを使用
- **型安全なAPI**: 強力な型システムが一般的なエラーを防止
- **包括的なエラーハンドリング**: コンテキスト情報を持つリッチなエラー型
- **ストリーム抽象化**: 統計とメタデータを持つ高レベルストリームAPI
- **デーモン統合**: デーモン制御用のJSON-RPCクライアント
- **クロスプラットフォーム**: Unix (Linux, macOS) と Windows で動作

## インストール

`Cargo.toml`に追加:

```toml
[dependencies]
nyx-sdk = { path = "../nyx-sdk" }
tokio = { version = "1.37", features = ["full"] }
bytes = "1.5"
```

## クイックスタート

### 基本的なストリーム使用

```rust
use nyx_sdk::{NyxStream, Result};
use bytes::Bytes;

#[tokio::main]
async fn main() -> Result<()> {
    // テスト用の接続されたストリームペアを作成
    let (mut sender, mut receiver) = NyxStream::pair(1024);

    // データを送信
    sender.send(Bytes::from("こんにちは、Nyx!")).await?;

    // データを受信
    if let Some(data) = receiver.recv().await? {
        println!("受信: {:?}", data);
    }

    // ストリームを閉じる
    sender.close().await?;
    receiver.close().await?;

    Ok(())
}
```

### デーモンクライアント使用

```rust
use nyx_sdk::{DaemonClient, SdkConfig, Result};

#[tokio::main]
async fn main() -> Result<()> {
    // 設定を作成
    let config = SdkConfig::default();

    // 自動検出されたトークンでクライアントを作成
    let client = DaemonClient::new_with_auto_token(config).await;

    // デーモン情報を取得
    let info = client.get_info().await?;
    println!("デーモン情報: {:?}", info);

    Ok(())
}
```

## 中核概念

### 設定

SDKはすべての設定ニーズに`SdkConfig`を使用します:

- デーモンエンドポイント設定 (UnixソケットまたはWindowsネームドパイプ)
- タイムアウト設定
- サイズ制限
- 再接続ポリシー
- ロギングオプション

### ストリーム

`NyxStream`は、以下の機能を持つ基礎となるネットワークストリームの高レベル抽象化を提供:

- 非同期送受信操作
- 自動統計収集
- メタデータサポート
- タイムアウト処理
- ライフサイクル管理

### エラーハンドリング

すべての操作は`Result<T, Error>`を返します。`Error`は以下を持つリッチなenum:

- コンテキスト情報
- エラー分類
- リトライ可能性インジケーター
- 致命的エラー検出

## 設定

### ビルダーパターンの使用

```rust
use nyx_sdk::SdkConfig;

let config = SdkConfig::builder()
    .daemon_endpoint("/var/run/nyx.sock")
    .request_timeout_ms(15000)
    .auto_reconnect(true)
    .max_reconnect_attempts(3)
    .enable_logging(true)
    .build()?;
```

### ファイルから読み込み

```rust
let config = SdkConfig::from_file("config.toml").await?;
```

### ファイルに保存

```rust
let config = SdkConfig::default();
config.save_to_file("config.toml").await?;
```

### 設定オプション

| オプション | 型 | デフォルト | 説明 |
|--------|------|---------|-------------|
| `daemon_endpoint` | String | プラットフォーム依存 | ソケットパスまたはネームドパイプ |
| `request_timeout_ms` | u64 | 10000 | リクエストタイムアウト(ミリ秒) |
| `max_request_size` | usize | 1MB | 最大リクエストサイズ |
| `max_response_size` | usize | 10MB | 最大レスポンスサイズ |
| `auto_reconnect` | bool | true | 自動再接続を有効化 |
| `max_reconnect_attempts` | u32 | 5 | 最大再接続試行回数 |
| `reconnect_delay_ms` | u64 | 1000 | 初期再接続遅延 |
| `enable_logging` | bool | false | リクエスト/レスポンスログを有効化 |

## ストリームAPI

### ストリームの作成

```rust
// デフォルト設定
let stream = NyxStream::new();

// カスタム設定
use nyx_stream::AsyncStreamConfig;
let config = AsyncStreamConfig {
    stream_id: 42,
    ..Default::default()
};
let stream = NyxStream::with_config(config);

// テスト用の接続されたペア
let (stream_a, stream_b) = NyxStream::pair(4096);
```

### データ送信

```rust
// 基本送信
stream.send(Bytes::from("データ")).await?;

// タイムアウト付き送信
stream.send_with_timeout(Bytes::from("データ"), 5000).await?;
```

### データ受信

```rust
// 基本受信
if let Some(data) = stream.recv().await? {
    println!("{}バイト受信", data.len());
}

// タイムアウト付き受信
match stream.recv_with_timeout(5000).await? {
    Some(data) => println!("受信: {:?}", data),
    None => println!("ストリーム閉じられた"),
}
```

### ストリーム統計

```rust
let stats = stream.stats();
println!("送信バイト数: {}", stats.bytes_sent);
println!("受信バイト数: {}", stats.bytes_received);
println!("送信メッセージ数: {}", stats.messages_sent);
println!("受信メッセージ数: {}", stats.messages_received);
println!("エラー数: {}", stats.errors);

// アップタイムとアイドル時間
if let Some(uptime) = stream.uptime() {
    println!("ストリームアップタイム: {:?}", uptime);
}
if let Some(idle) = stream.idle_time() {
    println!("最後のアクティビティからの時間: {:?}", idle);
}
```

### ストリームメタデータ

```rust
// ターゲットを設定
stream.set_target("example.com").await;

// カスタムメタデータを追加
stream.add_user_data("key", "value").await;

// メタデータを取得
let metadata = stream.metadata().await;
println!("ストリームID: {}", metadata.stream_id);
println!("ターゲット: {:?}", metadata.target);
println!("ユーザーデータ: {:?}", metadata.user_data);
```

## デーモンクライアント

### 認証

デーモンクライアントは複数の認証方法をサポート:

```rust
// 自動検出 (推奨)
// チェック: NYX_CONTROL_TOKEN → NYX_TOKEN → クッキーファイル
let client = DaemonClient::new_with_auto_token(config).await;

// 手動トークン
let client = DaemonClient::new(config)
    .with_token("your-secret-token");

// プログラム的自動検出
let client = DaemonClient::new(config).with_auto_token().await;
```

### トークン検出の優先順位

1. `NYX_CONTROL_TOKEN` 環境変数
2. `NYX_TOKEN` 環境変数
3. `$NYX_DAEMON_COOKIE` またはデフォルトパスのクッキーファイル
   - Windows: `%APPDATA%\nyx\control.authcookie`
   - Unix: `~/.nyx/control.authcookie`

### デーモン操作

#### デーモン情報取得

```rust
let info = client.get_info().await?;
```

#### 設定リロード

```rust
let result = client.reload_config().await?;
```

#### 設定更新

```rust
use serde_json::json;

let mut settings = serde_json::Map::new();
settings.insert("log_level".into(), json!("debug"));
settings.insert("max_connections".into(), json!(100));

let response = client.update_config(settings).await?;
if response.success {
    println!("設定更新: {}", response.message);
} else {
    println!("設定更新失敗: {}", response.message);
    for error in response.validation_errors {
        println!("  - {}", error);
    }
}
```

#### 設定バージョン管理

```rust
// バージョンリスト
let versions = client.list_versions().await?;

// スナップショット作成
let snapshot = client.create_config_snapshot(
    Some("メジャーアップデート前".to_string())
).await?;

// バージョンにロールバック
let result = client.rollback_config(version_number).await?;
```

#### イベントサブスクリプション

```rust
use tokio_stream::StreamExt;

// すべてのイベントをサブスクライブ
let mut events = client.subscribe_events(None).await?;

// 特定のイベントタイプをサブスクライブ
let mut events = client.subscribe_events(
    Some(vec!["connection".into(), "error".into()])
).await?;

// イベント処理
while let Ok(event) = events.recv().await {
    println!("イベントタイプ: {}", event.event_type);
    println!("詳細: {}", event.detail);
}
```

## エラーハンドリング

### エラータイプ

```rust
use nyx_sdk::Error;

match operation().await {
    Ok(result) => println!("成功: {:?}", result),
    Err(Error::Timeout { duration_ms }) => {
        println!("操作が{}msでタイムアウト", duration_ms);
    }
    Err(Error::Disconnected { reason }) => {
        println!("切断: {}", reason);
    }
    Err(Error::AuthenticationFailed(msg)) => {
        println!("認証失敗: {}", msg);
    }
    Err(e) => println!("その他のエラー: {}", e),
}
```

### エラーカテゴリ

```rust
let error = operation().await.unwrap_err();

// エラープロパティをチェック
if error.is_retryable() {
    println!("このエラーはリトライ可能");
}

if error.is_fatal() {
    println!("これは致命的エラー、リトライすべきでない");
}

// メトリクス用のエラーカテゴリを取得
let category = error.category();
println!("エラーカテゴリ: {}", category);
```

### リトライロジック

```rust
use tokio::time::{sleep, Duration};

async fn retry_operation<F, T>(mut op: F, max_attempts: u32) -> Result<T>
where
    F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T>>>>,
{
    let mut attempt = 0;
    loop {
        match op().await {
            Ok(result) => return Ok(result),
            Err(e) if e.is_retryable() && attempt < max_attempts => {
                attempt += 1;
                let delay = Duration::from_millis(100 * 2u64.pow(attempt));
                println!("試行{}失敗、{:?}後にリトライ", attempt, delay);
                sleep(delay).await;
            }
            Err(e) => return Err(e),
        }
    }
}
```

## ベストプラクティス

### 1. 設定にビルダーパターンを使用

```rust
// 良い
let config = SdkConfig::builder()
    .request_timeout_ms(5000)
    .auto_reconnect(true)
    .build()?;

// 避ける
let mut config = SdkConfig::default();
config.request_timeout_ms = 5000;
config.auto_reconnect = true;
// バリデーションなし!
```

### 2. エラーを適切に処理

```rust
// 良い
match client.get_info().await {
    Ok(info) => process(info),
    Err(e) if e.is_retryable() => retry_later(),
    Err(e) => log_fatal_error(e),
}

// 避ける
let info = client.get_info().await.unwrap(); // エラーでパニック
```

### 3. ネットワーク操作にタイムアウトを使用

```rust
// 良い
stream.send_with_timeout(data, 5000).await?;

// 危険
stream.send(data).await?; // 無期限にハングする可能性
```

### 4. リソースを明示的に閉じる

```rust
// 良い
{
    let mut stream = NyxStream::new();
    // ストリームを使用
    stream.close().await?;
}

// Dropに依存しない
let mut stream = NyxStream::new();
// ストリームを使用
// ストリームが正しく閉じられない可能性
```

### 5. ストリームの健全性を監視

```rust
async fn monitor_stream(stream: &NyxStream) {
    if let Some(idle) = stream.idle_time() {
        if idle > Duration::from_secs(300) {
            println!("警告: ストリームが{:?}アイドル", idle);
        }
    }
    
    let stats = stream.stats();
    if stats.errors > 10 {
        println!("警告: {}個のエラー検出", stats.errors);
    }
}
```

## トラブルシューティング

### よくある問題

#### 1. 接続拒否

```
Error: Io(Os { code: 111, kind: ConnectionRefused, message: "Connection refused" })
```

**解決策**: Nyxデーモンが実行中で、正しいソケットでリッスンしていることを確認。

```bash
# デーモンが実行中か確認
ps aux | grep nyx-daemon

# ソケットが存在するか確認
ls -l /tmp/nyx.sock  # Unix
```

#### 2. タイムアウトエラー

```
Error: Timeout { duration_ms: 10000 }
```

**解決策**:
- タイムアウトを増やす: `config.request_timeout_ms = 30000;`
- ネットワーク接続を確認
- デーモンが応答していることを確認

#### 3. 認証失敗

```
Error: AuthenticationFailed("Invalid token")
```

**解決策**:
- トークンが正しいことを確認
- 環境変数を確認: `echo $NYX_TOKEN`
- クッキーファイルが存在し読み取り可能であることを確認
- 必要に応じてデーモントークンを再生成

## 例

完全な例については、`examples/`ディレクトリを参照:

- `basic_stream.rs` - 基本的なストリーム使用
- `daemon_client.rs` - デーモンクライアント操作
- `event_subscription.rs` - イベントハンドリング
- `error_handling.rs` - エラーハンドリングパターン
- `stream_metadata.rs` - ストリームメタデータと監視

## ライセンス

MIT OR Apache-2.0
