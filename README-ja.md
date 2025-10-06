# NyxNet

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Rust](https://img.shields.io/badge/rust-1.70%2B-orange.svg)](https://www.rust-lang.org/)
[![Go](https://img.shields.io/badge/go-1.21%2B-00ADD8.svg)](https://go.dev/)

[![Main CI](https://github.com/SeleniaProject/NyxNet/actions/workflows/main.yml/badge.svg)](https://github.com/SeleniaProject/NyxNet/actions/workflows/main.yml)
[![Security Audit](https://github.com/SeleniaProject/NyxNet/actions/workflows/security.yml/badge.svg)](https://github.com/SeleniaProject/NyxNet/actions/workflows/security.yml)
[![Formal Verification](https://github.com/SeleniaProject/NyxNet/actions/workflows/formal-verification.yml/badge.svg)](https://github.com/SeleniaProject/NyxNet/actions/workflows/formal-verification.yml)
[![Coverage](https://github.com/SeleniaProject/NyxNet/actions/workflows/coverage.yml/badge.svg)](https://github.com/SeleniaProject/NyxNet/actions/workflows/coverage.yml)

**NyxNet** は、ピュアRustで書かれたプライバシーファースト、ポスト量子セキュアなネットワークスタックです。量子耐性暗号を組み込んだミックスネットワークアーキテクチャを使用して、匿名通信を提供します。量子コンピュータの脅威時代に対応した設計となっています。

[English README is here](README.md)

---

## 目次

- [特徴](#特徴)
- [アーキテクチャ](#アーキテクチャ)
- [クイックスタート](#クイックスタート)
- [インストール](#インストール)
- [使用例](#使用例)
- [ドキュメント](#ドキュメント)
- [パフォーマンス](#パフォーマンス)
- [セキュリティ](#セキュリティ)
- [開発](#開発)
- [貢献](#貢献)
- [ライセンス](#ライセンス)

---

## 特徴

### 🎯 機能マトリックス

```mermaid
mindmap
  root((NyxNet))
    セキュリティ
      ポスト量子暗号
        ML-KEM-768
        X25519 ハイブリッド
      Sphinx ルーティング
        3ホップミックス
        レイヤー暗号化
      リプレイ保護
        Bloom フィルタ
        タイムスタンプナンス
    パフォーマンス
      QUIC Transport
        低レイテンシ
        UDP データグラム
      マルチパスルーティング
        自動フェイルオーバー
        負荷分散
      FEC
        Reed-Solomon
        適応的冗長性
    プライバシー
      カバートラフィック
        ポアソン分布
        ダミーパケット
      トラフィック分析耐性
      単一信頼点なし
    統合
      gRPC API
        20以上のRPC
        ストリーム制御
      SOCKS5 プロキシ
        Tor互換
        ブラウザサポート
      OpenTelemetry
        Jaeger
        Prometheus
    モバイル
      低電力モード
        バッテリー最適化
      FFI バインディング
        iOS
        Android
      Push プロキシ
```

### コア機能

| 機能 | 説明 | ステータス |
|------|------|----------|
| **🔐 ポスト量子暗号** | ML-KEM-768（NIST標準化済み）とX25519を使用したハイブリッドハンドシェイク | ✅ 完成 |
| **🧅 Sphinxオニオンルーティング** | レイヤー暗号化による3ホップミックスネットワークによるトラフィック匿名化 | ✅ 完成 |
| **⚡ QUICトランスポート** | UDPデータグラム上の低レイテンシマルチパストランスポート | ✅ 完成 |
| **🛡️ 前方誤り訂正** | Reed-Solomon符号を使用した適応的冗長性制御 | ✅ 完成 |
| **🎛️ gRPC制御API** | ノード管理とストリーム制御のための20以上のRPC | ✅ 完成 |
| **🔒 リプレイ攻撃保護** | Bloomフィルタを使用したタイムスタンプベースのナンス検証 | ✅ 完成 |

### 高度な機能

| 機能 | 説明 | ステータス |
|------|------|----------|
| **🛤️ マルチパスルーティング** | 複数経路での同時通信と自動フェイルオーバー | ✅ 完成 |
| **👻 カバートラフィック** | ポアソン分布に基づく適応的ダミーパケット生成 | ✅ 完成 |
| **🌐 NAT Traversal** | ICE Lite実装によるSTUNサポート | ✅ 完成 |
| **🔄 ホット設定リロード** | ダウンタイムなしの動的設定更新 | ✅ 完成 |
| **🌍 国際化** | Fluent形式のメッセージローカライゼーション | ✅ 完成 |

### 完全機能

| 機能 | 説明 | ステータス |
|------|------|----------|
| **⚙️ cMix統合** | VDF（Verifiable Delay Function）ベースのバッチ処理 | ✅ 完成 |
| **🔌 プラグインフレームワーク** | CBORを使用した動的プロトコル拡張 | ✅ 完成 |
| **🔋 低電力モード** | モバイル環境向けバッテリー最適化 | ✅ 完成 |
| **📊 OpenTelemetry** | OTLP経由のトレーシング・メトリクス（Jaeger/Tempo対応） | ✅ 完成 |
| **☸️ Kubernetesサポート** | Helm charts、HPA、PDB、ServiceMonitor | ✅ 完成 |

### プロキシ機能

| 機能 | 説明 | ステータス |
|------|------|----------|
| **🌐 SOCKS5プロキシ** | RFC 1928準拠、Tor互換 | ✅ 完成 |
| **🌐 HTTP CONNECT** | HTTPSトラフィック用プロキシサポート | ✅ 完成 |
| **🔐 Pure Go TLS** | C/C++依存ゼロのTLS実装 | ✅ 完成 |
| **🦊 ブラウザ統合** | Firefox、Chrome、curl、wget互換 | ✅ 完成 |

---

## アーキテクチャ

NyxNetは、明確な責務分離を持つレイヤードアーキテクチャに従います：

```mermaid
graph TB
    subgraph "アプリケーション層"
        APP[ユーザーアプリケーション]
        BROWSER[Webブラウザ]
        MOBILE[モバイルアプリ]
    end
    
    subgraph "SDKレイヤー"
        SDK[nyx-sdk<br/>Stream API]
        WASM[nyx-sdk-wasm<br/>WebAssembly]
        FFI[nyx-mobile-ffi<br/>iOS/Android]
    end
    
    subgraph "プロキシレイヤー"
        SOCKS[SOCKS5 Proxy]
        HTTP[HTTP CONNECT]
    end
    
    subgraph "コントロールプレーン"
        DAEMON[nyx-daemon<br/>gRPC/JSON-RPC API]
        CLI[nyx-cli<br/>管理ツール]
    end
    
    subgraph "データプレーン"
        STREAM[nyx-stream<br/>Stream Manager]
        MIX[nyx-mix<br/>Sphinx Routing]
        TRANSPORT[nyx-transport<br/>QUIC Multipath]
        FEC[nyx-fec<br/>Reed-Solomon]
    end
    
    subgraph "基盤レイヤー"
        CRYPTO[nyx-crypto<br/>ML-KEM + X25519]
        CORE[nyx-core<br/>型と設定]
        TELEMETRY[nyx-telemetry<br/>メトリクスとトレーシング]
    end
    
    APP --> SDK
    BROWSER --> SOCKS
    BROWSER --> HTTP
    MOBILE --> FFI
    
    SDK --> DAEMON
    WASM --> DAEMON
    FFI --> DAEMON
    SOCKS --> DAEMON
    HTTP --> DAEMON
    CLI --> DAEMON
    
    DAEMON --> STREAM
    DAEMON --> MIX
    
    STREAM --> MIX
    MIX --> TRANSPORT
    MIX --> FEC
    TRANSPORT --> FEC
    
    STREAM --> CRYPTO
    MIX --> CRYPTO
    TRANSPORT --> CORE
    FEC --> CORE
    
    DAEMON --> TELEMETRY
    STREAM --> TELEMETRY
    
    style APP fill:#e1f5ff
    style BROWSER fill:#e1f5ff
    style MOBILE fill:#e1f5ff
    style CRYPTO fill:#ffe1e1
    style CORE fill:#ffe1e1
    style DAEMON fill:#fff4e1
    style MIX fill:#e8f5e1
```

### 主要コンポーネント

| コンポーネント | 説明 | 主な機能 |
|---------------|------|----------|
| **nyx-core** | コアユーティリティ、型、設定 | エラーハンドリング、設定ホットリロード、i18n |
| **nyx-crypto** | ポスト量子暗号 | ML-KEM-768、X25519、ChaCha20-Poly1305、BLAKE3 |
| **nyx-transport** | QUICベーストランスポート層 | マルチパスルーティング、NAT Traversal、UDPデータグラム |
| **nyx-mix** | ミックスネットワーク実装 | Sphinxパケット形式、3ホップルーティング、カバートラフィック |
| **nyx-fec** | 前方誤り訂正 | Reed-Solomon符号、適応的冗長性 |
| **nyx-stream** | ストリーム管理 | 多重化、フロー制御、再接続 |
| **nyx-daemon** | コントロールプレーンデーモン | gRPC API(20以上のRPC)、JSON-RPC 2.0、ノード管理 |
| **nyx-sdk** | クライアントSDK | 高レベルAPI、async/await、エラーリカバリ |
| **nyx-cli** | コマンドラインツール | ノード制御、ストリーム検査、診断 |
| **nyx-http-proxy** | SOCKS5/HTTPプロキシ | Tor互換、pure Go TLS、ブラウザ統合 |

---

## クイックスタート

### 前提条件

- **Rust**: 1.70.0以上（推奨: 1.75以上）
- **Cargo**: 1.70.0以上
- **Go**: 1.21以上（HTTPプロキシ用）
- **Git**: 2.30以上

### ソースからビルド

```bash
# リポジトリをクローン
git clone https://github.com/SeleniaProject/Nyx.git
cd Nyx

# Rustワークスペースをビルド（リリースモード）
cargo build --release

# Go HTTPプロキシをビルド
cd nyx-http-proxy
go build -o nyx-http-proxy
cd ..
```

### デーモンを実行

```bash
# NyxNetデーモンを起動
./target/release/nyx-daemon --config nyx.toml

# 別のターミナルで状態確認
./target/release/nyx-cli status
```

### プロキシを起動

```bash
# localhost:9050でSOCKS5プロキシを起動
./nyx-http-proxy/nyx-http-proxy --socks-port 9050
```

---

## インストール

### ソースから

```bash
# システムワイドにインストール（sudo/admin権限が必要）
cargo install --path nyx-daemon
cargo install --path nyx-cli

# またはtarget/release/から直接バイナリを使用
```

### Dockerを使用

```bash
# Dockerイメージをビルド
docker build -t nyxnet:latest .

# デーモンを実行
docker run -d --name nyx-daemon \
  -p 9050:9050 \
  -v $(pwd)/nyx.toml:/etc/nyx/nyx.toml \
  nyxnet:latest
```

### Kubernetes（Helm）を使用

```bash
# Helmチャートをインストール
helm install nyx ./charts/nyx \
  --namespace nyx-system \
  --create-namespace

# デプロイ状態を確認
kubectl get pods -n nyx-system
```

---

## 使用例

### 通信フロー

```mermaid
sequenceDiagram
    participant App as アプリケーション
    participant SDK as nyx-sdk
    participant Daemon as nyx-daemon
    participant Mix1 as ミックスノード 1
    participant Mix2 as ミックスノード 2
    participant Mix3 as ミックスノード 3
    participant Dest as 宛先
    
    App->>SDK: create_stream(config)
    SDK->>Daemon: gRPC: CreateStream
    Daemon->>Daemon: Sphinxパケット生成
    
    Note over Daemon,Mix1: レイヤー3暗号化
    Daemon->>Mix1: 暗号化パケット (レイヤー3,2,1)
    
    Note over Mix1,Mix2: レイヤー2暗号化
    Mix1->>Mix1: レイヤー3復号化
    Mix1->>Mix2: 暗号化パケット (レイヤー2,1)
    
    Note over Mix2,Mix3: レイヤー1暗号化
    Mix2->>Mix2: レイヤー2復号化
    Mix2->>Mix3: 暗号化パケット (レイヤー1)
    
    Mix3->>Mix3: レイヤー1復号化
    Mix3->>Dest: 宛先に転送
    
    Dest-->>Mix3: レスポンス
    Mix3-->>Mix2: 暗号化レスポンス
    Mix2-->>Mix1: 暗号化レスポンス
    Mix1-->>Daemon: 暗号化レスポンス
    Daemon-->>SDK: 復号化データ
    SDK-->>App: アプリケーションデータ
```

### SDKを使用（Rust）

```rust
use nyx_sdk::{DaemonClient, StreamConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // ローカルデーモンに接続
    let client = DaemonClient::connect("http://localhost:50051").await?;
    
    // 宛先への匿名ストリームを作成
    let config = StreamConfig {
        destination: "example.com:443".to_string(),
        multipath: true,
        low_power: false,
    };
    
    let mut stream = client.create_stream(config).await?;
    
    // 匿名ネットワーク経由でデータを送信
    stream.write_all(b"GET / HTTP/1.1\r\nHost: example.com\r\n\r\n").await?;
    
    // レスポンスを読み取り
    let mut buffer = vec![0u8; 4096];
    let n = stream.read(&mut buffer).await?;
    println!("{}バイト受信", n);
    
    Ok(())
}
```

### curlでSOCKS5プロキシを使用

```bash
# curlをNyxNet SOCKS5プロキシを使用するように設定
curl --socks5 localhost:9050 https://example.com

# または環境変数を設定
export ALL_PROXY=socks5://localhost:9050
curl https://example.com
```

### Firefoxで使用

1. Firefox設定 → ネットワーク設定を開く
2. 「手動でプロキシを設定する」を選択
3. SOCKSホスト: `localhost`、ポート: `9050`
4. 「SOCKS v5」を選択
5. 「SOCKS v5を使用するときはDNSもプロキシを使用する」にチェック

---

## ドキュメント

包括的なドキュメントは`docs/`ディレクトリにあります：

- [**プロジェクト概要**](docs/01_PROJECT_OVERVIEW.md) - 目標、ユースケース、コンプライアンスレベル
- [**システムアーキテクチャ**](docs/02_SYSTEM_ARCHITECTURE.md) - 詳細なアーキテクチャ設計
- [**主要機能**](docs/03_MAJOR_FEATURES.md) - 詳細な機能説明
- [**APIリファレンス**](docs/04_API_REFERENCE.md) - gRPC/JSON-RPC APIドキュメント
- [**開発セットアップ**](docs/05_DEVELOPMENT_SETUP.md) - 環境セットアップと貢献ガイド

### Torとの比較

Torネットワークとの詳細な比較については、[Tor比較ガイド](docs/ACTUAL_TOR_COMPARISON.md)を参照してください。

### 形式検証

NyxNetは`formal/`ディレクトリにTLA+仕様による形式検証を含んでいます。詳細は[検証ステータス](formal/FINAL_VERIFICATION_STATUS.md)を参照してください。

---

## パフォーマンス

### ベンチマーク

```mermaid
graph LR
    subgraph "パフォーマンス指標"
        A[ハンドシェイク<br/>~2.5ms] --> B[パケット処理<br/>~150µs]
        B --> C[スループット<br/>500 Mbps]
        C --> D[レイテンシ<br/>+80-120ms]
    end
    
    style A fill:#90EE90
    style B fill:#90EE90
    style C fill:#87CEEB
    style D fill:#FFD700
```

NyxNetは強力なセキュリティ保証と競争力のあるパフォーマンスを実現しています：

| 指標 | 値 | 詳細 |
|------|------|------|
| **ハンドシェイク** | 約2.5ms | ハイブリッドPQハンドシェイク（ML-KEM-768 + X25519） |
| **パケット処理** | 約150µs | パケットあたり（3ホップSphinxルーティング） |
| **スループット** | 最大500 Mbps | FEC有効時のストリームあたり |
| **レイテンシ** | +80-120ms | 直接接続と比較（3ホップミックスネットワーク） |
| **メモリ** | 約50MB | デーモンインスタンスあたり（標準的なワークロード） |
| **CPU** | <5% | 最新CPU上でのストリームあたり |

ローカルでベンチマークを実行：

```bash
# 暗号ベンチマーク
cargo bench -p nyx-crypto

# コアパフォーマンスベンチマーク
cargo bench -p nyx-core --bench security_scalability_benchmark

# 完全統合ベンチマーク
cargo bench -p tests --bench integration_benchmark
```

### Torとの比較

```mermaid
graph TB
    subgraph "セキュリティ機能"
        N1[NyxNet<br/>ML-KEM-768 ✅]
        T1[Tor<br/>PQなし ❌]
    end
    
    subgraph "ルーティング"
        N2[NyxNet<br/>マルチパス ✅]
        T2[Tor<br/>シングルパス ❌]
    end
    
    subgraph "モバイル"
        N3[NyxNet<br/>低電力 ✅]
        T3[Tor<br/>限定的 ⚠️]
    end
    
    subgraph "検証"
        N4[NyxNet<br/>TLA+ 仕様 ✅]
        T4[Tor<br/>部分的 ⚠️]
    end
    
    style N1 fill:#90EE90
    style N2 fill:#90EE90
    style N3 fill:#90EE90
    style N4 fill:#90EE90
    style T1 fill:#FFB6C6
    style T2 fill:#FFB6C6
    style T3 fill:#FFD700
    style T4 fill:#FFD700
```

| 指標 | NyxNet | Tor |
|------|--------|-----|
| **ポスト量子セキュリティ** | ✅ ML-KEM-768（NIST標準化） | ❌ 未実装 |
| **マルチパスサポート** | ✅ 自動フェイルオーバー付きネイティブサポート | ❌ シングルパスのみ |
| **モバイル最適化** | ✅ 低電力モード、バッテリー対応 | ⚠️ 限定的な最適化 |
| **形式検証** | ✅ TLA+仕様 | ⚠️ 部分的なカバレッジ |
| **トランスポート** | ✅ QUIC（UDP） | ⚠️ TCPのみ |
| **FEC** | ✅ 適応的Reed-Solomon | ❌ FECなし |
| **言語** | ✅ Pure Rust（メモリ安全） | ⚠️ C（メモリ非安全） |

---

## セキュリティ

### 暗号スタック

```mermaid
graph TD
    subgraph "鍵交換レイヤー"
        KEM[ML-KEM-768<br/>NIST FIPS 203]
        ECDH[X25519<br/>Curve25519]
        KEM -.ハイブリッド.-> HYBRID[ハイブリッド KEM]
        ECDH -.ハイブリッド.-> HYBRID
    end
    
    subgraph "暗号化レイヤー"
        HYBRID --> KDF[HKDF-SHA256<br/>鍵導出]
        KDF --> AEAD[ChaCha20-Poly1305<br/>AEAD暗号]
    end
    
    subgraph "整合性レイヤー"
        AEAD --> HASH[BLAKE3<br/>暗号学的ハッシュ]
        HASH --> SPHINX[Sphinxパケット形式<br/>レイヤー暗号化]
    end
    
    subgraph "保護レイヤー"
        SPHINX --> BLOOM[Bloomフィルタ<br/>リプレイ保護]
        SPHINX --> TIMESTAMP[タイムスタンプナンス<br/>時間ウィンドウ]
    end
    
    style KEM fill:#FFE1E1
    style ECDH fill:#FFE1E1
    style HYBRID fill:#90EE90
    style AEAD fill:#87CEEB
    style SPHINX fill:#DDA0DD
```

### 暗号プリミティブ

| コンポーネント | アルゴリズム | 目的 | 標準 |
|-------------|------------|------|------|
| **鍵交換** | ML-KEM-768 | ポスト量子KEM | NIST FIPS 203 |
| **鍵交換** | X25519 | 古典的ECDH | RFC 7748 |
| **AEAD** | ChaCha20-Poly1305 | 認証付き暗号 | RFC 8439 |
| **ハッシュ** | BLAKE3 | 暗号学的ハッシュ | 高速、安全 |
| **KDF** | HKDF-SHA256 | 鍵導出 | RFC 5869 |
| **パケット形式** | Sphinx | ミックスネットワークルーティング | Mixnet研究 |

### セキュリティ特性

```mermaid
mindmap
  root((セキュリティ))
    匿名性
      送信者匿名性
      受信者匿名性
      関係匿名性
    機密性
      エンドツーエンド暗号化
      レイヤー暗号化
      前方秘匿性
    整合性
      メッセージ認証
      リプレイ保護
      タイムスタンプ検証
    可用性
      マルチパス耐性
      FECリカバリ
      自動フェイルオーバー
```

### セキュリティ監査

NyxNetは活発に開発中です。セキュリティ監査レポートは完了次第公開されます。

### 脆弱性の報告

セキュリティの脆弱性は以下に報告してください：**security@selenia-project.org**

セキュリティポリシーについては[SECURITY.md](SECURITY.md)を参照してください。

---

## 開発

### ビルドとテスト

```bash
# すべてのテストを実行
cargo test --workspace --release

# カバレッジ付きでテストを実行
cargo install cargo-tarpaulin
cargo tarpaulin --workspace --out Html

# リンターを実行
cargo clippy --workspace --all-features -- -D warnings

# コードフォーマット
cargo fmt --all -- --check
```

### プロジェクト構造

```mermaid
graph TD
    subgraph "コアライブラリ"
        CORE[nyx-core<br/>コア型と設定]
        CRYPTO[nyx-crypto<br/>PQ暗号]
    end
    
    subgraph "ネットワーク層"
        TRANSPORT[nyx-transport<br/>QUICトランスポート]
        MIX[nyx-mix<br/>ミックスネットワーク]
        FEC[nyx-fec<br/>誤り訂正]
        STREAM[nyx-stream<br/>ストリームマネージャ]
    end
    
    subgraph "制御層"
        DAEMON[nyx-daemon<br/>コントロールプレーン]
        CONTROL[nyx-control<br/>ノード制御]
        TELEMETRY[nyx-telemetry<br/>可観測性]
    end
    
    subgraph "クライアント層"
        SDK[nyx-sdk<br/>Rust SDK]
        WASM[nyx-sdk-wasm<br/>WebAssembly]
        FFI[nyx-mobile-ffi<br/>モバイル FFI]
        CLI[nyx-cli<br/>CLIツール]
    end
    
    subgraph "プロキシ層"
        PROXY[nyx-http-proxy<br/>SOCKS5/HTTP]
        PUSH[nyx-push-proxy<br/>Push通知]
    end
    
    subgraph "サポート"
        DOCS[docs/<br/>ドキュメント]
        FORMAL[formal/<br/>TLA+ 仕様]
        TESTS[tests/<br/>統合テスト]
        EXAMPLES[examples/<br/>使用例]
    end
    
    CORE --> CRYPTO
    CRYPTO --> TRANSPORT
    CRYPTO --> MIX
    TRANSPORT --> FEC
    MIX --> STREAM
    STREAM --> DAEMON
    DAEMON --> SDK
    DAEMON --> CLI
    DAEMON --> PROXY
    DAEMON --> TELEMETRY
    
    style CORE fill:#FFE1E1
    style CRYPTO fill:#FFE1E1
    style DAEMON fill:#FFD700
    style SDK fill:#87CEEB
    style DOCS fill:#DDA0DD
```

**ディレクトリレイアウト:**

```
NyxNet/
├── nyx-core/          # コアユーティリティと型
├── nyx-crypto/        # 暗号プリミティブ
├── nyx-transport/     # QUICトランスポート層
├── nyx-mix/           # ミックスネットワーク実装
├── nyx-fec/           # 前方誤り訂正
├── nyx-stream/        # ストリーム管理
├── nyx-daemon/        # コントロールプレーンデーモン
├── nyx-sdk/           # クライアントSDK
├── nyx-cli/           # CLIツール
├── nyx-http-proxy/    # SOCKS5/HTTPプロキシ（Go）
├── docs/              # ドキュメント
├── formal/            # TLA+仕様
├── tests/             # 統合テスト
└── examples/          # 使用例
```

### 貢献

貢献を歓迎します！ガイドラインについては[CONTRIBUTING.md](CONTRIBUTING.md)を参照してください。

1. リポジトリをフォーク
2. 機能ブランチを作成（`git checkout -b feature/amazing-feature`）
3. 変更をコミット（`git commit -m 'Add amazing feature'`）
4. ブランチにプッシュ（`git push origin feature/amazing-feature`）
5. プルリクエストを開く

### 行動規範

このプロジェクトは[行動規範](CODE_OF_CONDUCT.md)に従います。参加することにより、このコードを守ることが期待されます。

---

## ライセンス

NyxNetはデュアルライセンスです：

- **MITライセンス**（[LICENSE-MIT](LICENSE-MIT)またはhttp://opensource.org/licenses/MIT）
- **Apache License, Version 2.0**（[LICENSE-APACHE](LICENSE-APACHE)またはhttp://www.apache.org/licenses/LICENSE-2.0）

目的に応じていずれかのライセンスを選択できます。

---

## 謝辞

NyxNetは以下の研究とプロトコルに基づいて構築されています：

- **Torプロジェクト**: オニオンルーティングの概念
- **Mixnet研究**: Sphinxパケット形式、Loopixタイミング戦略
- **NIST PQC**: ML-KEM標準化
- **Rustコミュニティ**: 優れた暗号ライブラリ

---

## 連絡先

- **プロジェクトウェブサイト**: https://selenia-project.org
- **GitHub**: https://github.com/SeleniaProject/Nyx
- **Email**: contact@selenia-project.org

---

**Selenia Projectチームが❤️を込めて構築**
