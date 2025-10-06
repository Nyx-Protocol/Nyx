# NyxNet

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Rust](https://img.shields.io/badge/rust-1.70%2B-orange.svg)](https://www.rust-lang.org/)
[![Go](https://img.shields.io/badge/go-1.21%2B-00ADD8.svg)](https://go.dev/)

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

### コア機能

- **🔐 ポスト量子暗号**: ML-KEM-768（NIST標準化済み）とX25519を使用したハイブリッドハンドシェイク
- **🧅 Sphinxオニオンルーティング**: レイヤー暗号化による3ホップミックスネットワークによるトラフィック匿名化
- **⚡ QUICトランスポート**: UDPデータグラム上の低レイテンシマルチパストランスポート
- **🛡️ Forward Error Correction (FEC)**: Reed-Solomon符号を使用した適応的冗長性制御
- **🎛️ gRPC制御API**: ノード管理とストリーム制御のための20以上のRPC
- **🔒 リプレイ攻撃保護**: Bloomフィルタを使用したタイムスタンプベースのナンス検証

### 高度な機能

- **🛤️ マルチパスルーティング**: 複数経路での同時通信と自動フェイルオーバー
- **👻 カバートラフィック**: ポアソン分布に基づく適応的ダミーパケット生成
- **🌐 NAT Traversal**: ICE Lite実装によるSTUNサポート
- **🔄 ホット設定リロード**: ダウンタイムなしの動的設定更新
- **🌍 国際化（i18n）**: Fluent形式のメッセージローカライゼーション

### 完全機能

- **⚙️ cMix統合**: VDF（Verifiable Delay Function）ベースのバッチ処理
- **🔌 プラグインフレームワーク**: CBORを使用した動的プロトコル拡張
- **🔋 低電力モード**: モバイル環境向けバッテリー最適化
- **📊 OpenTelemetry統合**: OTLP経由のトレーシング・メトリクス（Jaeger/Tempo対応）
- **☸️ Kubernetesサポート**: Helm charts、HPA、PDB、ServiceMonitor対応

### プロキシ機能

- **🌐 Tor互換プロキシ**: SOCKS5（RFC 1928）とHTTP CONNECTプロキシ（Go実装）
- **🌐 ブラウザ統合**: Firefox、Chrome、curl、wgetとの互換性
- **🔐 Pure Go TLS**: C/C++依存ゼロのTLS実装

---

## アーキテクチャ

NyxNetは、明確な責務分離を持つレイヤードアーキテクチャに従います：

```
┌─────────────────────────────────────────────────────────┐
│              アプリケーション層                          │
│  (ユーザーアプリ、ブラウザ拡張、モバイルアプリ)          │
└───────────────────┬─────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────────────────┐
│              SDKレイヤー (nyx-sdk)                      │
│  - Stream API                                           │
│  - Daemonクライアント (gRPC/JSON-RPC)                   │
└───────────────────┬─────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────────────────┐
│           コントロールプレーン (nyx-daemon)             │
│  - gRPCサービス (20以上のRPC)                           │
│  - JSON-RPC 2.0 (IPC)                                   │
└─────┬─────┬─────┬─────┬─────┬─────────────────────────┘
      │     │     │     │     │
      ▼     ▼     ▼     ▼     ▼
   Stream  Mix  Trans  Crypto  Telemetry
   Manager Network port  Layer   Layer
   (nyx-  (nyx- (nyx-  (nyx-   (nyx-
   stream) mix)  trans crypto) telemetry)
                 port)
```

### 主要コンポーネント

- **nyx-core**: コアユーティリティ、型、設定、エラーハンドリング
- **nyx-crypto**: ポスト量子暗号（ML-KEM-768、X25519、ChaCha20-Poly1305）
- **nyx-transport**: マルチパス対応のQUICベーストランスポート層
- **nyx-mix**: Sphinxパケット形式を使用したミックスネットワーク実装
- **nyx-fec**: Reed-Solomon符号を使用した前方誤り訂正
- **nyx-stream**: ストリーム管理と多重化
- **nyx-daemon**: gRPC/JSON-RPC APIを持つコントロールプレーンデーモン
- **nyx-sdk**: アプリケーション統合用クライアントSDK
- **nyx-cli**: コマンドラインインターフェースツール
- **nyx-http-proxy**: SOCKS5/HTTP CONNECTプロキシ（Go実装）

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

NyxNetは強力なセキュリティ保証と競争力のあるパフォーマンスを実現しています：

- **ハンドシェイク**: 約2.5ms（ハイブリッドPQハンドシェイク）
- **パケット処理**: パケットあたり約150µs（3ホップSphinx）
- **スループット**: ストリームあたり最大500 Mbps
- **レイテンシ**: 直接接続に対して+80-120ms（3ホップ）

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

| 指標 | NyxNet | Tor |
|------|--------|-----|
| ポスト量子セキュリティ | ✅ ML-KEM-768 | ❌ 未対応 |
| マルチパスサポート | ✅ ネイティブ | ❌ なし |
| モバイル最適化 | ✅ 低電力モード | ⚠️ 限定的 |
| 形式検証 | ✅ TLA+仕様 | ⚠️ 部分的 |

---

## セキュリティ

### 暗号プリミティブ

- **鍵交換**: ML-KEM-768（NIST FIPS 203）+ X25519（ハイブリッド）
- **AEAD**: ChaCha20-Poly1305
- **ハッシュ**: BLAKE3
- **KDF**: HKDF-SHA256
- **パケット形式**: Sphinxミックスネットワーク形式

### セキュリティ監査

NyxNetは活発に開発中です。セキュリティ監査レポートは完了次第公開されます。

### 脆弱性の報告

セキュリティの脆弱性は以下に報告してください：security@selenia-project.org

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