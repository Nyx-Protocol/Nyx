# NyxNet プロジェクト概要

**最終更新**: 2025年10月6日  
**バージョン**: v1.0  
**ステータス**: ✅ 完了（統合テスト進行中）

---

## 目的

NyxNetは、プライバシーファースト、ポスト量子セキュアなネットワークスタックをピュアRustで実装したプロジェクトです。匿名性とセキュリティを最優先し、量子コンピュータ時代における通信の安全性を保証します。

### 解決する課題

1. **量子コンピュータ脅威**: 既存の公開鍵暗号（RSA、ECDHなど）は量子コンピュータによって破られる可能性があります。NyxNetはML-KEM（旧Kyber）とX25519のハイブリッド暗号を採用し、量子耐性を実現します。

2. **トラフィック分析耐性**: 現代のネットワーク監視技術では、暗号化されていてもトラフィックパターンから通信内容を推測できます。NyxNetはSphinx暗号化とカバートラフィック生成により、トラフィック分析を防ぎます。

3. **信頼できるプライバシー通信**: TorやVPNは単一障害点や運営者への信頼が必要です。NyxNetは分散型ミックスネットワークアーキテクチャにより、単一の信頼点を排除します。

4. **モバイル環境での匿名性**: バッテリー制約のあるモバイルデバイスでも実用的な匿名性を提供します。Low Power ModeとPush通知統合により、電力効率と匿名性を両立します。

---

## 主要機能一覧

### コア機能（Core Compliance Level）

- **ポスト量子暗号**: ML-KEM-768（NIST標準化済み）とX25519のハイブリッドハンドシェイク
- **Sphinxオニオンルーティング**: 3ホップミックスネットワークによるトラフィック匿名化
- **QUIC Transport**: UDP datagram上の低レイテンシマルチパストランスポート
- **Forward Error Correction (FEC)**: Reed-Solomon符号による適応的冗長性制御
- **gRPC制御API**: 20以上のRPCによるノード管理、ストリーム制御
- **リプレイ攻撃保護**: タイムスタンプベースのナンス検証とbloomフィルタ

### 拡張機能（Plus Compliance Level）

- **マルチパスルーティング**: 複数経路での同時通信、自動フェイルオーバー
- **カバートラフィック**: Poisson分布に基づく適応的ダミーパケット生成
- **NAT Traversal**: ICE Lite実装によるSTUNサポート
- **設定ホットリロード**: ダウンタイムなしの動的設定更新
- **国際化（i18n）**: Fluent形式のメッセージローカライゼーション

### 完全機能（Full Compliance Level）

- **cMix統合**: VDF（Verifiable Delay Function）ベースのバッチ処理
- **プラグインフレームワーク**: CBORベースの動的プロトコル拡張
- **Low Power Mode**: モバイル環境向けバッテリー最適化
- **OpenTelemetry統合**: OTLP経由のトレーシング・メトリクス（Jaeger/Tempo対応）
- **Kubernetes対応**: Helm charts、HPA、PDB、ServiceMonitorサポート

### プロキシ機能

- **Tor互換プロキシ**: SOCKS5（RFC 1928）とHTTP CONNECTプロキシ（Go実装）
- **ブラウザ統合**: Firefox、Chrome、curl、wgetとの互換性
- **Pure Go TLS**: ゼロC/C++依存のTLS実装（crypto/tls使用）

---

## 技術スタック概要

### プログラミング言語

| 言語 | 用途 | 理由 |
|------|------|------|
| **Rust** | コアネットワークスタック | メモリ安全性、ゼロコスト抽象化、async/await |
| **Go** | HTTPプロキシ | Pure Go TLS、クロスプラットフォーム |
| **TLA+** | 形式検証 | プロトコル正当性の数学的証明 |

### 主要フレームワーク・ライブラリ

#### Rustクレート

**非同期ランタイム**
- `tokio` 1.37: 非同期I/O、マルチスレッドランタイム

**暗号化**
- `ml-kem` 0.2: ML-KEM-768（NIST標準ポスト量子暗号）
- `x25519-dalek` 2.0: 楕円曲線Diffie-Hellman
- `chacha20poly1305` 0.10: 認証付き暗号（AEAD）
- `blake3` 1.5: 高速暗号学的ハッシュ

**ネットワーク**
- `socket2` 0.6: クロスプラットフォームソケットAPI
- `tonic` 0.11: gRPCフレームワーク（Pure Rust、TLSなし）

**シリアライゼーション**
- `serde` 1.0 + `serde_json`: JSON
- `ciborium` 0.2: CBOR（Concise Binary Object Representation）
- `toml` 0.7: 設定ファイル

**テスト・ベンチマーク**
- `criterion` 0.5: 統計的ベンチマークフレームワーク
- `proptest` 1.0: プロパティベーステスト

#### Goパッケージ

- `crypto/tls`: Pure Go TLS実装
- Standard library: `net`, `io`, `context` など

### データベース・ストレージ

- **インメモリ**: `DashMap`（並行HashMap）による高速ピアキャッシュ
- **永続化**: TOML設定ファイル、将来的にはBolt DBを検討

### クラウド・デプロイメント

- **コンテナ**: Docker、multi-stage build
- **オーケストレーション**: Kubernetes（Helm charts提供）
- **CI/CD**: GitHub Actions（18ワークフロー）
- **監視**: Prometheus、OpenTelemetry、Grafana

### 開発ツール

- **ビルドシステム**: Cargo（Rustワークスペース）、Go modules
- **リンター**: Clippy、cargo-audit、go vet
- **フォーマッタ**: rustfmt、gofmt
- **ファジング**: cargo-fuzz（libFuzzer）

---

## ディレクトリ構成

```
NyxNet/
├── nyx-core/              # コアユーティリティ、型定義、設定
│   ├── src/
│   │   ├── config.rs      # 設定ロード・バリデーション
│   │   ├── types.rs       # 基本型（ConnectionId、StreamIdなど）
│   │   ├── error.rs       # エラー型定義
│   │   ├── security.rs    # セキュリティポリシー
│   │   └── i18n.rs        # 国際化サポート
│   └── Cargo.toml
│
├── nyx-crypto/            # 暗号化プリミティブ
│   ├── src/
│   │   ├── hybrid_handshake.rs  # ML-KEM + X25519ハイブリッド
│   │   ├── aead.rs              # ChaCha20Poly1305ラッパー
│   │   ├── kdf.rs               # HKDF鍵導出
│   │   ├── session.rs           # セッション鍵管理
│   │   └── sphinx.rs            # Sphinxオニオン暗号（計画中）
│   └── Cargo.toml
│
├── nyx-transport/         # QUICデータグラムトランスポート
│   ├── src/
│   │   ├── udp.rs         # Pure Rust UDP実装
│   │   ├── nat.rs         # NAT Traversal（ICE Lite）
│   │   └── multipath.rs   # マルチパスルーティング
│   └── Cargo.toml
│
├── nyx-mix/               # ミックスネットワーク層
│   ├── src/
│   │   ├── sphinx.rs      # Sphinxオニオンルーティング
│   │   ├── cover.rs       # カバートラフィック生成
│   │   ├── larmix.rs      # レイテンシ考慮ルーティング
│   │   └── cmix.rs        # cMix統合
│   └── Cargo.toml
│
├── nyx-stream/            # ストリーム管理
│   ├── src/
│   │   ├── stream.rs      # ストリームプロトコル
│   │   ├── frame.rs       # フレーム定義
│   │   └── plugin.rs      # プラグインフレームワーク
│   └── Cargo.toml
│
├── nyx-fec/               # Forward Error Correction
│   ├── src/
│   │   ├── reed_solomon.rs  # Reed-Solomon符号
│   │   └── adaptive.rs      # 適応的冗長性制御
│   └── Cargo.toml
│
├── nyx-control/           # 制御プレーン（DHT、設定同期）
│   ├── src/
│   │   ├── dht/           # Kademlia DHT実装
│   │   ├── gossip.rs      # 設定ゴシッププロトコル
│   │   └── push.rs        # Push通知トークン管理
│   └── Cargo.toml
│
├── nyx-daemon/            # メインデーモン
│   ├── src/
│   │   └── main.rs        # gRPCサーバー、JSON-RPC、メインループ
│   └── Cargo.toml
│
├── nyx-cli/               # コマンドラインインターフェース
│   ├── src/
│   │   └── main.rs        # CLI実装
│   └── Cargo.toml
│
├── nyx-sdk/               # アプリケーションSDK
│   ├── src/
│   │   ├── client.rs      # デーモンクライアント
│   │   └── stream.rs      # ストリームAPI
│   └── Cargo.toml
│
├── nyx-sdk-wasm/          # WASM SDK（ブラウザ/Node.js）
│   └── Cargo.toml
│
├── nyx-mobile-ffi/        # モバイルFFI（iOS/Android）
│   ├── src/
│   │   └── lib.rs         # C-ABI互換インターフェース
│   └── Cargo.toml
│
├── nyx-http-proxy/        # Tor互換HTTPプロキシ（Go）
│   ├── main.go            # プロキシサーバー
│   ├── socks5.go          # SOCKS5実装
│   ├── connect.go         # HTTP CONNECT実装
│   └── mixbridge.go       # MixレイヤーIPCブリッジ
│
├── nyx-telemetry/         # テレメトリ・メトリクス
│   ├── src/
│   │   ├── prometheus.rs  # Prometheusエクスポーター
│   │   └── otlp.rs        # OpenTelemetry OTLP
│   └── Cargo.toml
│
├── nyx-conformance/       # 決定論的シミュレータ
│   └── src/               # プロパティベーステスト
│
├── tests/                 # 統合テスト
│   ├── benchmarks/        # アプリケーションレベルベンチマーク
│   └── integration/       # E2Eテスト
│
├── formal/                # 形式検証（TLA+仕様）
│   ├── NyxBasicVerification.tla
│   └── NyxCryptography.tla
│
├── docs/                  # ドキュメント
│   ├── IMPLEMENTATION_SUMMARY.md
│   ├── TOR_COMPARISON_GUIDE.md
│   └── testing/
│
├── spec/                  # プロトコル仕様
│   └── Nyx_Protocol_v1.0_Spec.md
│
├── charts/                # Helm charts
│   └── nyx/
│
├── scripts/               # ビルド・デプロイスクリプト
│
├── Cargo.toml             # Rustワークスペース定義
├── nyx.toml               # サンプル設定
├── Dockerfile             # コンテナイメージ
├── Makefile               # コンプライアンステストタスク
└── README.md              # プロジェクトREADME
```

### 役割説明

- **nyx-core**: 全クレートで共有される基本型、エラー処理、設定管理
- **nyx-crypto**: 暗号化プリミティブ（ハイブリッドPQ暗号、AEAD、KDF）
- **nyx-transport**: Pure Rust QUIC/UDPトランスポート、NAT Traversal
- **nyx-mix**: Sphinxオニオンルーティング、カバートラフィック、cMix
- **nyx-stream**: ストリームプロトコル、フレーム定義、プラグイン
- **nyx-fec**: Reed-Solomon FEC、適応的冗長性制御
- **nyx-control**: DHT、ゴシッププロトコル、Push通知管理
- **nyx-daemon**: メインサーバープロセス、gRPC/JSON-RPC API
- **nyx-cli**: コマンドラインツール（設定検証、診断、ストリーム操作）
- **nyx-sdk**: アプリケーション統合SDK（Rust）
- **nyx-sdk-wasm**: WebAssembly SDK（ブラウザ/Node.js）
- **nyx-mobile-ffi**: iOS/Android用C-ABI FFI
- **nyx-http-proxy**: SOCKS5/HTTP CONNECTプロキシ（Go、Pure TLS）
- **nyx-telemetry**: Prometheus/OTLPメトリクス・トレーシング
- **nyx-conformance**: プロトコル準拠性テストフレームワーク

---

## アーキテクチャ原則

### 1. メモリ安全性最優先

- `#![forbid(unsafe_code)]`: 全クレートでunsafe禁止
- Rustの所有権システムによるメモリ安全性保証
- ゼロコピー最適化は安全な範囲で適用

### 2. ゼロC/C++依存

- Pure Rust暗号化（`ml-kem`, `x25519-dalek`, `chacha20poly1305`）
- Pure Go TLS（`crypto/tls`）
- ring、OpenSSL、libsodiumなどのC依存を排除

### 3. モジュラー設計

- 各クレートは独立してテスト可能
- 機能フラグによる柔軟なビルド設定
- トレイト駆動の抽象化

### 4. 設定駆動

- TOML設定ファイルによる宣言的設定
- 環境変数オーバーライド対応
- JSON Schemaバリデーション

### 5. オブザーバビリティ

- 構造化ログ（JSON形式）
- Prometheusメトリクス
- OpenTelemetryトレーシング
- ヘルスチェックエンドポイント

---

## テストカバレッジ

| カテゴリ | テスト数 | 説明 |
|---------|---------|------|
| ユニットテスト | 300+ | 各モジュールの関数レベルテスト |
| 統合テスト | 50+ | クレート間連携テスト |
| プロパティテスト | 30+ | proptest使用のランダムテスト |
| ベンチマーク | 15+ | Criterion統計的ベンチマーク |
| ファジング | 10+ targets | libFuzzer連続ファジング |
| E2Eテスト | 20+ | Kubernetes環境での実環境テスト |
| 形式検証 | 15+ specs | TLA+によるプロトコル検証 |

**合計**: 400テスト以上

---

## ライセンス

Dual License: **MIT OR Apache-2.0**

プロジェクト全体がMITライセンスまたはApache-2.0ライセンスのデュアルライセンスで提供されます。ユーザーはどちらかのライセンスを選択できます。

---

## セキュリティポリシー

脆弱性報告: `SECURITY.md`参照

- セキュリティ問題は非公開で報告（GitHub Security Advisories）
- 24時間以内に初期応答
- パッチリリース後90日間の秘密保持期間

---

## コミュニティ

- **GitHub**: [SeleniaProject/Nyx](https://github.com/SeleniaProject/Nyx)
- **Issue Tracker**: GitHub Issues
- **Contributing**: `CONTRIBUTING.md`参照
- **Code of Conduct**: `CODE_OF_CONDUCT.md`参照

---

## 補足: 推測箇所の明示

以下の情報は既存ドキュメント・コードから合理的に推測しています：

- **GitHubリポジトリURL**: READMEのバッジリンクから推測
- **コミュニティリンク**: 標準的なOSSプロジェクト構成から推測
- **将来的なストレージ**: コード内のTODOコメントから推測
