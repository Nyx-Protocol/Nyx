# NyxNet 用語集

**最終更新**: 2025年10月7日  
**対象バージョン**: v1.0

---

## 概要

NyxNetプロジェクトで使用される技術用語、略語、概念の定義集です。アルファベット順、日本語五十音順で整理しています。

---

## アルファベット

### A

#### AEAD (Authenticated Encryption with Associated Data)
**読み**: エーイーエーディー  
**日本語**: 認証付き暗号  
**説明**: 暗号化と認証を同時に提供する暗号方式。NyxNetでは`ChaCha20Poly1305`を使用。改ざん検出機能を持つ。

#### ASan (Address Sanitizer)
**読み**: アドレスサニタイザー  
**説明**: メモリエラー（バッファオーバーフロー、Use-After-Freeなど）を検出する動的解析ツール。

---

### B

#### BIKE (Bit Flipping Key Encapsulation)
**読み**: バイク  
**説明**: ポスト量子暗号の一種（QC-MDPC符号ベース）。NyxNetでは非推奨（ML-KEMを推奨）。

#### Bloom Filter
**読み**: ブルームフィルタ  
**日本語**: ブルームフィルタ  
**説明**: 確率的データ構造。リプレイ攻撃検出に使用。偽陽性あり（偽陰性なし）。

---

### C

#### CBOR (Concise Binary Object Representation)
**読み**: シーボー  
**説明**: バイナリ形式のデータシリアライゼーション。JSONより高効率。プラグインシステムで使用。

#### ChaCha20Poly1305
**読み**: チャチャニジュウポリワンサンゼロゴ  
**説明**: AEAD暗号アルゴリズム。ChaCha20（ストリーム暗号）+ Poly1305（MAC）。ソフトウェア実装が高速。

#### cMix
**読み**: シーミックス  
**説明**: VDF（Verifiable Delay Function）ベースのミックスネットワークプロトコル。バッチ処理により高スループット実現。

#### Cover Traffic
**読み**: カバートラフィック  
**日本語**: カバートラフィック、ダミートラフィック  
**説明**: トラフィック分析対策として送信される偽トラフィック。実トラフィックと区別不可能。

#### Criterion
**読み**: クライテリオン  
**説明**: Rustベンチマークフレームワーク。統計的分析、HTML形式レポート生成機能を持つ。

---

### D

#### DashMap
**読み**: ダッシュマップ  
**説明**: 並行HashMap（Concurrent HashMap）。ロックフリー設計で高性能。

#### DHT (Distributed Hash Table)
**読み**: ディーエイチティー  
**日本語**: 分散ハッシュテーブル  
**説明**: P2Pネットワークでのピア発見に使用。NyxNetではKademlia DHTを実装。

---

### E

#### ECDH (Elliptic Curve Diffie-Hellman)
**読み**: イーシーディーエイチ  
**日本語**: 楕円曲線ディフィー・ヘルマン  
**説明**: 楕円曲線暗号を使用した鍵交換プロトコル。NyxNetではX25519を使用。

---

### F

#### FEC (Forward Error Correction)
**読み**: エフイーシー  
**日本語**: 前方誤り訂正  
**説明**: データ送信前に冗長性を追加し、パケットロス時の復元を可能にする技術。Reed-Solomon符号使用。

#### FFI (Foreign Function Interface)
**読み**: エフエフアイ  
**説明**: 異なるプログラミング言語間の関数呼び出しインターフェース。モバイルアプリ向けにC-ABI互換FFI提供。

---

### G

#### gRPC
**読み**: ジーアールピーシー  
**説明**: Googleが開発したRPCフレームワーク。Protocol Buffers使用。NyxNetはPure Rust実装（TLSなし）。

---

### H

#### HKDF (HMAC-based Key Derivation Function)
**読み**: エイチケーディーエフ  
**日本語**: HMACベース鍵導出関数  
**説明**: 共有秘密から暗号学的に安全な鍵を導出。RFC 5869準拠。

#### HPA (Horizontal Pod Autoscaler)
**読み**: エイチピーエー  
**説明**: Kubernetes機能。負荷に応じてPod数を自動調整。

---

### I

#### ICE (Interactive Connectivity Establishment)
**読み**: アイス  
**説明**: NAT越えのための接続確立プロトコル。NyxNetではICE Lite実装。

---

### J

#### JSON-RPC
**読み**: ジェイソンアールピーシー  
**説明**: JSONフォーマットのRPCプロトコル。NyxNet CLIとデーモン間通信に使用（IPC経由）。

---

### K

#### Kademlia
**読み**: カデムリア  
**説明**: P2P分散ハッシュテーブルプロトコル。XORメトリックによる効率的ピア発見。

#### KDF (Key Derivation Function)
**読み**: ケーディーエフ  
**日本語**: 鍵導出関数  
**説明**: パスワードや共有秘密から暗号鍵を生成する関数。HKDFなど。

#### KEM (Key Encapsulation Mechanism)
**読み**: ケーイーエム  
**日本語**: 鍵カプセル化メカニズム  
**説明**: 公開鍵暗号方式の一種。共有秘密を公開鍵で暗号化（カプセル化）。ML-KEMなど。

---

### L

#### LARMix (Latency-Aware Routing Mix)
**読み**: ラーミックス  
**説明**: レイテンシを考慮した経路選択アルゴリム。低遅延と匿名性を両立。

#### libFuzzer
**読み**: リブファザー  
**説明**: LLVMプロジェクトのカバレッジ誘導ファザー。cargo-fuzzで使用。

---

### M

#### MAC (Message Authentication Code)
**読み**: マック  
**日本語**: メッセージ認証コード  
**説明**: メッセージの完全性と真正性を検証する暗号学的タグ。Poly1305など。

#### ML-KEM (Module-Lattice-Based Key Encapsulation Mechanism)
**読み**: エムエルケーイーエム  
**説明**: NIST標準化ポスト量子暗号（旧Kyber）。格子暗号ベース。NyxNetではML-KEM-768使用（Security Level 3）。

#### MSan (Memory Sanitizer)
**読み**: メモリサニタイザー  
**説明**: 未初期化メモリ使用を検出する動的解析ツール。

---

### N

#### NAT (Network Address Translation)
**読み**: ナット  
**日本語**: ネットワークアドレス変換  
**説明**: プライベートIPとグローバルIPの変換技術。NAT越え（Traversal）が必要。

#### Nonce
**読み**: ノンス  
**日本語**: ナンス、使い捨て乱数  
**説明**: 一度だけ使用される乱数。リプレイ攻撃防止に使用。

---

### O

#### Onion Routing
**読み**: オニオンルーティング  
**日本語**: オニオンルーティング、玉ねぎルーティング  
**説明**: 複数レイヤーの暗号化により匿名性を実現する技術。Torで使用。NyxNetはSphinx方式。

#### OTLP (OpenTelemetry Protocol)
**読み**: オーティーエルピー  
**説明**: OpenTelemetryの標準プロトコル。トレーシング・メトリクスデータ送信に使用。

---

### P

#### PDB (Pod Disruption Budget)
**読み**: ピーディービー  
**説明**: Kubernetes機能。ローリング更新時の最小Pod数保証。

#### Proptest
**読み**: プロップテスト  
**説明**: Rustプロパティベーステストライブラリ。ランダムテストケース生成。

---

### Q

#### QUIC
**読み**: クイック  
**説明**: UDP上の多重化トランスポートプロトコル。低レイテンシ、ヘッドオブラインブロッキング回避。

---

### R

#### Reed-Solomon
**読み**: リードソロモン  
**日本語**: リード・ソロモン符号  
**説明**: 誤り訂正符号。CD、DVDでも使用される実績ある技術。

#### RPC (Remote Procedure Call)
**読み**: アールピーシー  
**日本語**: リモートプロシージャコール  
**説明**: ネットワーク越しの関数呼び出し。gRPC、JSON-RPCなど。

---

### S

#### Sphinx
**読み**: スフィンクス  
**説明**: ミックスネットワーク用暗号化方式。レイヤードオニオン暗号化の一種。コンパクトで証明可能なセキュリティ。

#### SOCKS5
**読み**: ソックスファイブ  
**説明**: プロキシプロトコル。RFC 1928準拠。Tor互換。

#### STUN (Session Traversal Utilities for NAT)
**読み**: スタン  
**説明**: NAT越えのためのプロトコル。公開IPアドレス発見に使用。

---

### T

#### TLA+ (Temporal Logic of Actions Plus)
**読み**: ティーエルエープラス  
**説明**: 形式仕様言語。分散システムのプロトコル検証に使用。TLC Model Checkerで検証。

#### TSan (Thread Sanitizer)
**読み**: スレッドサニタイザー  
**説明**: データ競合を検出する動的解析ツール。

---

### V

#### VDF (Verifiable Delay Function)
**読み**: ブイディーエフ  
**日本語**: 検証可能遅延関数  
**説明**: 計算に時間がかかるが検証は高速な関数。cMixで使用。

---

### W

#### WASM (WebAssembly)
**読み**: ワズム  
**説明**: ブラウザで動作するバイナリ形式。nyx-sdk-wasmで提供。

---

### X

#### X25519
**読み**: エックスニーゴーニーゴー  
**説明**: Curve25519楕円曲線を使用したDiffie-Hellman鍵交換。高速で実績あり。

---

## 日本語五十音順

### あ行

#### 暗号学的ハッシュ関数
**英語**: Cryptographic Hash Function  
**説明**: 任意長データから固定長ハッシュ値を生成する一方向関数。SHA-256、BLAKE3など。

#### 匿名性 (Anonymity)
**説明**: 通信者の身元が特定されない性質。NyxNetの主目的。

---

### か行

#### カプセル化 (Encapsulation)
**説明**: 共有秘密を公開鍵で暗号化すること。KEMの核心操作。

#### 鍵交換 (Key Exchange)
**説明**: 通信相手と安全に共有秘密を確立すること。Diffie-Hellman、KEMなど。

#### 鍵導出 (Key Derivation)
**説明**: 1つの秘密から複数の暗号鍵を生成すること。HKDF使用。

#### 鍵ローテーション (Key Rotation)
**説明**: 定期的に鍵を更新すること。セキュリティ向上のため。

#### 格子暗号 (Lattice-based Cryptography)
**説明**: 格子問題の困難性に基づく暗号。ポスト量子暗号の主流。ML-KEMなど。

---

### さ行

#### 前方秘匿性 (Forward Secrecy)
**英語**: Forward Secrecy / Perfect Forward Secrecy (PFS)  
**説明**: 長期鍵が漏洩しても過去の通信は安全な性質。一時鍵使用で実現。

#### ストリーム暗号 (Stream Cipher)
**説明**: 平文をビット/バイト単位で暗号化する方式。ChaCha20など。

---

### た行

#### タイムスタンプ (Timestamp)
**説明**: 時刻情報。リプレイ攻撃防止のためナンスに含める。

#### トラフィック分析 (Traffic Analysis)
**説明**: 暗号化された通信のメタデータ（送信時刻、サイズなど）から情報を推測する攻撃。

---

### は行

#### ハイブリッド暗号 (Hybrid Cryptography)
**説明**: 複数の暗号方式を組み合わせる手法。NyxNetではML-KEM + X25519。

#### ハンドシェイク (Handshake)
**説明**: 通信開始時の鍵交換と認証プロセス。

#### ピア (Peer)
**説明**: P2Pネットワークの参加ノード。

---

### ま行

#### ミックスネットワーク (Mix Network)
**説明**: 複数の中継ノード（ミックス）を経由してトラフィックを匿名化するネットワーク。

#### メモリ安全性 (Memory Safety)
**説明**: メモリエラー（バッファオーバーフロー等）がない性質。Rustの主要特徴。

---

### や行

#### 誤り訂正 (Error Correction)
**説明**: データ破損を検出・修復する技術。Reed-Solomon符号など。

---

### ら行

#### リプレイ攻撃 (Replay Attack)
**説明**: 過去の正当な通信を再送する攻撃。タイムスタンプナンスで防御。

#### レイテンシ (Latency)
**説明**: 遅延時間。パケット送信から受信までの時間。

---

## 略語一覧

| 略語 | 正式名称 | 日本語 |
|------|---------|--------|
| AEAD | Authenticated Encryption with Associated Data | 認証付き暗号 |
| API | Application Programming Interface | アプリケーションプログラミングインターフェース |
| ASan | Address Sanitizer | アドレスサニタイザー |
| CDN | Content Delivery Network | コンテンツ配信ネットワーク |
| CI/CD | Continuous Integration / Continuous Delivery | 継続的インテグレーション/デリバリー |
| CLI | Command Line Interface | コマンドラインインターフェース |
| CPU | Central Processing Unit | 中央演算処理装置 |
| CVE | Common Vulnerabilities and Exposures | 共通脆弱性識別子 |
| DHT | Distributed Hash Table | 分散ハッシュテーブル |
| DoS | Denial of Service | サービス拒否攻撃 |
| ECDH | Elliptic Curve Diffie-Hellman | 楕円曲線ディフィー・ヘルマン |
| FEC | Forward Error Correction | 前方誤り訂正 |
| FFI | Foreign Function Interface | 外部関数インターフェース |
| HKDF | HMAC-based Key Derivation Function | HMACベース鍵導出関数 |
| HPA | Horizontal Pod Autoscaler | 水平Podオートスケーラー |
| HTTP | Hypertext Transfer Protocol | ハイパーテキスト転送プロトコル |
| ICE | Interactive Connectivity Establishment | 対話的接続確立 |
| IKM | Input Key Material | 入力鍵素材 |
| IPC | Inter-Process Communication | プロセス間通信 |
| JSON | JavaScript Object Notation | JavaScript Object Notation |
| KDF | Key Derivation Function | 鍵導出関数 |
| KEM | Key Encapsulation Mechanism | 鍵カプセル化メカニズム |
| MAC | Message Authentication Code | メッセージ認証コード |
| MSan | Memory Sanitizer | メモリサニタイザー |
| NAT | Network Address Translation | ネットワークアドレス変換 |
| NIST | National Institute of Standards and Technology | 米国国立標準技術研究所 |
| OKM | Output Key Material | 出力鍵素材 |
| OS | Operating System | オペレーティングシステム |
| OTLP | OpenTelemetry Protocol | OpenTelemetryプロトコル |
| P2P | Peer-to-Peer | ピアツーピア |
| PDB | Pod Disruption Budget | Pod中断予算 |
| PFS | Perfect Forward Secrecy | 完全前方秘匿性 |
| PRK | Pseudo-Random Key | 疑似ランダム鍵 |
| QC-MDPC | Quasi-Cyclic Moderate Density Parity Check | 準巡回中密度パリティ検査 |
| QUIC | Quick UDP Internet Connections | QUIC |
| RFC | Request for Comments | コメント募集 |
| RPC | Remote Procedure Call | リモートプロシージャコール |
| SDK | Software Development Kit | ソフトウェア開発キット |
| SHA | Secure Hash Algorithm | セキュアハッシュアルゴリズム |
| SLA | Service Level Agreement | サービスレベル合意 |
| SOCKS | Socket Secure | Socket Secure |
| STUN | Session Traversal Utilities for NAT | NAT越えセッション制御ユーティリティ |
| TCP | Transmission Control Protocol | 伝送制御プロトコル |
| TLA+ | Temporal Logic of Actions Plus | 時相論理アクション+ |
| TLS | Transport Layer Security | トランスポート層セキュリティ |
| TOML | Tom's Obvious, Minimal Language | TOML |
| TSan | Thread Sanitizer | スレッドサニタイザー |
| UDP | User Datagram Protocol | ユーザーデータグラムプロトコル |
| VDF | Verifiable Delay Function | 検証可能遅延関数 |
| WASM | WebAssembly | WebAssembly |
| WSL | Windows Subsystem for Linux | Windows Subsystem for Linux |

---

## セキュリティレベル定義

### Security Level（NIST定義）

| レベル | 量子ビット | 古典的等価 | 該当アルゴリズム |
|-------|----------|-----------|--------------|
| Level 1 | 128 | AES-128 | ML-KEM-512 |
| Level 3 | 192 | AES-192 | **ML-KEM-768** ★ |
| Level 5 | 256 | AES-256 | ML-KEM-1024 |

★ NyxNetはLevel 3（ML-KEM-768）を採用

---

## コンプライアンスレベル定義

NyxNet独自のプロトコル準拠レベル:

### Core（コア）

**必須機能**:
- ハイブリッドPQ暗号（ML-KEM-768 + X25519）
- Sphinxオニオンルーティング（3ホップ）
- QUIC Transport
- FEC（Reed-Solomon）
- gRPC API（20+ RPCs）
- リプレイ攻撃保護

### Plus（プラス）

**Core +**:
- マルチパスルーティング
- カバートラフィック（Poisson分布）
- NAT Traversal（STUN）
- 設定ホットリロード
- 国際化（i18n）

### Full（フル）

**Plus +**:
- cMix統合
- プラグインフレームワーク
- Low Power Mode
- OpenTelemetry統合
- Kubernetes完全対応

---

## 補足: 推測箇所の明示

以下の情報は既存ドキュメント・標準的定義から合理的に推測しています:

- **一部の技術用語の日本語訳**: 一般的な翻訳を採用
- **セキュリティレベルの数値**: NIST公開情報に基づく
- **略語の一部**: 標準的な業界用語を記載

正確な定義は、各種標準規格（RFC、NIST文書など）を参照してください。
