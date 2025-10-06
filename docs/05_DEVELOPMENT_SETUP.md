# NyxNet 開発環境セットアップガイド

**最終更新**: 2025年10月6日  
**対象バージョン**: v1.0  
**対応OS**: Windows 10/11, Linux (Ubuntu 20.04+), macOS (12+)

---

## 前提条件

### 必須ツール

| ツール | 最小バージョン | 推奨バージョン | 確認コマンド |
|-------|--------------|--------------|-------------|
| Rust | 1.70.0 | 1.75+ | `rustc --version` |
| Cargo | 1.70.0 | 1.75+ | `cargo --version` |
| Git | 2.30+ | 2.40+ | `git --version` |
| Go | 1.21+ | 1.23+ | `go version` |

### オプションツール（推奨）

| ツール | 用途 | インストール |
|-------|------|-------------|
| WSL2 | Windowsでのビルド・テスト | Microsoft Store |
| Docker | コンテナビルド | https://docker.com |
| TLA+ Toolbox | 形式検証 | https://lamport.azurewebsites.net/tla/toolbox.html |
| Protocol Buffers | gRPCコード生成 | 自動ダウンロード（build.rs） |

---

## セットアップ手順

### Windows環境

#### 1. Rustのインストール

```powershell
# Rust公式インストーラーをダウンロード・実行
# https://rustup.rs/
Invoke-WebRequest -Uri https://win.rustup.rs/x86_64 -OutFile rustup-init.exe
.\rustup-init.exe
```

インストール後、PowerShellを再起動して確認：

```powershell
rustc --version
cargo --version
```

#### 2. Goのインストール（HTTPプロキシ用）

```powershell
# Go公式サイトからダウンロード
# https://go.dev/dl/
# インストーラー実行後、確認
go version
```

#### 3. リポジトリクローン

```powershell
# GitHubからクローン
git clone https://github.com/SeleniaProject/Nyx.git
cd Nyx
```

#### 4. 依存関係の確認

```powershell
# Cargo依存関係チェック
cargo check

# Go依存関係ダウンロード
cd nyx-http-proxy
go mod download
cd ..
```

#### 5. ビルド

```powershell
# Rustワークスペース全体をビルド（リリースモード）
cargo build --release

# HTTPプロキシ（Go）をビルド
cd nyx-http-proxy
go build -o nyx-http-proxy.exe
cd ..
```

**ビルド成果物**:
- `target\release\nyx-daemon.exe`
- `target\release\nyx-cli.exe`
- `nyx-http-proxy\nyx-http-proxy.exe`

---

### WSL2環境（Windows推奨）

#### 1. WSL2のインストール

```powershell
# PowerShell（管理者権限）
wsl --install
# 再起動後、Ubuntu 22.04を起動
```

#### 2. WSL内でRustインストール

```bash
# WSL Ubuntu内で実行
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env
```

#### 3. 必要なパッケージインストール

```bash
# ビルドツールとライブラリ
sudo apt update
sudo apt install -y build-essential pkg-config libssl-dev git golang-1.21
```

#### 4. リポジトリクローン・ビルド

```bash
git clone https://github.com/SeleniaProject/Nyx.git
cd Nyx

# Rustビルド
cargo build --release

# Goビルド
cd nyx-http-proxy
go build -o nyx-http-proxy
cd ..
```

---

### Linux環境（Ubuntu/Debian）

#### 1. システムパッケージインストール

```bash
# ビルドツールとライブラリ
sudo apt update
sudo apt install -y curl build-essential pkg-config git

# Rustインストール
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env

# Goインストール
wget https://go.dev/dl/go1.23.0.linux-amd64.tar.gz
sudo tar -C /usr/local -xzf go1.23.0.linux-amd64.tar.gz
echo 'export PATH=$PATH:/usr/local/go/bin' >> ~/.bashrc
source ~/.bashrc
```

#### 2. リポジトリクローン・ビルド

```bash
git clone https://github.com/SeleniaProject/Nyx.git
cd Nyx

# 全体ビルド
cargo build --release

# HTTPプロキシビルド
cd nyx-http-proxy
go build
cd ..
```

---

### macOS環境

#### 1. Homebrewのインストール（未インストールの場合）

```bash
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
```

#### 2. 必要ツールのインストール

```bash
# Rust（公式インストーラー推奨）
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env

# Goインストール
brew install go

# 確認
rustc --version
go version
```

#### 3. リポジトリクローン・ビルド

```bash
git clone https://github.com/SeleniaProject/Nyx.git
cd Nyx

# ビルド
cargo build --release
cd nyx-http-proxy && go build && cd ..
```

---

## 開発サーバー起動

### デーモン起動

#### Windows PowerShell

```powershell
# デフォルト設定で起動
.\target\release\nyx-daemon.exe --config nyx.toml

# ログレベル指定
$env:RUST_LOG="debug"
.\target\release\nyx-daemon.exe --config nyx.toml

# バックグラウンド起動（Start-Jobを使用）
Start-Job -ScriptBlock { .\target\release\nyx-daemon.exe --config nyx.toml }
```

#### WSL/Linux/macOS (bash)

```bash
# デフォルト設定で起動
./target/release/nyx-daemon --config nyx.toml

# ログレベル指定
RUST_LOG=debug ./target/release/nyx-daemon --config nyx.toml

# バックグラウンド起動
./target/release/nyx-daemon --config nyx.toml > daemon.log 2>&1 &

# systemdサービス（Linux推奨）
sudo cp scripts/nyx-daemon.service /etc/systemd/system/
sudo systemctl enable nyx-daemon
sudo systemctl start nyx-daemon
sudo systemctl status nyx-daemon
```

### HTTPプロキシ起動

#### Windows PowerShell

```powershell
cd nyx-http-proxy
.\nyx-http-proxy.exe -socks5 :9050 -http :8080
```

#### WSL/Linux/macOS (bash)

```bash
cd nyx-http-proxy
./nyx-http-proxy -socks5 :9050 -http :8080 &
```

### デーモン動作確認

#### Windows PowerShell

```powershell
# CLIでノード情報取得
.\target\release\nyx-cli.exe node info

# gRPC APIテスト（grpcurl使用）
# grpcurl: https://github.com/fullstorydev/grpcurl
grpcurl -plaintext localhost:50051 nyx.control.v1.NyxControl/GetNodeInfo

# Prometheusメトリクス確認
curl http://localhost:9090/metrics
```

#### WSL/Linux/macOS (bash)

```bash
# CLIでノード情報取得
./target/release/nyx-cli node info

# JSON-RPC API テスト（IPC経由）
echo '{"jsonrpc":"2.0","id":"1","method":"get_info","params":{}}' | \
  nc -U /tmp/nyx-daemon.sock

# Prometheusメトリクス確認
curl http://localhost:9090/metrics
```

---

## テスト実行

### 単体テスト

#### Windows PowerShell

```powershell
# 全ワークスペーステスト
cargo test --workspace

# 特定クレートのみ
cargo test -p nyx-crypto
cargo test -p nyx-core

# 並列実行数制限（メモリ節約）
cargo test --workspace -- --test-threads=2

# リリースモードでテスト（高速）
cargo test --workspace --release
```

#### WSL/Linux/macOS (bash)

```bash
# 全ワークスペーステスト
cargo test --workspace --no-fail-fast

# 詳細ログ出力
RUST_LOG=debug cargo test --workspace -- --nocapture

# 特定テストのみ実行
cargo test -p nyx-crypto test_hybrid_handshake_success
```

### 統合テスト

#### Windows PowerShell

```powershell
# 統合テストスイート
cargo test -p tests --test integration

# E2Eテスト（要Docker）
docker-compose -f docker-compose.yml up -d
cargo test -p tests --test e2e
docker-compose down
```

#### WSL/Linux/macOS (bash)

```bash
# 統合テスト
cargo test -p tests --test integration -- --nocapture

# Kubernetesテスト（要kind）
kind create cluster --config kind-config.yaml
cargo test -p tests --test e2e_kind
kind delete cluster
```

### ベンチマーク

#### Windows PowerShell

```powershell
# 全ベンチマーク実行
cargo bench --workspace

# 特定ベンチマークのみ
cargo bench -p nyx-crypto --bench hybrid_handshake

# 結果確認（HTMLレポート）
Start-Process target\criterion\report\index.html
```

#### WSL/Linux/macOS (bash)

```bash
# ベンチマーク実行
cargo bench --workspace

# 特定ベンチマーク
cargo bench -p nyx-benchmarks -- file_transfer

# HTMLレポート表示
open target/criterion/report/index.html  # macOS
xdg-open target/criterion/report/index.html  # Linux
```

---

## よくあるトラブルと対処

### 問題1: ビルドエラー「linker 'link.exe' not found」（Windows）

**原因**: Visual Studio Build Toolsが未インストール

**対処**:

```powershell
# Visual Studio 2022 Build Tools をインストール
# https://visualstudio.microsoft.com/downloads/
# "C++によるデスクトップ開発" を選択
```

または

```powershell
# Windows SDKのみインストール
# https://developer.microsoft.com/ja-jp/windows/downloads/windows-sdk/
```

---

### 問題2: 「error: could not compile `ring`」（Rust暗号化ライブラリ）

**原因**: NyxNetは`ring`を使用していません（Pure Rust実装）

**対処**:

```powershell
# 依存関係の再確認
cargo clean
cargo update
cargo build --release
```

もしまだエラーが出る場合:

```powershell
# 依存関係ツリーの確認
cargo tree | Select-String "ring"
# ringを依存しているクレートを特定し、issue報告
```

---

### 問題3: テスト失敗「address already in use」

**原因**: デーモンが既に起動中

**対処**:

#### Windows PowerShell

```powershell
# プロセス確認
Get-Process nyx-daemon

# プロセス停止
Stop-Process -Name nyx-daemon

# ポート使用確認
netstat -ano | Select-String "50051"
# PIDを確認後、停止
Stop-Process -Id <PID>
```

#### WSL/Linux/macOS (bash)

```bash
# プロセス確認・停止
pkill nyx-daemon

# ポート使用確認
lsof -i :50051
# PIDを確認後、停止
kill -9 <PID>
```

---

### 問題4: WSL2でのネットワーク接続問題

**原因**: WSL2のネットワーク分離

**対処**:

```bash
# WSL内でのIPアドレス確認
ip addr show eth0

# Windowsホスト側からアクセスする場合
# PowerShellでWSLのIPを確認
wsl hostname -I

# nyx.tomlの bind_addr を 0.0.0.0 に変更
[network]
bind_addr = "0.0.0.0:43300"
```

---

### 問題5: Goモジュールダウンロード失敗

**原因**: プロキシ設定またはネットワーク問題

**対処**:

```bash
# プロキシ無効化
go env -w GOPROXY=direct

# モジュールキャッシュクリア
go clean -modcache

# 再ダウンロード
cd nyx-http-proxy
go mod download
```

---

### 問題6: メモリ不足でビルド失敗

**原因**: Rustのリンク時メモリ使用量が大きい

**対処**:

#### Windows PowerShell

```powershell
# 並列ビルド数を削減
$env:CARGO_BUILD_JOBS=2
cargo build --release

# または incremental compilation無効化
$env:CARGO_INCREMENTAL=0
cargo build --release
```

#### WSL/Linux/macOS (bash)

```bash
# 並列ビルド数制限
CARGO_BUILD_JOBS=2 cargo build --release

# スワップ領域増設（Linux）
sudo fallocate -l 4G /swapfile
sudo chmod 600 /swapfile
sudo mkswap /swapfile
sudo swapon /swapfile
```

---

## 環境変数

### ビルド・実行時

| 変数名 | 説明 | デフォルト | 例 |
|-------|------|-----------|---|
| `RUST_LOG` | ログレベル | `info` | `debug`, `trace` |
| `RUST_BACKTRACE` | バックトレース表示 | `0` | `1` (有効), `full` |
| `CARGO_BUILD_JOBS` | 並列ビルド数 | CPU数 | `2`, `4` |
| `NYX_CONFIG_PATH` | 設定ファイルパス | `nyx.toml` | `/etc/nyx/config.toml` |
| `NYX_LOG_FORMAT` | ログ形式 | `json` | `pretty`, `compact` |
| `NYX_OTLP_ENABLED` | OTLP有効化 | `0` | `1` |
| `NYX_OTLP_ENDPOINT` | OTLPエンドポイント | - | `http://localhost:4317` |

### 設定例

#### Windows PowerShell

```powershell
# デバッグログ有効化
$env:RUST_LOG="debug"
$env:RUST_BACKTRACE="1"
.\target\release\nyx-daemon.exe

# OTLP有効化
$env:NYX_OTLP_ENABLED="1"
$env:NYX_OTLP_ENDPOINT="http://localhost:4317"
.\target\release\nyx-daemon.exe
```

#### WSL/Linux/macOS (bash)

```bash
# デバッグログ
RUST_LOG=debug RUST_BACKTRACE=1 ./target/release/nyx-daemon

# 環境変数永続化（.bashrcに追記）
echo 'export RUST_LOG=info' >> ~/.bashrc
echo 'export NYX_CONFIG_PATH=/etc/nyx/nyx.toml' >> ~/.bashrc
source ~/.bashrc
```

---

## IDE設定

### Visual Studio Code

#### 推奨拡張機能

```json
// .vscode/extensions.json
{
  "recommendations": [
    "rust-lang.rust-analyzer",
    "tamasfe.even-better-toml",
    "vadimcn.vscode-lldb",
    "golang.go",
    "ms-azuretools.vscode-docker"
  ]
}
```

#### デバッグ設定

```json
// .vscode/launch.json
{
  "version": "0.2.0",
  "configurations": [
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug nyx-daemon",
      "cargo": {
        "args": ["build", "--bin=nyx-daemon", "--package=nyx-daemon"],
        "filter": { "name": "nyx-daemon", "kind": "bin" }
      },
      "args": ["--config", "nyx.toml"],
      "cwd": "${workspaceFolder}",
      "env": {
        "RUST_LOG": "debug"
      }
    }
  ]
}
```

#### タスク設定

```json
// .vscode/tasks.json
{
  "version": "2.0.0",
  "tasks": [
    {
      "type": "cargo",
      "command": "build",
      "args": ["--release"],
      "problemMatcher": ["$rustc"],
      "group": "build",
      "label": "rust: cargo build --release"
    },
    {
      "type": "cargo",
      "command": "test",
      "args": ["--workspace", "--no-fail-fast"],
      "problemMatcher": ["$rustc"],
      "group": "test",
      "label": "rust: cargo test"
    }
  ]
}
```

---

### CLion / IntelliJ IDEA

#### プラグイン

- Rust
- TOML
- Protocol Buffers

#### 実行設定

1. Run → Edit Configurations...
2. Add New Configuration → Cargo Command
3. Command: `run`
4. Package: `nyx-daemon`
5. Environment variables: `RUST_LOG=debug`

---

## Docker開発環境

### Dockerfileベースビルド

```bash
# イメージビルド
docker build -t nyx:dev .

# コンテナ起動
docker run -d -p 50051:50051 -p 9090:9090 --name nyx-dev nyx:dev

# ログ確認
docker logs -f nyx-dev

# コンテナ内でシェル起動
docker exec -it nyx-dev /bin/bash
```

### Docker Compose開発環境

```yaml
# docker-compose.dev.yml
version: '3.8'
services:
  nyx-daemon:
    build: .
    ports:
      - "50051:50051"
      - "9090:9090"
    volumes:
      - ./nyx.toml:/etc/nyx/nyx.toml
      - ./logs:/var/log/nyx
    environment:
      RUST_LOG: debug
  
  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9091:9090"
    volumes:
      - ./grafana/prometheus.yml:/etc/prometheus/prometheus.yml
  
  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
    environment:
      GF_SECURITY_ADMIN_PASSWORD: admin
```

起動:

```bash
docker-compose -f docker-compose.dev.yml up -d
```

---

## 形式検証環境（オプション）

### TLA+ Toolboxインストール

1. https://lamport.azurewebsites.net/tla/toolbox.html からダウンロード
2. インストール後、`formal/`ディレクトリの`.tla`ファイルを開く

### TLC Model Checkerの実行

#### Windows PowerShell

```powershell
cd formal
# TLA+ Toolboxから実行（GUI）
# または
java -cp tla2tools.jar tlc2.TLC NyxBasicVerification.tla
```

#### WSL/Linux/macOS (bash)

```bash
cd formal
# TLC実行
java -cp tla2tools.jar tlc2.TLC NyxBasicVerification.tla

# 並列検証
java -cp tla2tools.jar tlc2.TLC -workers 4 NyxBasicVerification.tla
```

---

## コントリビューション開発環境

### コード品質チェック

#### Windows PowerShell

```powershell
# Clippy（リンター）
cargo clippy --workspace --all-features -- -D warnings

# フォーマットチェック
cargo fmt --all -- --check

# セキュリティ監査
cargo install cargo-audit
cargo audit

# 依存関係チェック
cargo tree --duplicates
```

#### WSL/Linux/macOS (bash)

```bash
# すべてのチェックを実行
cargo clippy --workspace --all-features -- -D warnings
cargo fmt --all -- --check
cargo audit
cargo test --workspace

# カバレッジ計測（tarpaulin）
cargo install cargo-tarpaulin
cargo tarpaulin --workspace --out Html
open tarpaulin-report.html
```

### Pre-commit Hooks

```bash
# lefthookインストール
cargo install lefthook

# フック設定
cat > lefthook.yml << 'EOF'
pre-commit:
  commands:
    fmt:
      run: cargo fmt --all -- --check
    clippy:
      run: cargo clippy --workspace -- -D warnings
    test:
      run: cargo test --workspace --no-fail-fast
EOF

# フックインストール
lefthook install
```

---

## 次のステップ

1. **チュートリアル**: `docs/tutorials/` でサンプルアプリケーション作成
2. **アーキテクチャ理解**: `docs/02_SYSTEM_ARCHITECTURE.md` 精読
3. **APIドキュメント**: `docs/04_API_REFERENCE.md` でAPI仕様確認
4. **コントリビュート**: `CONTRIBUTING.md` でコントリビューションガイドライン確認

---

## 補足: 推測箇所の明示

以下の情報は既存ファイル・標準的なプラクティスから合理的に推測しています：

- **systemdサービス**: `scripts/`にサンプルがある想定
- **Docker Compose設定**: 既存の`docker-compose.*.yml`を参考
- **IDE設定例**: 一般的なRust/Go開発設定を記載
- **一部のトラブルシューティング**: 典型的な問題と標準的対処法を記載
