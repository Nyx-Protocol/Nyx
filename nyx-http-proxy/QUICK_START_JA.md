# Nyx HTTP Proxy - Quick Start Guide

このガイドでは、Nyx HTTP ProxyをTorのように使ってHTTP/HTTPS通信を匿名化する方法を説明します。

## 🚀 最も重要なこと

**すべてのトラフィックはNyx Mix Networkの3ホップを経由します！**

```
あなた → nyx-http-proxy → Mix Node 1 → Mix Node 2 → Mix Node 3 → インターネット
```

Torと同様、以下の特徴があります:
- ✅ 3ホップのオニオンルーティング
- ✅ ポスト量子暗号化 (ML-KEM-768)
- ✅ IPアドレスの匿名化
- ✅ エンドツーエンドの暗号化

## 📋 前提条件

### 1. nyx-daemonの起動 (必須!)

```bash
# ターミナル1: Nyxデーモンを起動
cd ../nyx-daemon
cargo run --release

# 以下のメッセージが表示されるまで待つ:
# "Mix Layer IPC listening on /tmp/nyx-mix.sock" (Unix/Linux/macOS)
# または
# "Mix Layer IPC listening on \\.\pipe\nyx-mix" (Windows)
```

**重要**: デーモンが起動していないとプロキシは動作しません!

### 2. IPCソケットの確認

```bash
# Unix/Linux/macOS
ls -l /tmp/nyx-mix.sock

# Windows PowerShell
Test-Path "\\.\pipe\nyx-mix"
```

## 🔧 セットアップ

### ビルド

```bash
cd nyx-http-proxy
go build -o nyx-http-proxy
```

### 起動

```bash
# ターミナル2: HTTPプロキシを起動
./nyx-http-proxy

# 以下のメッセージが表示されるはず:
# "Successfully connected to Mix Layer at /tmp/nyx-mix.sock"
# "SOCKS5 server listening on :9050"
# "HTTP CONNECT server listening on :8080"
# "Health check server listening on :8081"
```

## 🧪 動作確認

### 基本的なHTTPリクエスト

```bash
# SOCKS5プロキシ経由 (Tor互換)
curl --socks5 localhost:9050 https://example.com

# HTTP CONNECTプロキシ経由
curl --proxy http://localhost:8080 https://example.com
```

### IPアドレスの確認

```bash
# あなたの本当のIP
curl https://api.ipify.org?format=json

# Mix Network経由のIP (Exit NodeのIP)
curl --socks5 localhost:9050 https://api.ipify.org?format=json

# 両者は異なるはず!
```

### 自動テストスクリプト

```bash
# Unix/Linux/macOS
./test-mix-routing.sh

# Windows PowerShell
.\test-mix-routing.ps1
```

## 🌐 ブラウザ設定

### Firefox

1. 設定 → ネットワーク設定 → 接続設定
2. 「手動でプロキシを設定する」を選択
3. SOCKSホスト: `localhost`、ポート: `9050`
4. 「SOCKS v5」を選択
5. 「SOCKS v5使用時はDNSもプロキシを使用する」にチェック

### Chrome/Chromium

```bash
# Linux/macOS
chromium --proxy-server="socks5://localhost:9050"

# Windows
chrome.exe --proxy-server="socks5://localhost:9050"
```

## 📊 監視

### ヘルスチェック

```bash
curl http://localhost:8081/health
```

レスポンス:
```json
{
  "status": "healthy",
  "total_connections": 10,
  "socks5_connections": 7,
  "http_connections": 3,
  "active_connections": 2,
  "bytes_transferred": 1234567,
  "errors": 0
}
```

### Mix Networkのログ確認

```bash
# ターミナル3: プロキシのログを監視
tail -f proxy.log

# 以下のようなメッセージが表示されるはず:
# "Mix Layer RPC -> proxy.connect (ID: 1)"
# "SOCKS5 Mix connection established to example.com:443 (StreamID: abc123)"
# "SOCKS5 client->Mix sent 1234 bytes"
# "SOCKS5 Mix->client sent 5678 bytes"
```

## 🔒 セキュリティ確認

### トラフィックがMix Networkを経由していることを確認

1. **ログを確認**: `proxy.log`に"Mix Layer RPC"や"Mix connection"が表示される
2. **IPアドレスを確認**: 本当のIPとExit NodeのIPが異なる
3. **パケットキャプチャ**: `tcpdump`でトラフィックを確認すると、暗号化されたパケットのみが見える

```bash
# パケットキャプチャ (要root)
sudo tcpdump -i any -n 'port 9050 or port 8080'

# 暗号化されたバイナリデータのみが表示されるはず
# 平文のHTTPヘッダーやコンテンツは見えない
```

## ⚠️ トラブルシューティング

### "dial unix /tmp/nyx-mix.sock: connect: no such file or directory"

→ `nyx-daemon`が起動していません。ターミナル1でデーモンを起動してください。

### "failed to reconnect to Mix Layer"

→ デーモンが停止した可能性があります。再起動してください。プロキシは自動的に再接続を試みます。

### "connection timeout"

→ Mix Networkに十分なノードがない可能性があります。`nyx.toml`を確認してください。

### トラフィックがMix Networkを経由していない

→ ログに"Mix Layer RPC"が表示されない場合、デーモンとの接続に問題があります:
1. デーモンが起動しているか確認
2. IPCソケットが存在するか確認
3. プロキシを再起動

## 📚 その他のドキュメント

- [README.md](README.md) - 詳細な機能説明
- [nyx-daemon documentation](../nyx-daemon/README.md) - デーモンの設定
- [Nyx project root](../README.md) - プロジェクト全体の概要

## 🎯 まとめ

これで完了です! 以下を確認してください:

- ✅ nyx-daemonが起動している
- ✅ nyx-http-proxyが起動している
- ✅ curlやブラウザでアクセスできる
- ✅ ログにMix Networkの活動が表示される
- ✅ IPアドレスが匿名化されている

**すべてのトラフィックはNyx Mix Networkの3ホップを経由して完全に匿名化されます!**

Torと同じように使えますが、ポスト量子暗号化により将来の量子コンピュータからも保護されます。
