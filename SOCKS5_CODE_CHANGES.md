# SOCKS5 Debugging - Code Changes Summary

## Overview
この修正では、SOCKS5ハンドシェイクの問題を診断・修正するために、詳細なロギングとタイムアウト処理を改善しました。

## 変更日時
2025-10-13 (UTC)

## 問題の状況
```
❌ SOCKS5 auth failed: read greeting: EOF
❌ curl: (97) cannot complete SOCKS5 connection to example.com. (4)
```

すべてのPodは正常に起動し、Mix Layerへの接続も確立されていますが、SOCKS5プロトコルレベルでハンドシェイクが失敗していました。

## コードの変更

### 1. nyx-http-proxy/socks5.go

#### 変更A: handleAuth() - タイムアウトと詳細ログ追加
**Before:**
```go
func (s *SOCKS5Server) handleAuth(conn net.Conn) error {
    buf := make([]byte, 257)
    n, err := io.ReadAtLeast(conn, buf, 2)
    if err != nil {
        return fmt.Errorf("read greeting: %w", err)
    }
    // ... 処理続く
```

**After:**
```go
func (s *SOCKS5Server) handleAuth(conn net.Conn) error {
    // Set read timeout for authentication phase
    if err := conn.SetReadDeadline(time.Now().Add(30 * time.Second)); err != nil {
        return fmt.Errorf("set read deadline: %w", err)
    }
    defer conn.SetReadDeadline(time.Time{}) // Clear deadline after auth

    buf := make([]byte, 257)
    // Read header first (version + nmethods)
    if _, err := io.ReadFull(conn, buf[:2]); err != nil {
        return fmt.Errorf("read greeting header: %w", err)
    }

    // Verify version
    if buf[0] != socks5Version {
        log.Printf("SOCKS5 invalid version: got 0x%02x, expected 0x%02x", buf[0], socks5Version)
        return errSOCKS5InvalidVersion
    }

    nmethods := int(buf[1])
    if nmethods == 0 {
        log.Printf("SOCKS5 no authentication methods provided")
        return errSOCKS5InvalidRequest
    }

    // Read authentication methods
    if _, err := io.ReadFull(conn, buf[2:2+nmethods]); err != nil {
        return fmt.Errorf("read auth methods: %w", err)
    }
    methods := buf[2 : 2+nmethods]
    
    log.Printf("SOCKS5 client greeting: version=0x%02x, nmethods=%d, methods=%v", 
               buf[0], nmethods, methods)
    // ... 処理続く
```

**主な改善点:**
- ✅ 30秒のread timeoutを設定
- ✅ `io.ReadAtLeast`から`io.ReadFull`に変更(確実に全データ読み取り)
- ✅ ヘッダー(2バイト)を先に読み取り、その後メソッドを読み取る2段階処理
- ✅ 各ステップで詳細ログ出力
- ✅ エラー時にプロトコル情報をログ出力

#### 変更B: handleAuth() - 認証メソッド選択ログ追加
**Before:**
```go
    selectedMethod := byte(socks5AuthNoAccept)
    for _, method := range methods {
        if method == socks5AuthNone {
            selectedMethod = socks5AuthNone
            break
        }
    }

    reply := []byte{socks5Version, selectedMethod}
    if _, err := conn.Write(reply); err != nil {
        return fmt.Errorf("write auth reply: %w", err)
    }

    if selectedMethod == socks5AuthNoAccept {
        return errSOCKS5NoAcceptableAuth
    }
```

**After:**
```go
    selectedMethod := byte(socks5AuthNoAccept)
    for _, method := range methods {
        if method == socks5AuthNone {
            selectedMethod = socks5AuthNone
            break
        }
    }

    log.Printf("SOCKS5 selected auth method: 0x%02x (0x00=no-auth, 0xFF=no-accept)", selectedMethod)

    reply := []byte{socks5Version, selectedMethod}
    if _, err := conn.Write(reply); err != nil {
        return fmt.Errorf("write auth reply: %w", err)
    }

    if selectedMethod == socks5AuthNoAccept {
        log.Printf("SOCKS5 no acceptable auth method found in client methods: %v", methods)
        return errSOCKS5NoAcceptableAuth
    }

    log.Printf("SOCKS5 authentication handshake successful")
```

**改善点:**
- ✅ 選択された認証メソッドをログ出力
- ✅ 認証失敗時にクライアントが提供したメソッドをログ出力
- ✅ 認証成功時のログ追加

#### 変更C: handleRequest() - タイムアウトと詳細ログ追加
**Before:**
```go
func (s *SOCKS5Server) handleRequest(conn net.Conn) (string, error) {
    buf := make([]byte, 4)
    if _, err := io.ReadFull(conn, buf); err != nil {
        return "", fmt.Errorf("read request header: %w", err)
    }

    if buf[0] != socks5Version {
        if err := s.sendReply(conn, socks5RepGeneralFailure, nil); err != nil {
            log.Printf("SOCKS5 send reply error: %v", err)
        }
        return "", errSOCKS5InvalidVersion
    }

    cmd := buf[1]
    if cmd != socks5CmdConnect {
        if err := s.sendReply(conn, socks5RepCommandNotSupported, nil); err != nil {
            log.Printf("SOCKS5 send reply error: %v", err)
        }
        return "", errSOCKS5CommandNotSupported
    }
```

**After:**
```go
func (s *SOCKS5Server) handleRequest(conn net.Conn) (string, error) {
    // Set read timeout for request phase
    if err := conn.SetReadDeadline(time.Now().Add(30 * time.Second)); err != nil {
        return "", fmt.Errorf("set read deadline: %w", err)
    }
    defer conn.SetReadDeadline(time.Time{}) // Clear deadline after request

    buf := make([]byte, 4)
    if _, err := io.ReadFull(conn, buf); err != nil {
        return "", fmt.Errorf("read request header: %w", err)
    }

    log.Printf("SOCKS5 request header: version=0x%02x, cmd=0x%02x, rsv=0x%02x, atyp=0x%02x", 
               buf[0], buf[1], buf[2], buf[3])

    if buf[0] != socks5Version {
        log.Printf("SOCKS5 invalid request version: got 0x%02x, expected 0x%02x", buf[0], socks5Version)
        if err := s.sendReply(conn, socks5RepGeneralFailure, nil); err != nil {
            log.Printf("SOCKS5 send reply error: %v", err)
        }
        return "", errSOCKS5InvalidVersion
    }

    cmd := buf[1]
    if cmd != socks5CmdConnect {
        log.Printf("SOCKS5 unsupported command: 0x%02x (only CONNECT=0x01 supported)", cmd)
        if err := s.sendReply(conn, socks5RepCommandNotSupported, nil); err != nil {
            log.Printf("SOCKS5 send reply error: %v", err)
        }
        return "", errSOCKS5CommandNotSupported
    }
```

**改善点:**
- ✅ リクエスト読み取りに30秒タイムアウト設定
- ✅ リクエストヘッダーの全フィールドをログ出力
- ✅ バージョン不一致時に期待値と実際の値をログ出力
- ✅ サポートされていないコマンド時に詳細ログ

#### 変更D: handleRequest() - ターゲットアドレスログ改善
**Before:**
```go
    targetAddr := net.JoinHostPort(host, strconv.Itoa(int(port)))
    log.Printf("SOCKS5 CONNECT request to %s", targetAddr)
    return targetAddr, nil
```

**After:**
```go
    targetAddr := net.JoinHostPort(host, strconv.Itoa(int(port)))
    log.Printf("SOCKS5 CONNECT request parsed: target=%s (atyp=0x%02x)", targetAddr, atyp)
    return targetAddr, nil
```

**改善点:**
- ✅ アドレスタイプ(IPv4/Domain/IPv6)も含めてログ出力

#### 変更E: handleConnection() - 接続開始ログ追加
**Before:**
```go
func (s *SOCKS5Server) handleConnection(clientConn net.Conn) {
    defer clientConn.Close()

    s.stats.TotalConnections.Add(1)
    s.stats.SOCKS5Connections.Add(1)
    s.stats.ActiveConnections.Add(1)
    defer s.stats.ActiveConnections.Add(-1)

    // Phase 1: Authentication handshake
    if err := s.handleAuth(clientConn); err != nil {
        log.Printf("SOCKS5 auth failed: %v", err)
        s.stats.Errors.Add(1)
        return
    }
```

**After:**
```go
func (s *SOCKS5Server) handleConnection(clientConn net.Conn) {
    defer clientConn.Close()

    remoteAddr := clientConn.RemoteAddr().String()
    log.Printf("SOCKS5 new connection from %s", remoteAddr)

    s.stats.TotalConnections.Add(1)
    s.stats.SOCKS5Connections.Add(1)
    s.stats.ActiveConnections.Add(1)
    defer s.stats.ActiveConnections.Add(-1)

    // Phase 1: Authentication handshake
    log.Printf("SOCKS5 [%s] starting authentication handshake", remoteAddr)
    if err := s.handleAuth(clientConn); err != nil {
        log.Printf("SOCKS5 [%s] auth failed: %v", remoteAddr, err)
        s.stats.Errors.Add(1)
        return
    }
    log.Printf("SOCKS5 [%s] authentication successful", remoteAddr)
```

**改善点:**
- ✅ 接続開始時にクライアントIPアドレスをログ出力
- ✅ 認証開始時のログ追加
- ✅ 認証成功時のログ追加
- ✅ すべてのログにクライアントアドレスを含める(追跡容易化)

### 2. scripts/debug-socks5.sh (新規作成)
SOCKS5プロトコルレベルのデバッグスクリプト:
- ポート接続性確認
- 手動SOCKS5 greetingテスト (hex: `\x05\x01\x00`)
- socat詳細テスト
- Unix socketヘルスチェック
- Daemon/Proxyログ相関

### 3. docs/SOCKS5_DEBUGGING.md (新規作成)
包括的なデバッグガイド:
- 現在の状況分析
- 根本原因仮説
- 詳細なデバッグ手順
- 代替テスト方法
- トラブルシューティングフローチャート

### 4. 検証手順.md (更新)
SOCKS5デバッグセクション追加:
- 最新コードの取得方法
- デバッグスクリプトの実行方法
- 期待されるログエントリの例

## 期待される効果

### 診断能力の向上
新しいログにより、以下を特定可能:
1. **接続確立の確認**: `SOCKS5 new connection from X.X.X.X:XXXXX`
2. **認証フェーズの開始**: `starting authentication handshake`
3. **クライアントのプロトコル**: `client greeting: version=0x05, nmethods=1, methods=[0]`
4. **認証メソッド選択**: `selected auth method: 0x00`
5. **認証成功/失敗**: `authentication successful` or `auth failed: ...`
6. **リクエストの詳細**: `request header: version=0x05, cmd=0x01, ...`
7. **ターゲットアドレス**: `CONNECT request parsed: target=example.com:80`

### タイムアウト処理改善
- 30秒のread timeoutにより、無限待機を回避
- timeout後にdeadlineをクリアして次の処理に影響しない
- timeout発生時は明確なエラーメッセージ

### プロトコル処理の堅牢性向上
- `io.ReadAtLeast`から`io.ReadFull`への変更により、部分読み取りを回避
- 2段階読み取り(ヘッダー→データ)により、プロトコル違反を早期検出
- 各バイトの検証時に詳細ログ出力

## 次のステップ

### Linuxサーバーで実行:
```bash
cd /root/Nyx
git pull
SKIP_CLEANUP=true bash scripts/k8s-nyx-test.sh
bash scripts/debug-socks5.sh nyx-cluster-1
kubectl --context kind-nyx-cluster-1 -n nyx-test logs -l app=nyx-proxy --tail=100
```

### 期待されるログ(正常時):
```
SOCKS5 new connection from 10.240.1.3:45678
SOCKS5 [10.240.1.3:45678] starting authentication handshake
SOCKS5 client greeting: version=0x05, nmethods=1, methods=[0]
SOCKS5 selected auth method: 0x00 (0x00=no-auth, 0xFF=no-accept)
SOCKS5 authentication handshake successful
SOCKS5 [10.240.1.3:45678] authentication successful
SOCKS5 request header: version=0x05, cmd=0x01, rsv=0x00, atyp=0x03
SOCKS5 CONNECT request parsed: target=example.com:80 (atyp=0x03)
SOCKS5 Mix connection established to example.com:80 (StreamID: abc123)
```

### 問題別の診断:
1. **"new connection"ログなし** → TCP/Serviceレベルの問題
2. **"starting authentication"なし** → accept成功後すぐにクローズ
3. **"client greeting"なし** → タイムアウトまたはEOF(データ送信なし)
4. **"invalid version"** → プロトコルミスマッチ
5. **"no acceptable auth method"** → 認証メソッド不一致

## コミット情報
- Commit 1: `a7a156e` - Add SOCKS5 protocol debugging script
- Commit 2: `299e214` - Improve SOCKS5 handshake with better timeout handling and detailed logging
- Commit 3: `6293007` - Add comprehensive SOCKS5 debugging guide
- Commit 4: `aff5ad9` - Update verification guide with SOCKS5 debugging instructions

## ファイル変更サマリー
```
nyx-http-proxy/socks5.go          | 43行追加, 7行削除
scripts/debug-socks5.sh           | 82行追加 (新規)
docs/SOCKS5_DEBUGGING.md          | 178行追加 (新規)
検証手順.md                        | 31行追加, 2行削除
```

Total: **334 additions, 9 deletions**
