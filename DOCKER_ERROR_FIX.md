# Docker デーモンエラーの緊急対処ガイド

## 🚨 エラー内容

```
ERROR: failed to create cluster: failed to get docker info
error during connect: Get "http://%2Fvar%2Frun%2Fdocker.sock/v1.51/info": EOF
```

## 🔍 原因

- Docker デーモンが停止している
- Docker サービスがクラッシュしている
- 過度なクリーンアップ操作 (`docker system prune -af`) でDockerが不安定になった

## ✅ 即座に実行する対処法

### **ステップ1: Docker サービスの状態確認**

```bash
sudo systemctl status docker
```

**出力例 (正常な場合):**
```
● docker.service - Docker Application Container Engine
   Loaded: loaded (/lib/systemd/system/docker.service; enabled)
   Active: active (running) since ...
```

**出力例 (異常な場合):**
```
● docker.service - Docker Application Container Engine
   Loaded: loaded
   Active: inactive (dead) または failed
```

---

### **ステップ2: Docker デーモンを再起動**

```bash
# Docker サービスを再起動
sudo systemctl restart docker

# 5秒待機
sleep 5

# Docker が正常に動作しているか確認
docker info
docker ps
```

**成功した場合:** `docker info` がシステム情報を表示します

**失敗した場合:** ステップ3へ進む

---

### **ステップ3: Docker を完全に再起動**

```bash
# Docker を完全停止
sudo systemctl stop docker
sudo systemctl stop docker.socket

# 5秒待機
sleep 5

# Docker を起動
sudo systemctl start docker

# 動作確認
docker run hello-world
```

---

### **ステップ4: それでも解決しない場合 (最終手段)**

```bash
# システム全体を再起動
sudo reboot
```

**再起動後:**

```bash
# Docker が自動起動しているか確認
docker info
docker ps

# テストを実行 (2クラスター推奨)
cd /Nyx
CLUSTER_COUNT=2 bash scripts/k8s-nyx-test.sh
```

---

## 🐳 WSL 2 (Windows) での対処法

WSL 2環境でDockerを使用している場合:

### **PowerShell で実行 (管理者権限)**

```powershell
# WSL を完全にシャットダウン
wsl --shutdown

# Docker Desktop を再起動
# タスクマネージャーで "Docker Desktop" を終了してから、再度起動

# WSL に再接続
wsl
```

### **WSL 内で確認**

```bash
# Docker が利用可能か確認
docker info

# テストを実行
cd /Nyx
CLUSTER_COUNT=2 bash scripts/k8s-nyx-test.sh
```

---

## 📊 トラブルシューティングチェックリスト

実行前に以下を確認してください:

- [ ] Docker サービスが起動している (`sudo systemctl status docker`)
- [ ] `docker info` がエラーなく実行できる
- [ ] `docker ps` がエラーなく実行できる
- [ ] システムに十分なメモリがある (`free -h`)
- [ ] 以前のクラスターがクリーンアップされている (`kind get clusters`)

---

## 🔄 推奨される実行フロー

```bash
# 1. Docker の状態確認
sudo systemctl status docker
docker info

# 2. 必要に応じて Docker を再起動
sudo systemctl restart docker

# 3. 既存クラスターのクリーンアップ
kind delete clusters --all

# 4. 2クラスター構成でテスト実行
cd /Nyx
CLUSTER_COUNT=2 bash scripts/k8s-nyx-test.sh
```

---

## ⚠️ 注意事項

### **`docker system prune -af` の危険性**

このコマンドは以下を**完全に削除**します:
- すべての停止中のコンテナ
- 使用されていないすべてのイメージ
- 使用されていないすべてのネットワーク
- すべてのビルドキャッシュ

**結果:** Docker デーモンが不安定になる可能性があります。

**推奨:** 通常は以下のみ実行:
```bash
# 停止中のコンテナのみ削除
docker container prune -f

# 使用されていないイメージのみ削除
docker image prune -f
```

---

## ✅ 成功の確認

以下のコマンドがすべて成功すれば、テストを実行できます:

```bash
# 1. Docker サービスが起動している
sudo systemctl is-active docker
# 出力: active

# 2. Docker info が正常に動作
docker info | head -n 5
# 出力: Containers, Images などの情報が表示される

# 3. Hello World が実行できる
docker run --rm hello-world
# 出力: Hello from Docker! が表示される
```

すべて成功したら:

```bash
cd /Nyx
CLUSTER_COUNT=2 bash scripts/k8s-nyx-test.sh
```

---

## 📞 それでも解決しない場合

以下の情報を収集してください:

```bash
# Docker バージョン
docker version

# Docker サービスログ
sudo journalctl -xeu docker --no-pager | tail -100

# システムリソース
free -h
df -h
```

この情報をもとに、システム管理者に相談してください。
