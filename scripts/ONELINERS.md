# Nyx Ubuntu Server Complete Setup - One-Liner Collection
# すべてをワンライナーで実行するコマンド集

## 🚀 超圧縮ワンライナー (フルセットアップ)
```bash
curl -fsSL https://raw.githubusercontent.com/SeleniaProject/Nyx/main/scripts/ubuntu-k8s-nyx-setup.sh | bash
```

## 📝 完全版ワンライナー (ローカル実行用)
```bash
sudo apt-get update -qq && sudo apt-get install -y curl git build-essential pkg-config libssl-dev protobuf-compiler && curl -fsSL https://get.docker.com | sudo sh && sudo usermod -aG docker $USER && curl -Lo /tmp/kind https://kind.sigs.k8s.io/dl/v0.20.0/kind-linux-amd64 && sudo install /tmp/kind /usr/local/bin/ && curl -LO "https://dl.k8s.io/release/$(curl -Ls https://dl.k8s.io/release/stable.txt)/bin/linux/amd64/kubectl" && sudo install kubectl /usr/local/bin/ && curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y && source "$HOME/.cargo/env" && git clone https://github.com/SeleniaProject/Nyx.git ~/NyxNet && cd ~/NyxNet && cargo build --release && docker build -t nyx-daemon:latest . && for i in 1 2; do kind create cluster --config kind-config.yaml --name nyx-cluster-$i; kind load docker-image nyx-daemon:latest --name nyx-cluster-$i; kubectl --context kind-nyx-cluster-$i apply -f k8s-nyx-multinode.yaml; done && sleep 20 && for i in 1 2; do echo "Cluster $i:"; kubectl --context kind-nyx-cluster-$i get pods -n nyxnet-test; done
```

## 🎯 段階的ワンライナー集

### 1. システムセットアップ + ツールインストール
```bash
sudo apt-get update && sudo apt-get install -y curl git build-essential pkg-config libssl-dev protobuf-compiler jq net-tools iperf3 sysstat && curl -fsSL https://get.docker.com | sudo sh && sudo usermod -aG docker $USER && curl -Lo /tmp/kind https://kind.sigs.k8s.io/dl/v0.20.0/kind-linux-amd64 && sudo install /tmp/kind /usr/local/bin/ && curl -LO "https://dl.k8s.io/release/$(curl -Ls https://dl.k8s.io/release/stable.txt)/bin/linux/amd64/kubectl" && sudo install kubectl /usr/local/bin/ && curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y && echo "✅ Tools installed. Run: source ~/.cargo/env"
```

### 2. Nyxクローン + ビルド
```bash
source "$HOME/.cargo/env" && git clone https://github.com/SeleniaProject/Nyx.git ~/NyxNet && cd ~/NyxNet && cargo build --release && docker build -t nyx-daemon:latest . && echo "✅ Nyx built successfully"
```

### 3. K8sクラスタ作成 + デプロイ
```bash
cd ~/NyxNet && for i in 1 2; do kind create cluster --config kind-config.yaml --name nyx-cluster-$i --wait 60s && kind load docker-image nyx-daemon:latest --name nyx-cluster-$i && kubectl --context kind-nyx-cluster-$i apply -f k8s-nyx-multinode.yaml && echo "✅ Cluster $i ready"; done && sleep 15 && for i in 1 2; do echo "=== Cluster $i ===" && kubectl --context kind-nyx-cluster-$i get pods -n nyxnet-test -o wide; done
```

### 4. テスト実行 + 測定
```bash
cd ~/NyxNet && RESULTS="test-results-$(date +%Y%m%d-%H%M%S)" && mkdir -p "$RESULTS" && cargo test --package nyx-conformance --features hybrid --release -- --nocapture 2>&1 | tee "$RESULTS/conformance.log" && for i in 1 2; do kubectl --context kind-nyx-cluster-$i logs -n nyxnet-test mix-node-1 > "$RESULTS/cluster-$i-logs.txt" 2>&1; done && echo "✅ Results saved to $RESULTS"
```

### 5. クリーンアップ
```bash
for i in 1 2 3 4; do kind delete cluster --name nyx-cluster-$i 2>/dev/null; done && docker system prune -af && echo "✅ Cleanup complete"
```

## 🔥 最速ワンライナー (既存環境前提)
既にDocker/Kind/kubectl/Rustがインストール済みの場合:
```bash
cd ~/NyxNet 2>/dev/null || (git clone https://github.com/SeleniaProject/Nyx.git ~/NyxNet && cd ~/NyxNet) && git pull && cargo build --release && docker build -t nyx-daemon:latest . && for i in 1 2; do (kind get clusters | grep -q nyx-cluster-$i && kind delete cluster --name nyx-cluster-$i); kind create cluster --config kind-config.yaml --name nyx-cluster-$i && kind load docker-image nyx-daemon:latest --name nyx-cluster-$i && kubectl --context kind-nyx-cluster-$i apply -f k8s-nyx-multinode.yaml; done && sleep 20 && for i in 1 2; do kubectl --context kind-nyx-cluster-$i get pods -n nyxnet-test -o wide; done
```

## 🐳 Docker Composeベース (開発環境)
```bash
cd ~/NyxNet && docker-compose -f docker-compose.benchmark.yml up -d && sleep 10 && docker-compose -f docker-compose.benchmark.yml ps && docker-compose -f docker-compose.benchmark.yml logs --tail=50
```

## 📊 ベンチマーク専用ワンライナー
```bash
cd ~/NyxNet && cargo bench --workspace 2>&1 | tee benchmark-$(date +%Y%m%d-%H%M%S).log && cargo test --package nyx-conformance --features hybrid,multipath,telemetry --release -- --nocapture 2>&1 | tee conformance-$(date +%Y%m%d-%H%M%S).log
```

## 🔍 監視・デバッグ用ワンライナー
```bash
# すべてのPodのステータスとログを一気に取得
for i in 1 2; do echo "=== Cluster nyx-cluster-$i ===" && kubectl --context kind-nyx-cluster-$i get pods -n nyxnet-test -o wide && kubectl --context kind-nyx-cluster-$i describe pods -n nyxnet-test && kubectl --context kind-nyx-cluster-$i logs -n nyxnet-test --all-containers=true --tail=100; done

# リアルタイムログ監視 (全クラスタ)
for i in 1 2; do (kubectl --context kind-nyx-cluster-$i logs -n nyxnet-test mix-node-1 -f 2>&1 | sed "s/^/[Cluster-$i] /" &); done

# パフォーマンスメトリクス収集
kubectl --context kind-nyx-cluster-1 top pods -n nyxnet-test && kubectl --context kind-nyx-cluster-2 top pods -n nyxnet-test
```

## 💡 使い方

### 新規Ubuntuサーバーでゼロから:
```bash
wget https://raw.githubusercontent.com/SeleniaProject/Nyx/main/scripts/ubuntu-k8s-nyx-setup.sh
chmod +x ubuntu-k8s-nyx-setup.sh
./ubuntu-k8s-nyx-setup.sh
```

### スクリプトとして実行:
```bash
curl -fsSL https://raw.githubusercontent.com/SeleniaProject/Nyx/main/scripts/ubuntu-k8s-nyx-setup.sh | bash
```

### SSH経由でリモート実行:
```bash
ssh user@server 'bash -s' < scripts/ubuntu-k8s-nyx-setup.sh
```

### 環境変数でカスタマイズ:
```bash
NUM_CLUSTERS=4 RESULTS_DIR="/tmp/nyx-results" bash scripts/ubuntu-k8s-nyx-setup.sh
```

## ⚡ パフォーマンスチューニング版
```bash
# CPUコア数に応じて並列ビルド
cd ~/NyxNet && cargo build --release -j $(nproc) && docker build --build-arg MAKEFLAGS="-j$(nproc)" -t nyx-daemon:latest .

# メモリ制限付きでクラスタ作成
for i in 1 2; do kind create cluster --config <(cat kind-config.yaml && echo "  kubeadmConfigPatches: [\"kind: KubeletConfiguration\", \"maxPods: 110\", \"memoryThrottlingFactor: 0.8\"]") --name nyx-cluster-$i; done
```

## 🎓 実用例

### CI/CDパイプライン用:
```bash
#!/bin/bash -ex
apt-get update && apt-get install -y docker.io kubectl
curl -Lo /usr/local/bin/kind https://kind.sigs.k8s.io/dl/v0.20.0/kind-linux-amd64 && chmod +x /usr/local/bin/kind
git clone https://github.com/SeleniaProject/Nyx.git && cd Nyx
cargo test --workspace --release
docker build -t nyx:test .
kind create cluster --name ci-test
kind load docker-image nyx:test --name ci-test
kubectl apply -f k8s-nyx-multinode.yaml
kubectl wait --for=condition=Ready pod --all -n nyxnet-test --timeout=300s
kubectl logs -n nyxnet-test --all-containers=true
```

### 本番環境チェックリスト:
```bash
# システム要件確認
free -h && df -h && nproc && lsb_release -a

# ネットワーク確認
sudo ufw status && ip addr show && ss -tlnp

# Nyx完全セットアップ
bash ubuntu-k8s-nyx-setup.sh

# 結果確認
ls -lh ~/NyxNet/test-results-*/
```

## 🔧 トラブルシューティング

### Kind クラスタ作成エラー

**ポート競合エラー (`address already in use`):**
```bash
# 使用中のポートを確認
sudo netstat -tlnp | grep -E ':(80|443|30000)'

# Kindクラスタを全削除
kind get clusters | xargs -r -I {} kind delete cluster --name {}

# Dockerコンテナを全削除
docker ps -a | grep kind | awk '{print $1}' | xargs -r docker rm -f

# 再試行
bash scripts/ubuntu-k8s-nyx-setup.sh
```

**cgroup エラー (`could not find a log line`):**
```bash
# Dockerの状態確認
sudo systemctl status docker

# cgroupバージョン確認
cat /proc/cgroups

# cgroup v2の場合、v1モードで起動
sudo mkdir -p /etc/systemd/system/docker.service.d
echo '[Service]
Environment="DOCKER_OPTS=--exec-opt native.cgroupdriver=systemd"' | sudo tee /etc/systemd/system/docker.service.d/cgroup.conf
sudo systemctl daemon-reload
sudo systemctl restart docker

# シンプルなクラスタで再試行
kind create cluster --name test-cluster
```

**メモリ不足エラー:**
```bash
# メモリ使用状況確認
free -h

# 不要なDockerイメージを削除
docker system prune -af

# スワップを有効化（一時的）
sudo fallocate -l 4G /swapfile
sudo chmod 600 /swapfile
sudo mkswap /swapfile
sudo swapon /swapfile
```

### ビルドエラー

**protobuf エラー:**
```bash
# protobufコンパイラのインストール確認
protoc --version

# 再インストール
sudo apt-get update
sudo apt-get install -y protobuf-compiler libprotobuf-dev

# キャッシュクリアして再ビルド
cd ~/NyxNet
cargo clean
cargo build --release
```

**依存関係エラー:**
```bash
# Rust更新
rustup update stable

# Cargo.lockを再生成
rm Cargo.lock
cargo generate-lockfile
cargo build --release
```

### Docker ビルドエラー

**イメージが見つからない:**
```bash
# Dockerログを確認
docker logs $(docker ps -a | grep nyx | awk '{print $1}' | head -1)

# BuildKitを無効化して再試行
DOCKER_BUILDKIT=0 docker build -t nyx-daemon:latest .

# キャッシュなしでビルド
docker build --no-cache -t nyx-daemon:latest .
```

### クラスタ起動後のエラー

**Podが起動しない:**
```bash
# Pod状態確認
kubectl --context kind-nyx-cluster-1 get pods -n nyxnet-test -o wide

# Pod詳細情報
kubectl --context kind-nyx-cluster-1 describe pod -n nyxnet-test mix-node-1

# イベント確認
kubectl --context kind-nyx-cluster-1 get events -n nyxnet-test --sort-by='.lastTimestamp'

# ログ確認
kubectl --context kind-nyx-cluster-1 logs -n nyxnet-test mix-node-1 --previous
```

**ネットワーク接続エラー:**
```bash
# DNS確認
kubectl --context kind-nyx-cluster-1 exec -n nyxnet-test mix-node-1 -- nslookup kubernetes.default

# ネットワークプラグイン確認
kubectl --context kind-nyx-cluster-1 get pods -n kube-system

# ファイアウォール確認
sudo iptables -L -n | grep -E '(DOCKER|KIND)'
```

## 💡 パフォーマンスチューニング

### 高速化Tips:
```bash
# 並列ビルド（CPUコア数に応じて）
MAKEFLAGS="-j$(nproc)" cargo build --release

# Rust incrementalビルド無効化（リリースビルドの最適化）
CARGO_INCREMENTAL=0 cargo build --release

# リンク時間最適化
RUSTFLAGS="-C link-arg=-fuse-ld=lld" cargo build --release

# ディスクI/O最適化（tmpfsを使用）
sudo mount -t tmpfs -o size=4G tmpfs ~/NyxNet/target
```
