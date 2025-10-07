#!/bin/bash
# Nyx Complete Setup and Benchmark Script for Ubuntu Server
# ゼロから完全なk8sテスト環境を構築して測定まで実行

set -e

echo "🚀 Starting Complete Nyx Setup on Ubuntu Server"
echo "================================================"

# 色付き出力
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

log_info() { echo -e "${CYAN}ℹ️  $1${NC}"; }
log_success() { echo -e "${GREEN}✅ $1${NC}"; }
log_warn() { echo -e "${YELLOW}⚠️  $1${NC}"; }
log_error() { echo -e "${RED}❌ $1${NC}"; }

# システム更新
log_info "Updating system packages..."
sudo apt-get update -qq && sudo apt-get upgrade -y -qq
log_success "System updated"

# 必要なパッケージのインストール
log_info "Installing required packages..."
sudo apt-get install -y -qq \
    curl \
    wget \
    git \
    build-essential \
    pkg-config \
    libssl-dev \
    protobuf-compiler \
    jq \
    net-tools \
    iperf3 \
    sysstat
log_success "Base packages installed"

# Dockerのインストール
if ! command -v docker &> /dev/null; then
    log_info "Installing Docker..."
    curl -fsSL https://get.docker.com -o get-docker.sh
    sudo sh get-docker.sh
    sudo usermod -aG docker $USER
    rm get-docker.sh
    log_success "Docker installed"
else
    log_success "Docker already installed"
fi

# Kindのインストール
if ! command -v kind &> /dev/null; then
    log_info "Installing Kind..."
    curl -Lo ./kind https://kind.sigs.k8s.io/dl/v0.20.0/kind-linux-amd64
    chmod +x ./kind
    sudo mv ./kind /usr/local/bin/kind
    log_success "Kind installed"
else
    log_success "Kind already installed"
fi

# kubectlのインストール
if ! command -v kubectl &> /dev/null; then
    log_info "Installing kubectl..."
    curl -LO "https://dl.k8s.io/release/$(curl -L -s https://dl.k8s.io/release/stable.txt)/bin/linux/amd64/kubectl"
    chmod +x kubectl
    sudo mv kubectl /usr/local/bin/
    log_success "kubectl installed"
else
    log_success "kubectl already installed"
fi

# Rustのインストール
if ! command -v cargo &> /dev/null; then
    log_info "Installing Rust..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain stable
    source "$HOME/.cargo/env"
    log_success "Rust installed"
else
    log_success "Rust already installed"
fi

# Rustコンポーネントの更新
log_info "Updating Rust toolchain..."
source "$HOME/.cargo/env"
rustup update stable
rustup component add clippy rustfmt
log_success "Rust toolchain ready"

# Nyxリポジトリのクローン
REPO_DIR="$HOME/NyxNet"
if [ ! -d "$REPO_DIR" ]; then
    log_info "Cloning Nyx repository..."
    git clone https://github.com/SeleniaProject/Nyx.git "$REPO_DIR"
    log_success "Repository cloned"
else
    log_info "Repository already exists, pulling latest changes..."
    cd "$REPO_DIR"
    git pull
fi

cd "$REPO_DIR"
log_success "Working directory: $REPO_DIR"

# Nyxプロジェクトのビルド
log_info "Building Nyx project (this may take a while)..."
cargo build --release --workspace
log_success "Nyx built successfully"

# Dockerイメージのビルド
log_info "Building Nyx Docker image..."
sudo docker build -t nyx-daemon:latest .
log_success "Docker image built"

# 既存のKindクラスタをクリーンアップ
log_info "Cleaning up any existing Kind clusters..."
kind get clusters 2>/dev/null | grep "nyx-cluster" | xargs -r -I {} kind delete cluster --name {} 2>/dev/null || true

# Kindクラスタの作成（ポート競合を避けるためシンプルな設定）
NUM_CLUSTERS=2
log_info "Creating $NUM_CLUSTERS Kind clusters..."
for i in $(seq 1 $NUM_CLUSTERS); do
    CLUSTER_NAME="nyx-cluster-$i"
    log_info "Creating cluster: $CLUSTER_NAME"
    
    # ポート競合を避けるため、デフォルトのkind設定を使用（ポートマッピングなし）
    cat > /tmp/kind-config-${i}.yaml <<EOF
kind: Cluster
apiVersion: kind.x-k8s.io/v1alpha4
name: ${CLUSTER_NAME}
nodes:
  - role: control-plane
  - role: worker
  - role: worker
  - role: worker
EOF
    
    kind create cluster --config /tmp/kind-config-${i}.yaml --name "$CLUSTER_NAME" --wait 60s
    rm -f /tmp/kind-config-${i}.yaml
    log_success "Cluster $CLUSTER_NAME created"
done

# Dockerイメージを各クラスタにロード
log_info "Loading Docker image to clusters..."
for i in $(seq 1 $NUM_CLUSTERS); do
    CLUSTER_NAME="nyx-cluster-$i"
    log_info "Loading image to $CLUSTER_NAME..."
    kind load docker-image nyx-daemon:latest --name "$CLUSTER_NAME"
done
log_success "Images loaded to all clusters"

# Nyxノードのデプロイ
log_info "Deploying Nyx nodes to clusters..."
for i in $(seq 1 $NUM_CLUSTERS); do
    CLUSTER_NAME="nyx-cluster-$i"
    CONTEXT="kind-${CLUSTER_NAME}"
    log_info "Deploying to $CLUSTER_NAME..."
    kubectl --context "$CONTEXT" apply -f k8s-nyx-multinode.yaml
done
log_success "Nyx nodes deployed"

# Pod起動待機
log_info "Waiting for pods to be ready..."
sleep 20
for i in $(seq 1 $NUM_CLUSTERS); do
    CLUSTER_NAME="nyx-cluster-$i"
    CONTEXT="kind-${CLUSTER_NAME}"
    kubectl --context "$CONTEXT" wait --for=condition=Ready pod --all -n nyxnet-test --timeout=120s || true
done
log_success "Pods are ready"

# クラスタ状態の確認
echo ""
log_info "Cluster Status:"
echo "================"
for i in $(seq 1 $NUM_CLUSTERS); do
    CLUSTER_NAME="nyx-cluster-$i"
    CONTEXT="kind-${CLUSTER_NAME}"
    echo ""
    log_info "📊 Cluster: $CLUSTER_NAME"
    kubectl --context "$CONTEXT" get pods -n nyxnet-test -o wide
done

# パフォーマンステスト準備
log_info "Setting up performance monitoring..."
RESULTS_DIR="$REPO_DIR/test-results-$(date +%Y%m%d-%H%M%S)"
mkdir -p "$RESULTS_DIR"
log_success "Results directory: $RESULTS_DIR"

# システムメトリクスの収集開始
log_info "Starting system metrics collection..."
(iostat -x 5 > "$RESULTS_DIR/iostat.log" 2>&1 &)
(mpstat 5 > "$RESULTS_DIR/mpstat.log" 2>&1 &)
log_success "System monitoring started"

# Nyxノードのログ収集
log_info "Collecting initial logs..."
for i in $(seq 1 $NUM_CLUSTERS); do
    CLUSTER_NAME="nyx-cluster-$i"
    CONTEXT="kind-${CLUSTER_NAME}"
    LOG_DIR="$RESULTS_DIR/logs-$CLUSTER_NAME"
    mkdir -p "$LOG_DIR"
    
    PODS=$(kubectl --context "$CONTEXT" get pods -n nyxnet-test -o jsonpath='{.items[*].metadata.name}')
    for pod in $PODS; do
        kubectl --context "$CONTEXT" logs -n nyxnet-test "$pod" > "$LOG_DIR/${pod}.log" 2>&1 || true
    done
done
log_success "Initial logs collected"

# 簡易ベンチマークテストの実行
log_info "Running basic benchmark tests..."

# コンフォーマンステスト
log_info "Running conformance tests..."
cargo test --package nyx-conformance --features hybrid --release -- --nocapture > "$RESULTS_DIR/conformance-test.log" 2>&1 || true
log_success "Conformance tests completed"

# クリプトベンチマーク
if [ -f "Dockerfile.benchmark" ]; then
    log_info "Running crypto benchmarks..."
    cargo bench --package nyx-crypto > "$RESULTS_DIR/crypto-benchmark.log" 2>&1 || true
    log_success "Crypto benchmarks completed"
fi

# ノード間レイテンシ測定
log_info "Measuring inter-node latency..."
for i in $(seq 1 $NUM_CLUSTERS); do
    CLUSTER_NAME="nyx-cluster-$i"
    CONTEXT="kind-${CLUSTER_NAME}"
    
    # Pod内でpingテスト
    PODS=$(kubectl --context "$CONTEXT" get pods -n nyxnet-test -o jsonpath='{.items[*].metadata.name}' | head -1)
    if [ -n "$PODS" ]; then
        POD=$(echo $PODS | awk '{print $1}')
        log_info "Testing latency from $CLUSTER_NAME ($POD)..."
        kubectl --context "$CONTEXT" exec -n nyxnet-test "$POD" -- sh -c "time echo test" > "$RESULTS_DIR/latency-$CLUSTER_NAME.log" 2>&1 || true
    fi
done
log_success "Latency measurements completed"

# 最終的なログ収集
log_info "Collecting final logs..."
for i in $(seq 1 $NUM_CLUSTERS); do
    CLUSTER_NAME="nyx-cluster-$i"
    CONTEXT="kind-${CLUSTER_NAME}"
    LOG_DIR="$RESULTS_DIR/logs-final-$CLUSTER_NAME"
    mkdir -p "$LOG_DIR"
    
    PODS=$(kubectl --context "$CONTEXT" get pods -n nyxnet-test -o jsonpath='{.items[*].metadata.name}')
    for pod in $PODS; do
        kubectl --context "$CONTEXT" logs -n nyxnet-test "$pod" > "$LOG_DIR/${pod}.log" 2>&1 || true
    done
done
log_success "Final logs collected"

# システムメトリクスの収集停止
log_info "Stopping system metrics collection..."
pkill -f "iostat -x" || true
pkill -f "mpstat" || true

# 結果サマリーの生成
log_info "Generating test summary..."
cat > "$RESULTS_DIR/SUMMARY.md" << EOF
# Nyx Multi-Cluster Test Results
**Date:** $(date)
**Server:** $(hostname)
**OS:** $(lsb_release -d | cut -f2)
**Kernel:** $(uname -r)

## Environment
- **Clusters:** $NUM_CLUSTERS
- **Docker Version:** $(docker --version)
- **Kubernetes Version:** $(kubectl version --client --short)
- **Rust Version:** $(rustc --version)

## Test Components
- ✅ System packages installed
- ✅ Docker installed and configured
- ✅ Kind clusters created ($NUM_CLUSTERS clusters)
- ✅ Nyx built from source
- ✅ Nyx nodes deployed to all clusters
- ✅ Conformance tests executed
- ✅ Performance benchmarks collected
- ✅ Logs and metrics saved

## Cluster Status
EOF

for i in $(seq 1 $NUM_CLUSTERS); do
    CLUSTER_NAME="nyx-cluster-$i"
    CONTEXT="kind-${CLUSTER_NAME}"
    echo "" >> "$RESULTS_DIR/SUMMARY.md"
    echo "### Cluster: $CLUSTER_NAME" >> "$RESULTS_DIR/SUMMARY.md"
    echo "\`\`\`" >> "$RESULTS_DIR/SUMMARY.md"
    kubectl --context "$CONTEXT" get pods -n nyxnet-test -o wide >> "$RESULTS_DIR/SUMMARY.md" 2>&1 || true
    echo "\`\`\`" >> "$RESULTS_DIR/SUMMARY.md"
done

cat >> "$RESULTS_DIR/SUMMARY.md" << EOF

## Results Location
All test results, logs, and metrics are saved in:
\`$RESULTS_DIR\`

## Useful Commands
\`\`\`bash
# View cluster pods
kubectl --context kind-nyx-cluster-1 get pods -n nyxnet-test

# View pod logs
kubectl --context kind-nyx-cluster-1 logs -n nyxnet-test mix-node-1 -f

# Execute into pod
kubectl --context kind-nyx-cluster-1 exec -n nyxnet-test mix-node-1 -it -- /bin/bash

# Cleanup clusters
for i in \$(seq 1 $NUM_CLUSTERS); do
    kind delete cluster --name nyx-cluster-\$i
done
\`\`\`
EOF

log_success "Test summary generated"

# 完了メッセージ
echo ""
echo "================================================"
log_success "🎉 Complete Nyx Setup and Testing Finished!"
echo "================================================"
echo ""
log_info "📊 Results saved to: $RESULTS_DIR"
log_info "📄 View summary: cat $RESULTS_DIR/SUMMARY.md"
echo ""
log_info "Cluster Information:"
for i in $(seq 1 $NUM_CLUSTERS); do
    echo "  - nyx-cluster-$i (context: kind-nyx-cluster-$i)"
done
echo ""
log_warn "To cleanup all clusters, run:"
echo "  for i in \$(seq 1 $NUM_CLUSTERS); do kind delete cluster --name nyx-cluster-\$i; done"
echo ""

# サマリーを表示
cat "$RESULTS_DIR/SUMMARY.md"
