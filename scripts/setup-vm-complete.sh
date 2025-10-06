#!/bin/bash
################################################################################
# NyxNet VM Complete Setup Script
# 素のUbuntu VMにすべての必要なコンポーネントをインストール
# Usage: curl -sSL https://your-server/setup-vm-complete.sh | bash
#        or: bash setup-vm-complete.sh
################################################################################

set -euo pipefail

# カラー出力
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

log_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# VM番号を引数から取得（デフォルト: 1）
VM_NUMBER=${1:-1}
HOSTNAME="nyx-vm-${VM_NUMBER}"

log_info "Starting NyxNet VM setup for ${HOSTNAME}..."

################################################################################
# 1. システム基本設定
################################################################################
log_info "Step 1/7: Updating system and installing basic tools..."

sudo hostnamectl set-hostname "${HOSTNAME}"
sudo apt-get update -qq
sudo apt-get upgrade -y -qq
sudo apt-get install -y \
    curl \
    wget \
    git \
    build-essential \
    pkg-config \
    libssl-dev \
    ca-certificates \
    apt-transport-https \
    gnupg \
    lsb-release \
    software-properties-common \
    net-tools \
    iproute2 \
    iptables \
    jq \
    vim \
    htop

################################################################################
# 2. Dockerインストール
################################################################################
log_info "Step 2/7: Installing Docker..."

# Docker GPGキーとリポジトリ追加
sudo install -m 0755 -d /etc/apt/keyrings
curl -fsSL https://download.docker.com/linux/ubuntu/gpg | sudo gpg --dearmor -o /etc/apt/keyrings/docker.gpg
sudo chmod a+r /etc/apt/keyrings/docker.gpg

echo \
  "deb [arch=$(dpkg --print-architecture) signed-by=/etc/apt/keyrings/docker.gpg] https://download.docker.com/linux/ubuntu \
  $(. /etc/os-release && echo "$VERSION_CODENAME") stable" | \
  sudo tee /etc/apt/sources.list.d/docker.list > /dev/null

sudo apt-get update -qq
sudo apt-get install -y docker-ce docker-ce-cli containerd.io docker-buildx-plugin docker-compose-plugin

# Dockerグループに現在のユーザーを追加
sudo usermod -aG docker $USER

# containerdの設定（K8s用）
sudo mkdir -p /etc/containerd
containerd config default | sudo tee /etc/containerd/config.toml > /dev/null
sudo sed -i 's/SystemdCgroup = false/SystemdCgroup = true/' /etc/containerd/config.toml
sudo systemctl restart containerd
sudo systemctl enable containerd

log_info "Docker installed successfully"

################################################################################
# 3. Kubernetesインストール (kubeadm, kubelet, kubectl)
################################################################################
log_info "Step 3/7: Installing Kubernetes components..."

# カーネルモジュールとsysctl設定
cat <<EOF | sudo tee /etc/modules-load.d/k8s.conf
overlay
br_netfilter
EOF

sudo modprobe overlay
sudo modprobe br_netfilter

cat <<EOF | sudo tee /etc/sysctl.d/k8s.conf
net.bridge.bridge-nf-call-iptables  = 1
net.bridge.bridge-nf-call-ip6tables = 1
net.ipv4.ip_forward                 = 1
EOF

sudo sysctl --system

# swapを無効化
sudo swapoff -a
sudo sed -i '/ swap / s/^\(.*\)$/#\1/g' /etc/fstab

# Kubernetes APTリポジトリ追加
curl -fsSL https://pkgs.k8s.io/core:/stable:/v1.28/deb/Release.key | sudo gpg --dearmor -o /etc/apt/keyrings/kubernetes-apt-keyring.gpg

echo 'deb [signed-by=/etc/apt/keyrings/kubernetes-apt-keyring.gpg] https://pkgs.k8s.io/core:/stable:/v1.28/deb/ /' | sudo tee /etc/apt/sources.list.d/kubernetes.list

sudo apt-get update -qq
sudo apt-get install -y kubelet kubeadm kubectl
sudo apt-mark hold kubelet kubeadm kubectl

sudo systemctl enable kubelet

log_info "Kubernetes components installed successfully"

################################################################################
# 4. Rustインストール
################################################################################
log_info "Step 4/7: Installing Rust toolchain..."

# Rustup経由でRustをインストール
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain stable

# 環境変数を読み込む
source "$HOME/.cargo/env"

# 必要なコンポーネントを追加
rustup component add rustfmt clippy

# wasm32ターゲット（必要に応じて）
rustup target add wasm32-unknown-unknown

log_info "Rust installed: $(rustc --version)"

################################################################################
# 5. Helmインストール (K8sパッケージマネージャー)
################################################################################
log_info "Step 5/7: Installing Helm..."

curl https://raw.githubusercontent.com/helm/helm/main/scripts/get-helm-3 | bash

log_info "Helm installed: $(helm version --short)"

################################################################################
# 6. プロジェクト用ディレクトリ作成とセットアップ
################################################################################
log_info "Step 6/7: Setting up project directories..."

mkdir -p ~/nyxnet/{src,config,logs,data}

# NyxNetプロジェクトのクローン（または手動で配置）
cat > ~/nyxnet/README.md <<'EOF'
# NyxNet VM Setup

This VM has been configured with:
- Docker & containerd
- Kubernetes (kubeadm, kubelet, kubectl)
- Rust toolchain
- Helm

## Next Steps

1. Initialize Kubernetes cluster:
   - Control plane: sudo kubeadm init --pod-network-cidr=10.244.0.0/16
   - Worker: sudo kubeadm join <control-plane-ip>:6443 --token <token> --discovery-token-ca-cert-hash <hash>

2. Setup kubectl for non-root user:
   mkdir -p $HOME/.kube
   sudo cp -i /etc/kubernetes/admin.conf $HOME/.kube/config
   sudo chown $(id -u):$(id -g) $HOME/.kube/config

3. Install CNI plugin (e.g., Flannel):
   kubectl apply -f https://raw.githubusercontent.com/flannel-io/flannel/master/Documentation/kube-flannel.yml

4. Clone and build NyxNet:
   cd ~/nyxnet/src
   git clone <your-repo>
   cd NyxNet
   cargo build --release
EOF

log_info "Project directories created at ~/nyxnet/"

################################################################################
# 7. 環境変数とプロファイル設定
################################################################################
log_info "Step 7/7: Configuring environment..."

# .bashrcに環境変数を追加
cat >> ~/.bashrc <<'EOF'

# NyxNet Environment
export NYXNET_HOME="$HOME/nyxnet"
export NYXNET_CONFIG="$NYXNET_HOME/config"
export NYXNET_LOGS="$NYXNET_HOME/logs"
export PATH="$HOME/.cargo/bin:$PATH"

# Kubernetes aliases
alias k='kubectl'
alias kgp='kubectl get pods'
alias kgs='kubectl get svc'
alias kgn='kubectl get nodes'

# VM識別
export NYX_VM_NUMBER=${VM_NUMBER}
export NYX_VM_HOSTNAME=${HOSTNAME}

EOF

source ~/.bashrc

################################################################################
# 完了メッセージ
################################################################################
log_info "=========================================="
log_info "NyxNet VM Setup Complete!"
log_info "=========================================="
log_info "VM Number: ${VM_NUMBER}"
log_info "Hostname: ${HOSTNAME}"
log_info ""
log_info "Installed components:"
log_info "  - Docker: $(docker --version)"
log_info "  - Kubernetes: $(kubeadm version -o short)"
log_info "  - Rust: $(rustc --version)"
log_info "  - Helm: $(helm version --short)"
log_info ""
log_info "Next steps:"
log_info "  1. Logout and login again (or run: newgrp docker)"
log_info "  2. Initialize K8s cluster (see ~/nyxnet/README.md)"
log_info "  3. Clone and build NyxNet project"
log_info ""
log_warn "IMPORTANT: You need to logout and login for Docker group to take effect!"

# VM情報を保存
cat > ~/nyxnet/vm-info.json <<EOF
{
  "vm_number": ${VM_NUMBER},
  "hostname": "${HOSTNAME}",
  "setup_date": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "docker_version": "$(docker --version)",
  "kubernetes_version": "$(kubeadm version -o short)",
  "rust_version": "$(rustc --version)"
}
EOF

log_info "VM info saved to ~/nyxnet/vm-info.json"
