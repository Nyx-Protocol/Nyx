#!/bin/bash
################################################################################
# NyxNet K8s Cluster Initialization Script
# 各VM内で複数ノードK8sクラスタを初期化
# Usage: bash init-k8s-cluster.sh [control-plane|worker] [vm-number] [control-plane-ip]
################################################################################

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

log_info() { echo -e "${GREEN}[INFO]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $1"; }

NODE_TYPE=${1:-control-plane}  # control-plane or worker
VM_NUMBER=${2:-1}
CONTROL_PLANE_IP=${3:-}

POD_NETWORK_CIDR="10.244.0.0/16"
SERVICE_CIDR="10.96.0.0/12"

################################################################################
# Control Plane初期化
################################################################################
if [ "$NODE_TYPE" == "control-plane" ]; then
    log_info "Initializing Kubernetes Control Plane on VM-${VM_NUMBER}..."
    
    # kubeadm init
    sudo kubeadm init \
        --pod-network-cidr="${POD_NETWORK_CIDR}" \
        --service-cidr="${SERVICE_CIDR}" \
        --node-name="control-plane-vm${VM_NUMBER}" \
        --apiserver-advertise-address="$(hostname -I | awk '{print $1}')"
    
    # kubectlセットアップ（非rootユーザー用）
    mkdir -p $HOME/.kube
    sudo cp -i /etc/kubernetes/admin.conf $HOME/.kube/config
    sudo chown $(id -u):$(id -g) $HOME/.kube/config
    
    log_info "Waiting for control plane to be ready..."
    sleep 10
    
    # CNIプラグイン（Flannel）をインストール
    log_info "Installing Flannel CNI..."
    kubectl apply -f https://raw.githubusercontent.com/flannel-io/flannel/master/Documentation/kube-flannel.yml
    
    # Control Planeでもワークロードを実行可能にする（小規模クラスタ用）
    kubectl taint nodes --all node-role.kubernetes.io/control-plane- || true
    
    # Join tokenを生成して保存
    log_info "Generating join token..."
    JOIN_COMMAND=$(sudo kubeadm token create --print-join-command)
    echo "$JOIN_COMMAND" > ~/nyxnet/k8s-join-command.sh
    chmod +x ~/nyxnet/k8s-join-command.sh
    
    log_info "=========================================="
    log_info "Control Plane initialized successfully!"
    log_info "=========================================="
    log_info "Control Plane IP: $(hostname -I | awk '{print $1}')"
    log_info ""
    log_info "To join worker nodes, run on each worker:"
    log_info "${BLUE}${JOIN_COMMAND}${NC}"
    log_info ""
    log_info "Join command saved to: ~/nyxnet/k8s-join-command.sh"
    
    # クラスタ情報を保存
    cat > ~/nyxnet/cluster-info.json <<EOF
{
  "cluster_type": "control-plane",
  "vm_number": ${VM_NUMBER},
  "control_plane_ip": "$(hostname -I | awk '{print $1}')",
  "pod_network_cidr": "${POD_NETWORK_CIDR}",
  "service_cidr": "${SERVICE_CIDR}",
  "initialized_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
EOF

################################################################################
# Worker Node参加
################################################################################
elif [ "$NODE_TYPE" == "worker" ]; then
    if [ -z "$CONTROL_PLANE_IP" ]; then
        log_error "Control Plane IP is required for worker nodes!"
        log_error "Usage: bash init-k8s-cluster.sh worker <vm-number> <control-plane-ip>"
        exit 1
    fi
    
    log_info "Joining Kubernetes cluster as Worker Node on VM-${VM_NUMBER}..."
    log_info "Control Plane IP: ${CONTROL_PLANE_IP}"
    
    # Join commandをControl Planeから取得する必要がある
    log_warn "Please run the join command provided by control plane:"
    log_warn "Example: sudo kubeadm join ${CONTROL_PLANE_IP}:6443 --token <token> --discovery-token-ca-cert-hash <hash>"
    log_warn ""
    log_warn "Or copy ~/nyxnet/k8s-join-command.sh from control plane and run it here"
    
    # クラスタ情報を保存
    cat > ~/nyxnet/cluster-info.json <<EOF
{
  "cluster_type": "worker",
  "vm_number": ${VM_NUMBER},
  "control_plane_ip": "${CONTROL_PLANE_IP}",
  "joined_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
EOF
    
else
    log_error "Invalid node type: ${NODE_TYPE}"
    log_error "Must be 'control-plane' or 'worker'"
    exit 1
fi

log_info "K8s cluster initialization complete for VM-${VM_NUMBER}"
