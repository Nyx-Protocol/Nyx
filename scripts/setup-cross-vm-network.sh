#!/bin/bash
################################################################################
# Cross-VM/Cluster Network Setup for NyxNet
# 複数VM、複数K8sクラスタ間でのNyxNet通信を設定
# Usage: bash setup-cross-vm-network.sh
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

# VM情報を読み込む
if [ -f ~/nyxnet/vm-info.json ]; then
    VM_NUMBER=$(jq -r '.vm_number' ~/nyxnet/vm-info.json)
else
    log_error "VM info not found!"
    exit 1
fi

log_info "Setting up cross-VM network for VM-${VM_NUMBER}..."

################################################################################
# 1. 他VMのIPアドレスを取得・設定
################################################################################
log_info "Step 1/5: Configuring VM network discovery..."

# VM間通信用の設定ファイルを作成
cat > ~/nyxnet/config/vm-network.json <<EOF
{
  "local_vm": ${VM_NUMBER},
  "vms": []
}
EOF

log_warn "Please configure other VMs' IP addresses in ~/nyxnet/config/vm-network.json"
log_warn "Example format:"
cat <<'EOF'
{
  "local_vm": 1,
  "vms": [
    {"vm_id": 1, "ip": "192.168.1.101", "k8s_api": "https://192.168.1.101:6443"},
    {"vm_id": 2, "ip": "192.168.1.102", "k8s_api": "https://192.168.1.102:6443"},
    {"vm_id": 3, "ip": "192.168.1.103", "k8s_api": "https://192.168.1.103:6443"}
  ]
}
EOF

################################################################################
# 2. NodePort Serviceを作成（VM間通信用）
################################################################################
log_info "Step 2/5: Creating NodePort services for cross-VM communication..."

# 各Mix NodeにNodePortサービスを追加
for NODE_ID in 1 2 3; do
    NODE_PORT=$((30000 + ($VM_NUMBER - 1) * 100 + $NODE_ID))
    
    cat <<EOF | kubectl apply -f -
apiVersion: v1
kind: Service
metadata:
  name: mix-node-${NODE_ID}-external
  namespace: nyxnet-vm${VM_NUMBER}
spec:
  type: NodePort
  selector:
    app: nyx-mix
    node: "node${NODE_ID}"
  ports:
  - name: nyx-udp
    port: 9999
    targetPort: 9999
    nodePort: ${NODE_PORT}
    protocol: UDP
  - name: nyx-api
    port: 8080
    targetPort: 8080
    nodePort: $((${NODE_PORT} + 10))
    protocol: TCP
EOF
    
    log_info "Created external service for mix-node-${NODE_ID} on NodePort ${NODE_PORT}"
done

################################################################################
# 3. クロスクラスタサービスディスカバリー
################################################################################
log_info "Step 3/5: Setting up cross-cluster service discovery..."

# 全VM/クラスタのノード情報を集約
mkdir -p ~/nyxnet/config/clusters

cat > ~/nyxnet/config/clusters/global-directory.yaml <<EOF
# Global NyxNet Directory
# すべてのVM/クラスタのノード情報

version: "1.0"
total_vms: 3  # 必要に応じて変更
nodes_per_vm: 3
total_nodes: 9  # total_vms * nodes_per_vm

# VM1のノード
vm1:
  ip: "192.168.1.101"  # 要変更
  k8s_api: "https://192.168.1.101:6443"
  nodes:
    - id: 1
      port: 30001
      api_port: 30011
    - id: 2
      port: 30002
      api_port: 30012
    - id: 3
      port: 30003
      api_port: 30013

# VM2のノード
vm2:
  ip: "192.168.1.102"  # 要変更
  k8s_api: "https://192.168.1.102:6443"
  nodes:
    - id: 4
      port: 30101
      api_port: 30111
    - id: 5
      port: 30102
      api_port: 30112
    - id: 6
      port: 30103
      api_port: 30113

# VM3のノード
vm3:
  ip: "192.168.1.103"  # 要変更
  k8s_api: "https://192.168.1.103:6443"
  nodes:
    - id: 7
      port: 30201
      api_port: 30211
    - id: 8
      port: 30202
      api_port: 30212
    - id: 9
      port: 30203
      api_port: 30213
EOF

log_warn "Global directory template created at ~/nyxnet/config/clusters/global-directory.yaml"
log_warn "Update IP addresses for your VM setup!"

################################################################################
# 4. ConfigMapに全ノード情報を登録
################################################################################
log_info "Step 4/5: Updating ConfigMap with global node directory..."

# ConfigMapを更新して全ノード情報を含める
kubectl create configmap nyx-global-directory \
    --from-file=~/nyxnet/config/clusters/global-directory.yaml \
    --namespace=nyxnet-vm${VM_NUMBER} \
    --dry-run=client -o yaml | kubectl apply -f -

# Podに環境変数として注入
for NODE_ID in 1 2 3; do
    kubectl set env pod/mix-node-${NODE_ID} \
        -n nyxnet-vm${VM_NUMBER} \
        NYX_GLOBAL_DIRECTORY=/etc/nyx/global-directory.yaml || true
done

################################################################################
# 5. ファイアウォール設定（必要なポートを開放）
################################################################################
log_info "Step 5/5: Configuring firewall rules..."

# UFWでポートを開放（Ubuntuの場合）
if command -v ufw &> /dev/null; then
    log_info "Opening ports with UFW..."
    
    # K8s API
    sudo ufw allow 6443/tcp comment "K8s API"
    
    # NodePort範囲
    sudo ufw allow 30000:30999/tcp comment "K8s NodePort TCP"
    sudo ufw allow 30000:30999/udp comment "K8s NodePort UDP"
    
    # Flannel VXLAN
    sudo ufw allow 8472/udp comment "Flannel VXLAN"
    
    sudo ufw reload || true
    
    log_info "Firewall rules configured"
else
    log_warn "UFW not found, configure firewall manually:"
    log_warn "  - TCP: 6443, 30000-30999"
    log_warn "  - UDP: 8472, 30000-30999"
fi

################################################################################
# 完了メッセージ
################################################################################
log_info "=========================================="
log_info "Cross-VM Network Setup Complete!"
log_info "=========================================="
log_info "VM-${VM_NUMBER} configuration:"
log_info "  - External services created with NodePorts"
log_info "  - Global directory template: ~/nyxnet/config/clusters/global-directory.yaml"
log_info "  - Firewall rules configured"
log_info ""
log_info "Next steps:"
log_info "  1. Update VM IPs in global-directory.yaml on ALL VMs"
log_info "  2. Test connectivity: nc -zv <other-vm-ip> 30001"
log_info "  3. Run integration test: bash test-cross-vm.sh"

# ネットワーク情報を保存
MY_IP=$(hostname -I | awk '{print $1}')
cat > ~/nyxnet/network-info.json <<EOF
{
  "vm_number": ${VM_NUMBER},
  "local_ip": "${MY_IP}",
  "nodeport_range_start": $((30000 + ($VM_NUMBER - 1) * 100 + 1)),
  "nodeport_range_end": $((30000 + ($VM_NUMBER - 1) * 100 + 13)),
  "configured_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
EOF

log_info "Network info saved to ~/nyxnet/network-info.json"
