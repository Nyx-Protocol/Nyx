#!/bin/bash
################################################################################
# NyxNet Multi-VM Deployment Script
# 複数VM、複数K8sクラスタにNyxNetをデプロイ
# Usage: bash deploy-nyxnet-multivm.sh
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
    HOSTNAME=$(jq -r '.hostname' ~/nyxnet/vm-info.json)
else
    log_error "VM info not found! Run setup-vm-complete.sh first."
    exit 1
fi

log_info "Deploying NyxNet on ${HOSTNAME} (VM-${VM_NUMBER})..."

################################################################################
# 1. NyxNetプロジェクトのビルド
################################################################################
log_info "Step 1/5: Building NyxNet project..."

cd ~/nyxnet/src/NyxNet || {
    log_error "NyxNet source not found at ~/nyxnet/src/NyxNet"
    log_error "Clone the repository first: git clone <repo-url> ~/nyxnet/src/NyxNet"
    exit 1
}

# Dockerイメージをビルド
log_info "Building Docker images..."
docker build -t nyxnet/daemon:latest -f Dockerfile .
docker build -t nyxnet/mix:latest -f nyx-mix/Dockerfile . || docker build -t nyxnet/mix:latest -f Dockerfile .

# Cargoでバイナリもビルド（ローカルテスト用）
cargo build --release --bin nyx-daemon

log_info "Build complete!"

################################################################################
# 2. K8s Namespaceとリソース作成
################################################################################
log_info "Step 2/5: Creating Kubernetes resources..."

kubectl create namespace nyxnet-vm${VM_NUMBER} --dry-run=client -o yaml | kubectl apply -f -

# ConfigMapを作成
cat <<EOF | kubectl apply -f -
apiVersion: v1
kind: ConfigMap
metadata:
  name: nyx-config
  namespace: nyxnet-vm${VM_NUMBER}
data:
  nyx.toml: |
    [network]
    listen_port = 9999
    max_connections = 100
    vm_id = ${VM_NUMBER}
    
    [crypto]
    algorithm = "ChaCha20Poly1305"
    key_rotation_interval = 3600
    
    [routing]
    num_hops = 3
    path_selection = "weighted"
    
    [performance]
    worker_threads = 4
    buffer_size = 65536
    
    [telemetry]
    enabled = true
    export_interval = 60
EOF

################################################################################
# 3. Mix Nodeをデプロイ（VM番号に応じて複数ノード）
################################################################################
log_info "Step 3/5: Deploying Mix Nodes..."

# 各VMで3つのMix Nodeをデプロイ
for NODE_ID in 1 2 3; do
    GLOBAL_NODE_ID=$((($VM_NUMBER - 1) * 3 + $NODE_ID))
    
    cat <<EOF | kubectl apply -f -
apiVersion: v1
kind: Pod
metadata:
  name: mix-node-${NODE_ID}
  namespace: nyxnet-vm${VM_NUMBER}
  labels:
    app: nyx-mix
    vm: "vm${VM_NUMBER}"
    node: "node${NODE_ID}"
    global-node: "node${GLOBAL_NODE_ID}"
spec:
  containers:
  - name: nyx-daemon
    image: nyxnet/daemon:latest
    imagePullPolicy: Never
    ports:
    - containerPort: 9999
      protocol: UDP
      name: nyx-udp
    - containerPort: 8080
      protocol: TCP
      name: nyx-api
    env:
    - name: NODE_ID
      value: "vm${VM_NUMBER}-node${NODE_ID}"
    - name: GLOBAL_NODE_ID
      value: "${GLOBAL_NODE_ID}"
    - name: VM_NUMBER
      value: "${VM_NUMBER}"
    - name: RUST_LOG
      value: "info,nyx_core=debug"
    - name: NYX_CONFIG
      value: "/etc/nyx/nyx.toml"
    volumeMounts:
    - name: config
      mountPath: /etc/nyx
    - name: data
      mountPath: /var/lib/nyx
    resources:
      requests:
        memory: "256Mi"
        cpu: "250m"
      limits:
        memory: "512Mi"
        cpu: "500m"
  volumes:
  - name: config
    configMap:
      name: nyx-config
  - name: data
    emptyDir: {}
---
apiVersion: v1
kind: Service
metadata:
  name: mix-node-${NODE_ID}
  namespace: nyxnet-vm${VM_NUMBER}
spec:
  selector:
    app: nyx-mix
    node: "node${NODE_ID}"
  ports:
  - name: nyx-udp
    port: 9999
    targetPort: 9999
    protocol: UDP
  - name: nyx-api
    port: 8080
    targetPort: 8080
    protocol: TCP
  type: ClusterIP
EOF
    
    log_info "Deployed mix-node-${NODE_ID} (Global Node ${GLOBAL_NODE_ID})"
done

################################################################################
# 4. Control Planeサービス（Directory Authority）
################################################################################
log_info "Step 4/5: Deploying Control Plane services..."

# VM1でのみDirectory Authorityを起動
if [ "$VM_NUMBER" == "1" ]; then
    cat <<EOF | kubectl apply -f -
apiVersion: apps/v1
kind: Deployment
metadata:
  name: directory-authority
  namespace: nyxnet-vm1
spec:
  replicas: 1
  selector:
    matchLabels:
      app: directory-authority
  template:
    metadata:
      labels:
        app: directory-authority
    spec:
      containers:
      - name: directory
        image: nyxnet/daemon:latest
        imagePullPolicy: Never
        command: ["/usr/local/bin/nyx-daemon"]
        args: ["--mode", "directory"]
        ports:
        - containerPort: 8090
          name: directory
        env:
        - name: RUST_LOG
          value: "info,nyx_control=debug"
---
apiVersion: v1
kind: Service
metadata:
  name: directory-authority
  namespace: nyxnet-vm1
spec:
  selector:
    app: directory-authority
  ports:
  - port: 8090
    targetPort: 8090
  type: NodePort
  externalTrafficPolicy: Local
EOF
    log_info "Directory Authority deployed on VM1"
fi

################################################################################
# 5. デプロイ状態確認
################################################################################
log_info "Step 5/5: Verifying deployment..."

sleep 5

kubectl get pods -n nyxnet-vm${VM_NUMBER}
kubectl get svc -n nyxnet-vm${VM_NUMBER}

# デプロイ情報を保存
cat > ~/nyxnet/deployment-info.json <<EOF
{
  "vm_number": ${VM_NUMBER},
  "namespace": "nyxnet-vm${VM_NUMBER}",
  "mix_nodes": 3,
  "deployed_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "global_node_ids": [
    $(($VM_NUMBER - 1) * 3 + 1),
    $(($VM_NUMBER - 1) * 3 + 2),
    $(($VM_NUMBER - 1) * 3 + 3)
  ]
}
EOF

log_info "=========================================="
log_info "NyxNet Deployment Complete on VM-${VM_NUMBER}!"
log_info "=========================================="
log_info "Namespace: nyxnet-vm${VM_NUMBER}"
log_info "Mix Nodes: 3 (Global IDs: $((($VM_NUMBER - 1) * 3 + 1))-$((($VM_NUMBER - 1) * 3 + 3)))"
log_info ""
log_info "Check status:"
log_info "  kubectl get pods -n nyxnet-vm${VM_NUMBER}"
log_info "  kubectl logs -n nyxnet-vm${VM_NUMBER} mix-node-1"
