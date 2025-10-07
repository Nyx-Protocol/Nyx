#!/usr/bin/env bash

set -euo pipefail

# スクリプトディレクトリ取得
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

# ログシステム読み込み
source "${SCRIPT_DIR}/k8s-test-logger.sh"

# バージョン情報
KUBECTL_VERSION="v1.28.0"
KIND_VERSION="v0.20.0"
DOCKER_COMPOSE_VERSION="v2.23.0"

# グローバル変数
CLUSTERS=("nyx-cluster-1" "nyx-cluster-2" "nyx-cluster-3")
TEST_NAMESPACE="nyx-test"
TEST_RESULTS_DIR="${PROJECT_ROOT}/test-results"
START_TIME=$(date +%s)

# テスト結果追跡
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0
TEST_DETAILS=()

# クリーンアップ関数
cleanup() {
    log_section "Cleaning up resources"
    
    for cluster in "${CLUSTERS[@]}"; do
        log_info "Deleting cluster: ${cluster}"
        kind delete cluster --name "${cluster}" 2>/dev/null || true
    done
    
    log_success "Cleanup completed"
}

# シグナルハンドラー
trap cleanup EXIT INT TERM

# rootチェック
if [ "$EUID" -eq 0 ]; then
    IS_ROOT=true
    SUDO_CMD=""
else
    IS_ROOT=false
    SUDO_CMD="sudo"
fi

# 依存関係チェック関数
check_command() {
    command -v "$1" >/dev/null 2>&1
}

# Dockerインストール
install_docker() {
    log_section "Installing Docker"
    
    if check_command docker; then
        log_info "Docker is already installed: $(docker --version)"
        
        # Dockerが起動しているか確認
        if ! docker info >/dev/null 2>&1; then
            log_warning "Docker daemon is not running. Starting..."
            $SUDO_CMD systemctl start docker 2>/dev/null || $SUDO_CMD service docker start 2>/dev/null || true
            sleep 5
        fi
        
        # ユーザーがdockerグループに所属しているか確認（rootでない場合のみ）
        if [ "$IS_ROOT" = false ] && ! groups | grep -q docker; then
            log_warning "Adding current user to docker group..."
            $SUDO_CMD usermod -aG docker "$USER"
            log_warning "You may need to log out and back in for this to take effect"
            log_info "Attempting to use sudo for docker commands in this session..."
        fi
        
        return 0
    fi
    
    local install_start=$(date +%s)
    log_info "Docker not found. Installing..."
    
    # 古いバージョンを削除
    $SUDO_CMD apt-get remove -y docker docker-engine docker.io containerd runc 2>/dev/null || true
    
    # 依存関係インストール
    $SUDO_CMD apt-get update
    $SUDO_CMD apt-get install -y \
        ca-certificates \
        curl \
        gnupg \
        lsb-release
    
    # Docker GPGキー追加
    $SUDO_CMD install -m 0755 -d /etc/apt/keyrings
    curl -fsSL https://download.docker.com/linux/ubuntu/gpg | $SUDO_CMD gpg --dearmor -o /etc/apt/keyrings/docker.gpg
    $SUDO_CMD chmod a+r /etc/apt/keyrings/docker.gpg
    
    # Dockerリポジトリ追加
    echo \
      "deb [arch=$(dpkg --print-architecture) signed-by=/etc/apt/keyrings/docker.gpg] https://download.docker.com/linux/ubuntu \
      $(lsb_release -cs) stable" | $SUDO_CMD tee /etc/apt/sources.list.d/docker.list > /dev/null
    
    # Dockerインストール
    $SUDO_CMD apt-get update
    $SUDO_CMD apt-get install -y docker-ce docker-ce-cli containerd.io docker-buildx-plugin docker-compose-plugin
    
    # Docker起動
    $SUDO_CMD systemctl start docker
    $SUDO_CMD systemctl enable docker
    
    # 現在のユーザーをdockerグループに追加（rootでない場合のみ）
    if [ "$IS_ROOT" = false ]; then
        $SUDO_CMD usermod -aG docker "$USER"
        log_warning "You may need to log out and back in for docker group changes to take effect"
    fi
    
    local install_end=$(date +%s)
    local install_duration=$((install_end - install_start))
    
    log_success "Docker installed successfully in ${install_duration}s: $(docker --version)"
}

# kubectlインストール
install_kubectl() {
    log_section "Installing kubectl"
    
    if check_command kubectl; then
        log_info "kubectl is already installed: $(kubectl version --client --short 2>/dev/null || kubectl version --client)"
        return 0
    fi
    
    log_info "kubectl not found. Installing..."
    
    local start_time=$(date +%s)
    log_info "Downloading kubectl ${KUBECTL_VERSION}..."
    curl -# -LO "https://dl.k8s.io/release/${KUBECTL_VERSION}/bin/linux/amd64/kubectl"
    curl -sS -LO "https://dl.k8s.io/release/${KUBECTL_VERSION}/bin/linux/amd64/kubectl.sha256"
    local end_time=$(date +%s)
    local duration=$((end_time - start_time))
    
    log_info "Downloaded in ${duration}s"
    
    log_info "Verifying checksum..."
    echo "$(cat kubectl.sha256)  kubectl" | sha256sum --check
    
    $SUDO_CMD install -o root -g root -m 0755 kubectl /usr/local/bin/kubectl
    rm kubectl kubectl.sha256
    
    log_success "kubectl installed successfully: $(kubectl version --client --short 2>/dev/null || kubectl version --client)"
}

# kindインストール
install_kind() {
    log_section "Installing kind"
    
    if check_command kind; then
        log_info "kind is already installed: $(kind version)"
        return 0
    fi
    
    log_info "kind not found. Installing..."
    
    local start_time=$(date +%s)
    log_info "Downloading kind ${KIND_VERSION}..."
    curl -# -Lo ./kind "https://kind.sigs.k8s.io/dl/${KIND_VERSION}/kind-linux-amd64"
    local end_time=$(date +%s)
    local duration=$((end_time - start_time))
    local file_size=$(ls -lh ./kind | awk '{print $5}')
    
    log_info "Downloaded ${file_size} in ${duration}s"
    
    chmod +x ./kind
    $SUDO_CMD mv ./kind /usr/local/bin/kind
    
    log_success "kind installed successfully: $(kind version)"
}

# 必要なツールをインストール
install_dependencies() {
    log_header "CHECKING AND INSTALLING DEPENDENCIES"
    
    # 基本ツールのインストール
    log_section "Installing basic tools"
    $SUDO_CMD apt-get update -qq
    $SUDO_CMD apt-get install -y curl wget git jq bc >/dev/null 2>&1
    log_success "Basic tools installed"
    
    # Docker
    install_docker
    
    # kubectl
    install_kubectl
    
    # kind
    install_kind
    
    log_success "All dependencies are ready!"
    echo ""
}

# システムチェック
check_system() {
    log_section "System Requirements Check"
    
    # メモリチェック
    local total_mem=$(free -g | awk '/^Mem:/{print $2}')
    if [ "$total_mem" -lt 4 ]; then
        log_warning "Low memory detected: ${total_mem}GB (recommended: 8GB+)"
    else
        log_success "Memory: ${total_mem}GB"
    fi
    
    # ディスクスペースチェック
    local free_space=$(df -BG / | awk 'NR==2 {print $4}' | sed 's/G//')
    if [ "$free_space" -lt 10 ]; then
        log_warning "Low disk space: ${free_space}GB (recommended: 20GB+)"
    else
        log_success "Disk space: ${free_space}GB available"
    fi
    
    # CPUコア数チェック
    local cpu_cores=$(nproc)
    log_success "CPU cores: ${cpu_cores}"
    
    echo ""
}

# システム制限の調整
adjust_system_limits() {
    log_section "Adjusting system limits"
    
    # inotify制限の確認と調整
    local current_watches=$(cat /proc/sys/fs/inotify/max_user_watches 2>/dev/null || echo "0")
    local current_instances=$(cat /proc/sys/fs/inotify/max_user_instances 2>/dev/null || echo "0")
    
    log_info "Current inotify watches: ${current_watches}"
    log_info "Current inotify instances: ${current_instances}"
    
    # 制限を増やす
    if [ "$current_watches" -lt 524288 ]; then
        log_info "Increasing inotify max_user_watches to 524288..."
        echo 524288 | $SUDO_CMD tee /proc/sys/fs/inotify/max_user_watches > /dev/null
        
        # 永続化
        if [ ! -f /etc/sysctl.d/99-k8s-inotify.conf ]; then
            echo "fs.inotify.max_user_watches=524288" | $SUDO_CMD tee /etc/sysctl.d/99-k8s-inotify.conf > /dev/null
            echo "fs.inotify.max_user_instances=512" | $SUDO_CMD tee -a /etc/sysctl.d/99-k8s-inotify.conf > /dev/null
        fi
    fi
    
    if [ "$current_instances" -lt 512 ]; then
        log_info "Increasing inotify max_user_instances to 512..."
        echo 512 | $SUDO_CMD tee /proc/sys/fs/inotify/max_user_instances > /dev/null
    fi
    
    # ファイルディスクリプタ制限の確認
    local file_max=$(cat /proc/sys/fs/file-max 2>/dev/null || echo "0")
    log_info "System file-max: ${file_max}"
    
    if [ "$file_max" -lt 2097152 ]; then
        log_info "Increasing fs.file-max to 2097152..."
        echo 2097152 | $SUDO_CMD tee /proc/sys/fs/file-max > /dev/null
        
        if [ ! -f /etc/sysctl.d/99-k8s-limits.conf ]; then
            echo "fs.file-max=2097152" | $SUDO_CMD tee /etc/sysctl.d/99-k8s-limits.conf > /dev/null
        fi
    fi
    
    # ulimit調整
    ulimit -n 65536 2>/dev/null || log_warning "Could not adjust ulimit"
    
    log_success "System limits adjusted successfully"
    echo ""
}

# Kindクラスター作成
create_clusters() {
    log_section "Creating Kind clusters"
    
    local total=${#CLUSTERS[@]}
    local current=0
    local cluster_start=$(date +%s)
    
    for i in "${!CLUSTERS[@]}"; do
        local cluster="${CLUSTERS[$i]}"
        local config_file="${PROJECT_ROOT}/k8s-multi-cluster-config-$((i+1)).yaml"
        
        current=$((current + 1))
        log_step "$current" "$total" "Creating cluster: ${cluster}"
        
        if kind get clusters 2>/dev/null | grep -q "^${cluster}$"; then
            log_warning "Cluster ${cluster} already exists, deleting..."
            kind delete cluster --name "${cluster}"
        fi
        
        local single_start=$(date +%s)
        kind create cluster --config "${config_file}" --wait 5m > /dev/null 2>&1 &
        local pid=$!
        spinner $pid "Creating ${cluster}"
        wait $pid
        local single_end=$(date +%s)
        local single_duration=$((single_end - single_start))
        
        log_success "Cluster ${cluster} created in ${single_duration}s"
        show_progress $current $total
    done
    
    local cluster_end=$(date +%s)
    local total_duration=$((cluster_end - cluster_start))
    
    echo ""
    log_info "All clusters created in ${total_duration}s (average: $((total_duration / total))s per cluster)"
    echo ""
}

# クラスター準備
prepare_clusters() {
    log_section "Preparing clusters"
    
    local total=${#CLUSTERS[@]}
    local current=0
    
    for cluster in "${CLUSTERS[@]}"; do
        current=$((current + 1))
        log_step "$current" "$total" "Configuring cluster: ${cluster}"
        
        # kubectlコンテキスト設定
        kubectl config use-context "kind-${cluster}" > /dev/null
        
        # 名前空間作成
        kubectl create namespace "${TEST_NAMESPACE}" --dry-run=client -o yaml | kubectl apply -f - > /dev/null
        
        log_success "Cluster ${cluster} prepared"
        show_progress $current $total
    done
    
    echo ""
}

# テストPod展開
deploy_test_pods() {
    log_section "Deploying test pods"
    
    local total=${#CLUSTERS[@]}
    local current=0
    local deploy_start=$(date +%s)
    
    for i in "${!CLUSTERS[@]}"; do
        local cluster="${CLUSTERS[$i]}"
        local cluster_num=$((i + 1))
        
        current=$((current + 1))
        log_step "$current" "$total" "Deploying to ${cluster}"
        
        local pod_start=$(date +%s)
        kubectl config use-context "kind-${cluster}" > /dev/null
        
        # テストPod作成（iperf3用のHostPortを公開）
        cat <<EOF | kubectl apply -f - > /dev/null
apiVersion: v1
kind: Pod
metadata:
  name: test-pod-${cluster_num}
  namespace: ${TEST_NAMESPACE}
  labels:
    app: nyx-test
    cluster: ${cluster}
spec:
  hostNetwork: false
  containers:
  - name: test-container
    image: nicolaka/netshoot:latest
    command: ["sleep", "3600"]
    env:
    - name: CLUSTER_NAME
      value: "${cluster}"
    ports:
    - name: iperf3
      containerPort: 5201
      hostPort: $((5201 + i))
      protocol: TCP
    resources:
      requests:
        memory: "128Mi"
        cpu: "100m"
      limits:
        memory: "512Mi"
        cpu: "500m"
---
apiVersion: v1
kind: Service
metadata:
  name: test-service-${cluster_num}
  namespace: ${TEST_NAMESPACE}
spec:
  type: NodePort
  selector:
    app: nyx-test
    cluster: ${cluster}
  ports:
  - port: 80
    targetPort: 80
    nodePort: $((30080 + i))
EOF
        
        # Pod起動待機
        kubectl wait --for=condition=ready pod/test-pod-${cluster_num} \
            -n "${TEST_NAMESPACE}" --timeout=120s > /dev/null 2>&1 || true
        
        local pod_end=$(date +%s)
        local pod_duration=$((pod_end - pod_start))
        
        log_success "Deployed to ${cluster} in ${pod_duration}s"
        show_progress $current $total
    done
    
    local deploy_end=$(date +%s)
    local total_deploy=$((deploy_end - deploy_start))
    
    echo ""
    log_info "All pods deployed in ${total_deploy}s"
    echo ""
}

# クラスター情報取得
get_cluster_info() {
    local cluster=$1
    kubectl config use-context "kind-${cluster}" > /dev/null
    local pods=$(kubectl get pods -n "${TEST_NAMESPACE}" --no-headers 2>/dev/null | wc -l)
    echo "$pods"
}

# クラスター状態表示
show_clusters_status() {
    log_section "Cluster Status"
    
    for cluster in "${CLUSTERS[@]}"; do
        local pods=$(get_cluster_info "$cluster")
        show_cluster_info "$cluster" "ready" "$pods"
    done
    
    echo ""
}

# ネットワーク接続テスト
test_network_connectivity() {
    log_section "Testing network connectivity between clusters"
    
    local test_count=0
    local passed=0
    local test_start=$(date +%s)
    
    for i in "${!CLUSTERS[@]}"; do
        local src_cluster="${CLUSTERS[$i]}"
        local src_pod="test-pod-$((i + 1))"
        
        kubectl config use-context "kind-${src_cluster}" > /dev/null
        
        for j in "${!CLUSTERS[@]}"; do
            if [ $i -eq $j ]; then
                continue
            fi
            
            local dst_cluster="${CLUSTERS[$j]}"
            local dst_pod="test-pod-$((j + 1))"
            
            test_count=$((test_count + 1))
            TOTAL_TESTS=$((TOTAL_TESTS + 1))
            
            log_info "Testing: ${src_cluster} → ${dst_cluster}"
            
            # Docker内部ネットワークでのPing（Dockerネットワーク経由）
            local dst_container="${dst_cluster}-control-plane"
            local dst_ip=$(docker inspect -f '{{range.NetworkSettings.Networks}}{{.IPAddress}}{{end}}' "${dst_container}" 2>/dev/null || echo "")
            
            if [ -n "$dst_ip" ]; then
                # レイテンシ測定 (10回ping)
                local ping_output=$(kubectl exec -n "${TEST_NAMESPACE}" "${src_pod}" -- ping -c 10 -W 2 "${dst_ip}" 2>/dev/null || echo "")
                
                if echo "$ping_output" | grep -q "10 packets transmitted"; then
                    # 平均レイテンシを抽出
                    local latency=$(echo "$ping_output" | grep "rtt min/avg/max" | awk -F'/' '{print $5}' || echo "0")
                    local packet_loss=$(echo "$ping_output" | grep "packet loss" | awk '{print $6}' | sed 's/%//' || echo "100")
                    
                    if [ "${packet_loss%.*}" -lt 50 ]; then
                        log_success "Connection successful: ${src_cluster} → ${dst_cluster} | Latency: ${latency}ms | Loss: ${packet_loss}%"
                        passed=$((passed + 1))
                        PASSED_TESTS=$((PASSED_TESTS + 1))
                        TEST_DETAILS+=("PASS|${src_cluster}|${dst_cluster}|Latency ${latency}ms, Loss ${packet_loss}%")
                    else
                        log_error "High packet loss: ${src_cluster} → ${dst_cluster} | Loss: ${packet_loss}%"
                        FAILED_TESTS=$((FAILED_TESTS + 1))
                        TEST_DETAILS+=("FAIL|${src_cluster}|${dst_cluster}|High packet loss ${packet_loss}%")
                    fi
                else
                    log_error "Connection failed: ${src_cluster} → ${dst_cluster} (${dst_ip})"
                    FAILED_TESTS=$((FAILED_TESTS + 1))
                    TEST_DETAILS+=("FAIL|${src_cluster}|${dst_cluster}|Ping failed to ${dst_ip}")
                fi
            else
                log_warning "Could not resolve IP for ${dst_cluster}"
                FAILED_TESTS=$((FAILED_TESTS + 1))
                TEST_DETAILS+=("FAIL|${src_cluster}|${dst_cluster}|IP resolution failed")
            fi
        done
    done
    
    local test_end=$(date +%s)
    local test_duration=$((test_end - test_start))
    
    echo ""
    log_info "Network tests completed in ${test_duration}s: ${passed}/${test_count} passed"
}

# Pod間通信テスト
test_pod_communication() {
    log_section "Testing pod-to-pod communication"
    
    local test_count=0
    local passed=0
    
    for i in "${!CLUSTERS[@]}"; do
        local cluster="${CLUSTERS[$i]}"
        local pod="test-pod-$((i + 1))"
        
        kubectl config use-context "kind-${cluster}" > /dev/null
        
        test_count=$((test_count + 1))
        TOTAL_TESTS=$((TOTAL_TESTS + 1))
        
        log_info "Testing pod health in ${cluster}"
        
        if kubectl exec -n "${TEST_NAMESPACE}" "${pod}" -- echo "health check" > /dev/null 2>&1; then
            log_success "Pod ${pod} is healthy"
            passed=$((passed + 1))
            PASSED_TESTS=$((PASSED_TESTS + 1))
            TEST_DETAILS+=("PASS|${cluster}|self|Pod health check")
        else
            log_error "Pod ${pod} health check failed"
            FAILED_TESTS=$((FAILED_TESTS + 1))
            TEST_DETAILS+=("FAIL|${cluster}|self|Pod health check")
        fi
    done
    
    echo ""
    log_info "Pod communication tests completed: ${passed}/${test_count} passed"
}

# スループット測定テスト
test_throughput() {
    log_section "Testing network throughput between clusters"
    
    local test_count=0
    local passed=0
    
    # 各クラスターにiperfサーバーを起動
    log_info "Starting iperf3 servers in all clusters..."
    
    for i in "${!CLUSTERS[@]}"; do
        local cluster="${CLUSTERS[$i]}"
        local pod="test-pod-$((i + 1))"
        
        kubectl config use-context "kind-${cluster}" > /dev/null
        
        # 既存のiperf3プロセスを停止
        kubectl exec -n "${TEST_NAMESPACE}" "${pod}" -- pkill iperf3 > /dev/null 2>&1 || true
        
        # バックグラウンドでiperfサーバー起動（デーモンモードで）
        kubectl exec -n "${TEST_NAMESPACE}" "${pod}" -- sh -c "nohup iperf3 -s > /dev/null 2>&1 &" > /dev/null 2>&1
        
        if [ $? -eq 0 ]; then
            log_info "iperf3 server started on ${cluster}"
        else
            log_warning "Failed to start iperf3 server on ${cluster}"
        fi
    done
    
    # サーバー起動を待機
    log_info "Waiting for iperf3 servers to be ready..."
    sleep 5
    
    # スループット測定
    for i in "${!CLUSTERS[@]}"; do
        local src_cluster="${CLUSTERS[$i]}"
        local src_pod="test-pod-$((i + 1))"
        
        kubectl config use-context "kind-${src_cluster}" > /dev/null
        
        for j in "${!CLUSTERS[@]}"; do
            if [ $i -eq $j ]; then
                continue
            fi
            
            local dst_cluster="${CLUSTERS[$j]}"
            local dst_pod="test-pod-$((j + 1))"
            local dst_hostport=$((5201 + j))
            
            # 宛先Podがスケジュールされているノードを特定
            kubectl config use-context "kind-${dst_cluster}" > /dev/null
            local dst_node=$(kubectl get pod "${dst_pod}" -n "${TEST_NAMESPACE}" -o jsonpath='{.spec.nodeName}' 2>/dev/null || echo "")
            kubectl config use-context "kind-${src_cluster}" > /dev/null
            
            if [ -z "$dst_node" ]; then
                log_warning "Could not determine node for Pod ${dst_pod} in ${dst_cluster}"
                FAILED_TESTS=$((FAILED_TESTS + 1))
                TOTAL_TESTS=$((TOTAL_TESTS + 1))
                TEST_DETAILS+=("FAIL|${src_cluster}|${dst_cluster}|Node detection failed")
                continue
            fi
            
            # ノードのDocker IPアドレスを取得
            local dst_ip=$(docker inspect -f '{{range.NetworkSettings.Networks}}{{.IPAddress}}{{end}}' "${dst_node}" 2>/dev/null || echo "")
            
            if [ -z "$dst_ip" ]; then
                log_warning "Could not resolve IP for node ${dst_node} in ${dst_cluster}"
                FAILED_TESTS=$((FAILED_TESTS + 1))
                TOTAL_TESTS=$((TOTAL_TESTS + 1))
                TEST_DETAILS+=("FAIL|${src_cluster}|${dst_cluster}|Node IP resolution failed")
                continue
            fi
            
            test_count=$((test_count + 1))
            TOTAL_TESTS=$((TOTAL_TESTS + 1))
            
            log_info "Measuring throughput: ${src_cluster} → ${dst_cluster} (${dst_ip}:${dst_hostport})"
            
            # まず接続テスト（hostPort経由で到達可能か確認）
            if ! kubectl exec -n "${TEST_NAMESPACE}" "${src_pod}" -- nc -zv -w 2 "${dst_ip}" "${dst_hostport}" > /dev/null 2>&1; then
                log_warning "iperf3 port ${dst_hostport} not reachable on ${dst_ip}"
                FAILED_TESTS=$((FAILED_TESTS + 1))
                TEST_DETAILS+=("FAIL|${src_cluster}|${dst_cluster}|iperf3 server not reachable")
                continue
            fi
            
            # iperf3で5秒間測定（hostPort経由）
            local iperf_output=$(kubectl exec -n "${TEST_NAMESPACE}" "${src_pod}" -- iperf3 -c "${dst_ip}" -p "${dst_hostport}" -t 5 2>&1 || echo "")
            
            if echo "$iperf_output" | grep -q "sender"; then
                # テキスト出力から速度を抽出
                local throughput=$(echo "$iperf_output" | grep "sender" | awk '{print $(NF-2)" "$(NF-1)}')
                
                if [ -n "$throughput" ]; then
                    log_success "Throughput: ${src_cluster} → ${dst_cluster} | ${throughput}"
                    passed=$((passed + 1))
                    PASSED_TESTS=$((PASSED_TESTS + 1))
                    TEST_DETAILS+=("PASS|${src_cluster}|${dst_cluster}|Throughput ${throughput}")
                else
                    log_error "Could not parse throughput: ${src_cluster} → ${dst_cluster}"
                    FAILED_TESTS=$((FAILED_TESTS + 1))
                    TEST_DETAILS+=("FAIL|${src_cluster}|${dst_cluster}|Throughput parsing failed")
                fi
            else
                log_error "Failed to measure throughput: ${src_cluster} → ${dst_cluster}"
                FAILED_TESTS=$((FAILED_TESTS + 1))
                TEST_DETAILS+=("FAIL|${src_cluster}|${dst_cluster}|iperf3 connection failed")
            fi
        done
    done
    
    # クリーンアップ: iperf3サーバーを停止
    log_info "Stopping iperf3 servers..."
    for i in "${!CLUSTERS[@]}"; do
        local cluster="${CLUSTERS[$i]}"
        local pod="test-pod-$((i + 1))"
        kubectl config use-context "kind-${cluster}" > /dev/null
        kubectl exec -n "${TEST_NAMESPACE}" "${pod}" -- pkill iperf3 > /dev/null 2>&1 || true
    done
    
    echo ""
    log_info "Throughput tests completed: ${passed}/${test_count} passed"
}

# DNS解決テスト
test_dns_resolution() {
    log_section "Testing DNS resolution"
    
    local test_count=0
    local passed=0
    
    for i in "${!CLUSTERS[@]}"; do
        local cluster="${CLUSTERS[$i]}"
        local pod="test-pod-$((i + 1))"
        
        kubectl config use-context "kind-${cluster}" > /dev/null
        
        test_count=$((test_count + 1))
        TOTAL_TESTS=$((TOTAL_TESTS + 1))
        
        log_info "Testing DNS in ${cluster}"
        
        if kubectl exec -n "${TEST_NAMESPACE}" "${pod}" -- nslookup kubernetes.default > /dev/null 2>&1; then
            log_success "DNS resolution working in ${cluster}"
            passed=$((passed + 1))
            PASSED_TESTS=$((PASSED_TESTS + 1))
            TEST_DETAILS+=("PASS|${cluster}|internal|DNS resolution")
        else
            log_error "DNS resolution failed in ${cluster}"
            FAILED_TESTS=$((FAILED_TESTS + 1))
            TEST_DETAILS+=("FAIL|${cluster}|internal|DNS resolution")
        fi
    done
    
    echo ""
    log_info "DNS tests completed: ${passed}/${test_count} passed"
}

# テスト結果保存
save_test_results() {
    log_section "Saving test results"
    
    mkdir -p "${TEST_RESULTS_DIR}"
    
    local end_time=$(date +%s)
    local duration=$((end_time - START_TIME))
    local timestamp=$(date +"%Y%m%d-%H%M%S")
    
    # JSON形式で保存
    local json_file="${TEST_RESULTS_DIR}/test-results-${timestamp}.json"
    
    cat > "${json_file}" <<EOF
{
  "timestamp": "$(date -Iseconds)",
  "duration_seconds": ${duration},
  "summary": {
    "total": ${TOTAL_TESTS},
    "passed": ${PASSED_TESTS},
    "failed": ${FAILED_TESTS},
    "success_rate": $((PASSED_TESTS * 100 / TOTAL_TESTS))
  },
  "clusters": [
    $(for cluster in "${CLUSTERS[@]}"; do
      echo "    \"${cluster}\""
      if [ "$cluster" != "${CLUSTERS[-1]}" ]; then echo ","; fi
    done)
  ],
  "test_details": [
EOF
    
    local detail_count=${#TEST_DETAILS[@]}
    for i in "${!TEST_DETAILS[@]}"; do
        IFS='|' read -r status src dst desc <<< "${TEST_DETAILS[$i]}"
        echo "    {" >> "${json_file}"
        echo "      \"status\": \"${status}\"," >> "${json_file}"
        echo "      \"source\": \"${src}\"," >> "${json_file}"
        echo "      \"destination\": \"${dst}\"," >> "${json_file}"
        echo "      \"description\": \"${desc}\"" >> "${json_file}"
        if [ $i -lt $((detail_count - 1)) ]; then
            echo "    }," >> "${json_file}"
        else
            echo "    }" >> "${json_file}"
        fi
    done
    
    cat >> "${json_file}" <<EOF
  ]
}
EOF
    
    log_success "Results saved to: ${json_file}"
    
    # HTML形式でも保存
    generate_html_report "${timestamp}" "${duration}"
}

# HTMLレポート生成
generate_html_report() {
    local timestamp=$1
    local duration=$2
    local html_file="${TEST_RESULTS_DIR}/test-results-${timestamp}.html"
    
    cat > "${html_file}" <<'EOF'
<!DOCTYPE html>
<html lang="ja">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Nyx Multi-Cluster Test Results</title>
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body {
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            padding: 20px;
            min-height: 100vh;
        }
        .container {
            max-width: 1200px;
            margin: 0 auto;
            background: white;
            border-radius: 20px;
            box-shadow: 0 20px 60px rgba(0,0,0,0.3);
            overflow: hidden;
        }
        .header {
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 40px;
            text-align: center;
        }
        .header h1 {
            font-size: 2.5em;
            margin-bottom: 10px;
            text-shadow: 2px 2px 4px rgba(0,0,0,0.2);
        }
        .summary {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 20px;
            padding: 40px;
            background: #f8f9fa;
        }
        .summary-card {
            background: white;
            padding: 25px;
            border-radius: 15px;
            box-shadow: 0 4px 6px rgba(0,0,0,0.1);
            text-align: center;
            transition: transform 0.3s;
        }
        .summary-card:hover {
            transform: translateY(-5px);
        }
        .summary-card .number {
            font-size: 3em;
            font-weight: bold;
            margin: 10px 0;
        }
        .summary-card .label {
            color: #666;
            font-size: 0.9em;
            text-transform: uppercase;
            letter-spacing: 1px;
        }
        .passed { color: #28a745; }
        .failed { color: #dc3545; }
        .total { color: #667eea; }
        .duration { color: #ffc107; }
        .details {
            padding: 40px;
        }
        .details h2 {
            margin-bottom: 20px;
            color: #333;
        }
        table {
            width: 100%;
            border-collapse: collapse;
            margin-top: 20px;
        }
        th, td {
            padding: 15px;
            text-align: left;
            border-bottom: 1px solid #ddd;
        }
        th {
            background: #667eea;
            color: white;
            font-weight: 600;
            text-transform: uppercase;
            font-size: 0.85em;
            letter-spacing: 1px;
        }
        tr:hover {
            background: #f8f9fa;
        }
        .status-badge {
            display: inline-block;
            padding: 5px 15px;
            border-radius: 20px;
            font-weight: bold;
            font-size: 0.85em;
        }
        .status-pass {
            background: #d4edda;
            color: #155724;
        }
        .status-fail {
            background: #f8d7da;
            color: #721c24;
        }
        .footer {
            text-align: center;
            padding: 20px;
            color: #666;
            font-size: 0.9em;
        }
    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1>🚀 Nyx Multi-Cluster Test Results</h1>
            <p>Kubernetes Inter-Cluster Communication Test Report</p>
        </div>
        
        <div class="summary">
            <div class="summary-card">
                <div class="label">Total Tests</div>
                <div class="number total">__TOTAL__</div>
            </div>
            <div class="summary-card">
                <div class="label">Passed</div>
                <div class="number passed">__PASSED__</div>
            </div>
            <div class="summary-card">
                <div class="label">Failed</div>
                <div class="number failed">__FAILED__</div>
            </div>
            <div class="summary-card">
                <div class="label">Duration</div>
                <div class="number duration">__DURATION__s</div>
            </div>
        </div>
        
        <div class="details">
            <h2>📊 Test Details</h2>
            <table>
                <thead>
                    <tr>
                        <th>Status</th>
                        <th>Source Cluster</th>
                        <th>Destination</th>
                        <th>Description</th>
                    </tr>
                </thead>
                <tbody>
__TEST_ROWS__
                </tbody>
            </table>
        </div>
        
        <div class="footer">
            <p>Generated at __TIMESTAMP__</p>
            <p>Nyx Network - Multi-Cluster Test Framework</p>
        </div>
    </div>
</body>
</html>
EOF
    
    # プレースホルダー置換
    local test_rows=""
    for detail in "${TEST_DETAILS[@]}"; do
        IFS='|' read -r status src dst desc <<< "$detail"
        local badge_class="status-pass"
        local status_text="✅ PASS"
        if [ "$status" = "FAIL" ]; then
            badge_class="status-fail"
            status_text="❌ FAIL"
        fi
        test_rows+="                    <tr>\n"
        test_rows+="                        <td><span class=\"status-badge ${badge_class}\">${status_text}</span></td>\n"
        test_rows+="                        <td>${src}</td>\n"
        test_rows+="                        <td>${dst}</td>\n"
        test_rows+="                        <td>${desc}</td>\n"
        test_rows+="                    </tr>\n"
    done
    
    sed -i "s|__TOTAL__|${TOTAL_TESTS}|g" "${html_file}"
    sed -i "s|__PASSED__|${PASSED_TESTS}|g" "${html_file}"
    sed -i "s|__FAILED__|${FAILED_TESTS}|g" "${html_file}"
    sed -i "s|__DURATION__|${duration}|g" "${html_file}"
    sed -i "s|__TIMESTAMP__|$(date)|g" "${html_file}"
    sed -i "s|__TEST_ROWS__|${test_rows}|g" "${html_file}"
    
    log_success "HTML report saved to: ${html_file}"
}

# メイン処理
main() {
    show_banner
    
    log_header "NYX MULTI-CLUSTER KUBERNETES TEST"
    
    # システムチェック
    check_system
    
    # システム制限調整
    adjust_system_limits
    
    # 依存関係インストール
    install_dependencies
    
    # クラスター作成
    create_clusters
    
    # クラスター準備
    prepare_clusters
    
    # テストPod展開
    deploy_test_pods
    
    # クラスター状態表示
    show_clusters_status
    
    # テスト実行
    test_pod_communication
    test_dns_resolution
    test_network_connectivity
    test_throughput
    
    # 結果計算
    local end_time=$(date +%s)
    local duration=$((end_time - START_TIME))
    
    # サマリー表示
    show_summary "${TOTAL_TESTS}" "${PASSED_TESTS}" "${FAILED_TESTS}" "${duration}"
    
    # 詳細テーブル表示
    table_header "TEST RESULTS DETAILS"
    table_row "Test Case" "Status" "Details"
    for detail in "${TEST_DETAILS[@]}"; do
        IFS='|' read -r status src dst desc <<< "$detail"
        if [ "$status" = "PASS" ]; then
            table_row "${src} → ${dst}" "✅ PASSED" "${desc}"
        else
            table_row "${src} → ${dst}" "❌ FAILED" "${desc}"
        fi
    done
    table_footer
    
    # 結果保存
    save_test_results
    
    log_header "TEST COMPLETED SUCCESSFULLY!"
    
    # 終了コード
    if [ ${FAILED_TESTS} -gt 0 ]; then
        exit 1
    fi
    
    exit 0
}

# スクリプト実行
main "$@"
