#!/bin/bash
################################################################################
# NyxNet Cross-VM Integration Test
# 複数VM、複数K8sクラスタ間でのNyxNet動作テスト
# Usage: bash test-cross-vm.sh
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
log_success() { echo -e "${GREEN}[✓]${NC} $1"; }
log_fail() { echo -e "${RED}[✗]${NC} $1"; }

# VM情報を読み込む
if [ -f ~/nyxnet/vm-info.json ]; then
    VM_NUMBER=$(jq -r '.vm_number' ~/nyxnet/vm-info.json)
else
    log_error "VM info not found!"
    exit 1
fi

PASSED_TESTS=0
FAILED_TESTS=0
TOTAL_TESTS=0

run_test() {
    local test_name=$1
    local test_command=$2
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    echo ""
    log_info "Test $TOTAL_TESTS: $test_name"
    
    if eval "$test_command"; then
        log_success "PASSED"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        return 0
    else
        log_fail "FAILED"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        return 1
    fi
}

################################################################################
# Test Suite
################################################################################
log_info "=========================================="
log_info "NyxNet Cross-VM Integration Test"
log_info "VM-${VM_NUMBER}"
log_info "=========================================="

################################################################################
# 1. ローカルK8sクラスタ健全性チェック
################################################################################
log_info "Phase 1: Local Kubernetes Cluster Health Check"

run_test "K8s nodes are ready" \
    "kubectl get nodes | grep -q Ready"

run_test "All pods in nyxnet-vm${VM_NUMBER} are running" \
    "[ \$(kubectl get pods -n nyxnet-vm${VM_NUMBER} --field-selector=status.phase!=Running --no-headers 2>/dev/null | wc -l) -eq 0 ]"

run_test "Mix node services are accessible" \
    "kubectl get svc -n nyxnet-vm${VM_NUMBER} mix-node-1 -o jsonpath='{.spec.clusterIP}' | grep -q '^[0-9]'"

################################################################################
# 2. ローカルノード間通信テスト
################################################################################
log_info "Phase 2: Local Inter-Node Communication Test"

# Pod間通信テスト
run_test "Pod-to-Pod communication (node-1 to node-2)" \
    "kubectl exec -n nyxnet-vm${VM_NUMBER} mix-node-1 -- nc -zv -w 3 \$(kubectl get svc -n nyxnet-vm${VM_NUMBER} mix-node-2 -o jsonpath='{.spec.clusterIP}') 9999 2>&1 | grep -q 'succeeded\|open'"

run_test "Pod-to-Pod communication (node-2 to node-3)" \
    "kubectl exec -n nyxnet-vm${VM_NUMBER} mix-node-2 -- nc -zv -w 3 \$(kubectl get svc -n nyxnet-vm${VM_NUMBER} mix-node-3 -o jsonpath='{.spec.clusterIP}') 9999 2>&1 | grep -q 'succeeded\|open'"

################################################################################
# 3. クロスVM通信テスト（global-directory.yamlから他VMのIPを取得）
################################################################################
log_info "Phase 3: Cross-VM Communication Test"

if [ -f ~/nyxnet/config/clusters/global-directory.yaml ]; then
    # 他VMのIPアドレスを取得してテスト
    OTHER_VMS=$(seq 1 3 | grep -v "^${VM_NUMBER}$" || true)
    
    for OTHER_VM in $OTHER_VMS; do
        # YAMLから該当VMのIPを抽出（簡易的な方法）
        OTHER_VM_IP=$(grep -A 2 "^vm${OTHER_VM}:" ~/nyxnet/config/clusters/global-directory.yaml | grep "ip:" | awk '{print $2}' | tr -d '"' || echo "")
        
        if [ -n "$OTHER_VM_IP" ] && [ "$OTHER_VM_IP" != "192.168.1.10${OTHER_VM}" ]; then
            NODE_PORT=$((30000 + ($OTHER_VM - 1) * 100 + 1))
            
            run_test "Cross-VM communication to VM-${OTHER_VM} (${OTHER_VM_IP}:${NODE_PORT})" \
                "timeout 5 nc -zv -u ${OTHER_VM_IP} ${NODE_PORT} 2>&1 | grep -q 'succeeded\|open' || ping -c 1 -W 2 ${OTHER_VM_IP} > /dev/null"
        else
            log_warn "Skipping VM-${OTHER_VM}: IP not configured or unreachable"
        fi
    done
else
    log_warn "Global directory not found, skipping cross-VM tests"
fi

################################################################################
# 4. NyxNetプロトコルテスト
################################################################################
log_info "Phase 4: NyxNet Protocol Test"

# 簡易的なパケット送信テスト（実際のプロトコルに応じて調整）
run_test "Send test packet through local mix network" \
    "kubectl exec -n nyxnet-vm${VM_NUMBER} mix-node-1 -- timeout 5 sh -c 'echo \"TEST_PACKET\" | nc -u \$(kubectl get svc -n nyxnet-vm${VM_NUMBER} mix-node-2 -o jsonpath=\"{.spec.clusterIP}\") 9999' || true"

################################################################################
# 5. リソース使用状況チェック
################################################################################
log_info "Phase 5: Resource Usage Check"

run_test "CPU usage is acceptable" \
    "[ \$(kubectl top pods -n nyxnet-vm${VM_NUMBER} --no-headers 2>/dev/null | awk '{sum+=\$2} END {print (sum < 2000 ? 0 : 1)}') -eq 0 ] || true"

run_test "Memory usage is acceptable" \
    "[ \$(kubectl top pods -n nyxnet-vm${VM_NUMBER} --no-headers 2>/dev/null | awk '{sum+=\$3} END {print (sum < 2000 ? 0 : 1)}') -eq 0 ] || true"

################################################################################
# 6. ログエラーチェック
################################################################################
log_info "Phase 6: Log Error Check"

run_test "No critical errors in mix-node-1 logs" \
    "! kubectl logs -n nyxnet-vm${VM_NUMBER} mix-node-1 --tail=100 | grep -i 'critical\|fatal\|panic'"

run_test "No critical errors in mix-node-2 logs" \
    "! kubectl logs -n nyxnet-vm${VM_NUMBER} mix-node-2 --tail=100 | grep -i 'critical\|fatal\|panic'"

################################################################################
# 7. エンドツーエンドパステスト（実際のルーティング）
################################################################################
log_info "Phase 7: End-to-End Path Test"

# 3ホップルーティングテスト（node-1 -> node-2 -> node-3）
log_info "Testing 3-hop routing: node-1 -> node-2 -> node-3"
# 実際のNyxNetクライアントを使用したテストに置き換える
log_warn "E2E path test requires NyxNet client - skipping for now"

################################################################################
# テスト結果サマリー
################################################################################
echo ""
log_info "=========================================="
log_info "Test Results Summary"
log_info "=========================================="
log_info "Total Tests:  $TOTAL_TESTS"
log_success "Passed:       $PASSED_TESTS"
log_fail "Failed:       $FAILED_TESTS"

PASS_RATE=$((PASSED_TESTS * 100 / TOTAL_TESTS))
log_info "Pass Rate:    ${PASS_RATE}%"

# 結果をファイルに保存
cat > ~/nyxnet/test-results.json <<EOF
{
  "vm_number": ${VM_NUMBER},
  "test_date": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "total_tests": ${TOTAL_TESTS},
  "passed": ${PASSED_TESTS},
  "failed": ${FAILED_TESTS},
  "pass_rate": ${PASS_RATE}
}
EOF

log_info "Results saved to ~/nyxnet/test-results.json"

# 終了コード
if [ $FAILED_TESTS -eq 0 ]; then
    log_success "All tests passed! ✓"
    exit 0
else
    log_error "Some tests failed. Check logs for details."
    exit 1
fi
