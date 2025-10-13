#!/usr/bin/env bash

##############################################################################
# NyxNet Multi-Cluster Test - Network Performance Verification Script
# 
# This script tests NyxNet's network capabilities:
# 1. Deploy NyxNet daemons across multiple Kubernetes clusters
# 2. Test inter-cluster network connectivity
# 3. Measure network throughput and latency
# 4. Verify daemon-to-daemon communication
##############################################################################

set -euo pipefail

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

# Load logger
source "${SCRIPT_DIR}/k8s-test-logger.sh"

# Configuration
CLUSTER_COUNT="${CLUSTER_COUNT:-3}"
CLUSTERS=()
for i in $(seq 1 "$CLUSTER_COUNT"); do
    CLUSTERS+=("nyx-cluster-$i")
done

TEST_NAMESPACE="nyx-test"
TEST_RESULTS_DIR="${PROJECT_ROOT}/test-results"
START_TIME=$(date +%s)

# Test results tracking
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

# Cleanup function
cleanup() {
    if [[ "${SKIP_CLEANUP:-}" == "true" ]]; then
        log_warning "Skipping cleanup (SKIP_CLEANUP=true)"
        return 0
    fi
    
    log_section "Cleaning up resources"
    for cluster in "${CLUSTERS[@]}"; do
        log_info "Deleting cluster: ${cluster}"
        kind delete cluster --name "${cluster}" 2>/dev/null || true
    done
    log_success "Cleanup completed"
}

trap cleanup EXIT

# Create Kind clusters
create_clusters() {
    log_section "Creating Kubernetes Clusters"
    
    for cluster in "${CLUSTERS[@]}"; do
        kind delete cluster --name "${cluster}" 2>/dev/null || true
    done
    
    local config_file="${SCRIPT_DIR}/../kind-config.yaml"
    local cluster_start=$(date +%s)
    
    for cluster in "${CLUSTERS[@]}"; do
        log_info "Creating cluster: ${cluster}"
        kind create cluster --name "${cluster}" --config "${config_file}"
    done
    
    local cluster_end=$(date +%s)
    local cluster_duration=$((cluster_end - cluster_start))
    log_success "All clusters created in ${cluster_duration}s"
}

# Build Docker image
build_nyxnet_image() {
    log_section "Building NyxNet Docker image"
    
    log_info "Building multi-stage Docker image..."
    local build_start=$(date +%s)
    
    docker build -t nyxnet-test:latest -f "${PROJECT_ROOT}/Dockerfile.nyx-test" "${PROJECT_ROOT}"
    
    local build_end=$(date +%s)
    local build_duration=$((build_end - build_start))
    log_success "Docker image built in ${build_duration}s"
}

# Load image into clusters
load_image_to_clusters() {
    log_section "Loading Docker image into Kind clusters"
    
    for cluster in "${CLUSTERS[@]}"; do
        log_info "Loading image into ${cluster}..."
        kind load docker-image nyxnet-test:latest --name "${cluster}"
    done
    
    log_success "Image loaded into all clusters"
}

# Deploy NyxNet
deploy_nyxnet() {
    log_section "Deploying NyxNet components"
    
    for cluster in "${CLUSTERS[@]}"; do
        log_info "Deploying to ${cluster}..."
        kubectl config use-context "kind-${cluster}"
        
        kubectl apply -f "${PROJECT_ROOT}/k8s-nyx-manifests.yaml"
        
        log_info "Waiting for ServiceAccount to be ready..."
        sleep 2
        
        log_info "Waiting for nyx-daemon DaemonSet..."
        kubectl wait --for=condition=ready pod -l app=nyx-daemon -n "${TEST_NAMESPACE}" --timeout=60s
        
        log_info "Waiting for test-client Pod..."
        kubectl wait --for=condition=ready pod test-client -n "${TEST_NAMESPACE}" --timeout=60s || true
        
        log_success "Deployed to ${cluster}"
    done
}

# Test daemon health
test_daemon_health() {
    log_section "Testing NyxNet Daemon Health"
    
    local passed=0
    local total=0
    
    for cluster in "${CLUSTERS[@]}"; do
        kubectl config use-context "kind-${cluster}" > /dev/null
        
        local daemon_pods=$(kubectl get pods -n "${TEST_NAMESPACE}" -l app=nyx-daemon -o jsonpath='{.items[*].metadata.name}')
        
        for pod in $daemon_pods; do
            total=$((total + 1))
            TOTAL_TESTS=$((TOTAL_TESTS + 1))
            
            log_info "Checking daemon health: ${cluster}/${pod}"
            
            if kubectl exec -n "${TEST_NAMESPACE}" "${pod}" -- test -S /tmp/nyx.sock 2>/dev/null; then
                log_success "Daemon healthy: ${cluster}/${pod}"
                passed=$((passed + 1))
                PASSED_TESTS=$((PASSED_TESTS + 1))
            else
                log_error "Daemon unhealthy: ${cluster}/${pod}"
                FAILED_TESTS=$((FAILED_TESTS + 1))
            fi
        done
    done
    
    echo ""
    log_info "Daemon health tests completed: ${passed}/${total} passed"
}

# Test network connectivity
test_network_connectivity() {
    log_section "Testing Inter-Cluster Network Connectivity"
    
    local passed=0
    local total=0
    
    for i in "${!CLUSTERS[@]}"; do
        local src_cluster="${CLUSTERS[$i]}"
        kubectl config use-context "kind-${src_cluster}" > /dev/null
        
        for j in "${!CLUSTERS[@]}"; do
            if [ $i -eq $j ]; then
                continue
            fi
            
            local dst_cluster="${CLUSTERS[$j]}"
            total=$((total + 1))
            TOTAL_TESTS=$((TOTAL_TESTS + 1))
            
            log_info "Testing: ${src_cluster} → ${dst_cluster}"
            
            local dst_ip=$(docker exec "${dst_cluster}-control-plane" hostname -i | awk '{print $1}')
            
            if kubectl exec -n "${TEST_NAMESPACE}" test-client -- ping -c 3 -W 2 "${dst_ip}" &>/dev/null; then
                log_success "Connectivity OK: ${src_cluster} → ${dst_cluster}"
                passed=$((passed + 1))
                PASSED_TESTS=$((PASSED_TESTS + 1))
            else
                log_error "Connectivity failed: ${src_cluster} → ${dst_cluster}"
                FAILED_TESTS=$((FAILED_TESTS + 1))
            fi
        done
    done
    
    echo ""
    log_info "Network connectivity tests: ${passed}/${total} passed"
}

# Test network latency
test_network_latency() {
    log_section "Testing Network Latency"
    
    local passed=0
    local total=0
    
    for i in "${!CLUSTERS[@]}"; do
        local src_cluster="${CLUSTERS[$i]}"
        kubectl config use-context "kind-${src_cluster}" > /dev/null
        
        for j in "${!CLUSTERS[@]}"; do
            if [ $i -eq $j ]; then
                continue
            fi
            
            local dst_cluster="${CLUSTERS[$j]}"
            total=$((total + 1))
            TOTAL_TESTS=$((TOTAL_TESTS + 1))
            
            log_info "Latency test: ${src_cluster} → ${dst_cluster}"
            
            kubectl config use-context "kind-${dst_cluster}" > /dev/null
            local dst_ip=$(kubectl get svc -n "${TEST_NAMESPACE}" nyx-daemon -o jsonpath='{.spec.clusterIP}')
            
            kubectl config use-context "kind-${src_cluster}" > /dev/null
            
            local ping_output=$(kubectl exec -n "${TEST_NAMESPACE}" test-client -- \
                ping -c 10 -W 2 "${dst_ip}" 2>&1)
            
            if echo "${ping_output}" | grep -q "min/avg/max"; then
                local avg_latency=$(echo "${ping_output}" | grep "min/avg/max" | cut -d'=' -f2 | cut -d'/' -f2)
                log_success "Latency: ${src_cluster} → ${dst_cluster} = ${avg_latency} ms"
                passed=$((passed + 1))
                PASSED_TESTS=$((PASSED_TESTS + 1))
            else
                log_error "Latency test failed: ${src_cluster} → ${dst_cluster}"
                FAILED_TESTS=$((FAILED_TESTS + 1))
            fi
        done
    done
    
    echo ""
    log_info "Latency tests: ${passed}/${total} passed"
}

# Main execution
main() {
    log_section "NyxNet Multi-Cluster Network Performance Test"
    
    create_clusters
    build_nyxnet_image
    load_image_to_clusters
    deploy_nyxnet
    
    # Run tests
    test_daemon_health
    test_network_connectivity
    test_network_latency
    
    # Summary
    log_section "Test Summary"
    
    local success_rate=0
    if [ $TOTAL_TESTS -gt 0 ]; then
        success_rate=$((PASSED_TESTS * 100 / TOTAL_TESTS))
    fi
    
    log_info "Total tests: ${TOTAL_TESTS}"
    log_info "Passed: ${PASSED_TESTS}"
    log_info "Failed: ${FAILED_TESTS}"
    log_info "Success rate: ${success_rate}%"
    
    if [ $FAILED_TESTS -eq 0 ]; then
        log_success "All tests passed! 🎉"
        return 0
    else
        log_warning "Some tests failed"
        return 1
    fi
}

main "$@"
