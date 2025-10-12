#!/usr/bin/env bash

##############################################################################
# NyxNet Multi-Cluster Test - Mix Network Verification Script
# 
# This script tests NyxNet's anonymization capabilities:
# 1. Deploy NyxNet daemons across multiple clusters
# 2. Build 3-hop Mix Network circuits
# 3. Test SOCKS5/HTTP proxy routing through Mix Network
# 4. Verify encryption and anonymization
# 5. Measure Mix Network performance
##############################################################################

set -euo pipefail

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

# Load logger
source "${SCRIPT_DIR}/k8s-test-logger.sh"

# Configuration
CLUSTERS=("nyx-cluster-1" "nyx-cluster-2" "nyx-cluster-3")
TEST_NAMESPACE="nyx-test"
TEST_RESULTS_DIR="${PROJECT_ROOT}/test-results"
START_TIME=$(date +%s)

# Test results tracking
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0
TEST_DETAILS=()

# Cleanup function
cleanup() {
    log_section "Cleaning up resources"
    
    for cluster in "${CLUSTERS[@]}"; do
        log_info "Deleting cluster: ${cluster}"
        kind delete cluster --name "${cluster}" 2>/dev/null || true
    done
    
    log_success "Cleanup completed"
}

trap cleanup EXIT INT TERM

# Create Kind clusters
create_clusters() {
    log_section "Creating Kind clusters"
    
    local total=${#CLUSTERS[@]}
    local current=0
    local cluster_start=$(date +%s)
    
    for i in "${!CLUSTERS[@]}"; do
        local cluster="${CLUSTERS[$i]}"
        local config_file="${PROJECT_ROOT}/k8s-multi-cluster-config-$((i+1)).yaml"
        
        current=$((current + 1))
        log_info "[$current/$total] Creating cluster: ${cluster}"
        
        if kind get clusters 2>/dev/null | grep -q "^${cluster}$"; then
            log_warning "Cluster ${cluster} already exists, deleting..."
            kind delete cluster --name "${cluster}"
        fi
        
        local single_start=$(date +%s)
        kind create cluster --config "${config_file}" --wait 5m
        local single_end=$(date +%s)
        local single_duration=$((single_end - single_start))
        
        log_success "Cluster ${cluster} created in ${single_duration}s"
    done
    
    local cluster_end=$(date +%s)
    local total_duration=$((cluster_end - cluster_start))
    
    echo ""
    log_info "All clusters created in ${total_duration}s"
    echo ""
}

# Build NyxNet Docker image
build_nyxnet_image() {
    log_section "Building NyxNet Docker image"
    
    local build_start=$(date +%s)
    
    cd "${PROJECT_ROOT}"
    
    log_info "Building multi-stage Docker image..."
    docker build -f Dockerfile.nyx-test -t nyxnet-test:latest . 2>&1 | while read line; do
        log_info "$line"
    done
    
    local build_end=$(date +%s)
    local build_duration=$((build_end - build_start))
    
    log_success "Docker image built in ${build_duration}s"
}

# Load image into Kind clusters
load_image_to_clusters() {
    log_section "Loading Docker image into Kind clusters"
    
    for cluster in "${CLUSTERS[@]}"; do
        log_info "Loading image into ${cluster}..."
        kind load docker-image nyxnet-test:latest --name "${cluster}"
    done
    
    log_success "Image loaded into all clusters"
}

# Deploy NyxNet components
deploy_nyxnet() {
    log_section "Deploying NyxNet components"
    
    for cluster in "${CLUSTERS[@]}"; do
        log_info "Deploying to ${cluster}..."
        kubectl config use-context "kind-${cluster}" > /dev/null
        
        # Apply manifests
        kubectl apply -f "${PROJECT_ROOT}/k8s-nyx-manifests.yaml"
        
        # Wait for nyx-daemon to be ready
        log_info "Waiting for nyx-daemon DaemonSet..."
        kubectl wait --for=condition=ready pod \
            -l app=nyx-daemon \
            -n "${TEST_NAMESPACE}" \
            --timeout=120s || true
        
        # Wait for nyx-proxy to be ready
        log_info "Waiting for nyx-proxy Deployment..."
        kubectl wait --for=condition=ready pod \
            -l app=nyx-proxy \
            -n "${TEST_NAMESPACE}" \
            --timeout=120s || true
        
        log_success "Deployed to ${cluster}"
    done
}

# Test NyxNet daemon health
test_daemon_health() {
    log_section "Testing NyxNet Daemon Health"
    
    local test_count=0
    local passed=0
    
    for cluster in "${CLUSTERS[@]}"; do
        kubectl config use-context "kind-${cluster}" > /dev/null
        
        local pods=$(kubectl get pods -n "${TEST_NAMESPACE}" -l app=nyx-daemon -o jsonpath='{.items[*].metadata.name}')
        
        for pod in $pods; do
            test_count=$((test_count + 1))
            TOTAL_TESTS=$((TOTAL_TESTS + 1))
            
            log_info "Checking daemon health: ${cluster}/${pod}"
            
            # Check if daemon is responding on gRPC port
            if kubectl exec -n "${TEST_NAMESPACE}" "${pod}" -- sh -c "timeout 2 nc -zv localhost 9000" > /dev/null 2>&1; then
                log_success "Daemon healthy: ${cluster}/${pod}"
                passed=$((passed + 1))
                PASSED_TESTS=$((PASSED_TESTS + 1))
                TEST_DETAILS+=("PASS|${cluster}|daemon|Health check")
            else
                log_error "Daemon unhealthy: ${cluster}/${pod}"
                FAILED_TESTS=$((FAILED_TESTS + 1))
                TEST_DETAILS+=("FAIL|${cluster}|daemon|Health check failed")
            fi
        done
    done
    
    echo ""
    log_info "Daemon health tests completed: ${passed}/${test_count} passed"
}

# Test SOCKS5 proxy connectivity
test_socks5_proxy() {
    log_section "Testing SOCKS5 Proxy via Mix Network"
    
    local test_count=0
    local passed=0
    
    for i in "${!CLUSTERS[@]}"; do
        local src_cluster="${CLUSTERS[$i]}"
        
        kubectl config use-context "kind-${src_cluster}" > /dev/null
        
        # Get nyx-proxy service NodePort
        local proxy_nodeport=$(kubectl get svc nyx-proxy -n "${TEST_NAMESPACE}" -o jsonpath='{.spec.ports[?(@.name=="socks5")].nodePort}')
        
        # Get control plane IP
        local proxy_ip=$(docker inspect -f '{{range.NetworkSettings.Networks}}{{.IPAddress}}{{end}}' "${src_cluster}-control-plane")
        
        test_count=$((test_count + 1))
        TOTAL_TESTS=$((TOTAL_TESTS + 1))
        
        log_info "Testing SOCKS5 proxy: ${src_cluster} (${proxy_ip}:${proxy_nodeport})"
        
        # Test with curl through SOCKS5
        if kubectl exec -n "${TEST_NAMESPACE}" test-client -- \
            curl -x "socks5://${proxy_ip}:${proxy_nodeport}" \
            --connect-timeout 10 \
            -s -o /dev/null -w "%{http_code}" \
            "https://www.cloudflare.com" | grep -q "200"; then
            
            log_success "SOCKS5 proxy working: ${src_cluster}"
            passed=$((passed + 1))
            PASSED_TESTS=$((PASSED_TESTS + 1))
            TEST_DETAILS+=("PASS|${src_cluster}|socks5|HTTPS via Mix Network")
        else
            log_error "SOCKS5 proxy failed: ${src_cluster}"
            FAILED_TESTS=$((FAILED_TESTS + 1))
            TEST_DETAILS+=("FAIL|${src_cluster}|socks5|Connection failed")
        fi
    done
    
    echo ""
    log_info "SOCKS5 proxy tests completed: ${passed}/${test_count} passed"
}

# Test Mix Network routing between clusters
test_mix_network_routing() {
    log_section "Testing Inter-Cluster Mix Network Routing"
    
    local test_count=0
    local passed=0
    
    for i in "${!CLUSTERS[@]}"; do
        local src_cluster="${CLUSTERS[$i]}"
        
        kubectl config use-context "kind-${src_cluster}" > /dev/null
        
        for j in "${!CLUSTERS[@]}"; do
            if [ $i -eq $j ]; then
                continue
            fi
            
            local dst_cluster="${CLUSTERS[$j]}"
            
            test_count=$((test_count + 1))
            TOTAL_TESTS=$((TOTAL_TESTS + 1))
            
            log_info "Testing Mix routing: ${src_cluster} → ${dst_cluster}"
            
            # Get destination proxy IP
            local dst_ip=$(docker inspect -f '{{range.NetworkSettings.Networks}}{{.IPAddress}}{{end}}' "${dst_cluster}-control-plane")
            
            # Test HTTP request through Mix Network
            local response_time=$(kubectl exec -n "${TEST_NAMESPACE}" test-client -- \
                sh -c "time curl -x socks5://nyx-proxy:9050 --connect-timeout 10 -s -o /dev/null http://${dst_ip}:8080/health 2>&1" | \
                grep real | awk '{print $2}' || echo "timeout")
            
            if [ "$response_time" != "timeout" ]; then
                log_success "Mix routing OK: ${src_cluster} → ${dst_cluster} (${response_time})"
                passed=$((passed + 1))
                PASSED_TESTS=$((PASSED_TESTS + 1))
                TEST_DETAILS+=("PASS|${src_cluster}|${dst_cluster}|Mix routing ${response_time}")
            else
                log_error "Mix routing failed: ${src_cluster} → ${dst_cluster}"
                FAILED_TESTS=$((FAILED_TESTS + 1))
                TEST_DETAILS+=("FAIL|${src_cluster}|${dst_cluster}|Timeout")
            fi
        done
    done
    
    echo ""
    log_info "Mix Network routing tests completed: ${passed}/${test_count} passed"
}

# Test encryption and anonymization
test_anonymization() {
    log_section "Testing Anonymization & Encryption"
    
    local test_count=0
    local passed=0
    
    for cluster in "${CLUSTERS[@]}"; do
        kubectl config use-context "kind-${cluster}" > /dev/null
        
        test_count=$((test_count + 1))
        TOTAL_TESTS=$((TOTAL_TESTS + 1))
        
        log_info "Checking Mix Network metrics: ${cluster}"
        
        # Get daemon pod
        local daemon_pod=$(kubectl get pods -n "${TEST_NAMESPACE}" -l app=nyx-daemon -o jsonpath='{.items[0].metadata.name}')
        
        # Check Prometheus metrics for Mix Network activity
        local metrics=$(kubectl exec -n "${TEST_NAMESPACE}" "${daemon_pod}" -- \
            curl -s http://localhost:9090/metrics 2>/dev/null || echo "")
        
        if echo "$metrics" | grep -q "nyx_mix_packets_sent"; then
            local packets_sent=$(echo "$metrics" | grep "nyx_mix_packets_sent" | awk '{print $2}' || echo "0")
            log_success "Mix Network active: ${cluster} (${packets_sent} packets sent)"
            passed=$((passed + 1))
            PASSED_TESTS=$((PASSED_TESTS + 1))
            TEST_DETAILS+=("PASS|${cluster}|anonymization|Mix packets: ${packets_sent}")
        else
            log_warning "No Mix Network metrics: ${cluster}"
            FAILED_TESTS=$((FAILED_TESTS + 1))
            TEST_DETAILS+=("FAIL|${cluster}|anonymization|No metrics")
        fi
    done
    
    echo ""
    log_info "Anonymization tests completed: ${passed}/${test_count} passed"
}

# Test Cover Traffic
test_cover_traffic() {
    log_section "Testing Cover Traffic Generation"
    
    local test_count=0
    local passed=0
    
    for cluster in "${CLUSTERS[@]}"; do
        kubectl config use-context "kind-${cluster}" > /dev/null
        
        test_count=$((test_count + 1))
        TOTAL_TESTS=$((TOTAL_TESTS + 1))
        
        log_info "Checking cover traffic: ${cluster}"
        
        local daemon_pod=$(kubectl get pods -n "${TEST_NAMESPACE}" -l app=nyx-daemon -o jsonpath='{.items[0].metadata.name}')
        
        # Check for cover traffic in metrics
        local cover_packets=$(kubectl exec -n "${TEST_NAMESPACE}" "${daemon_pod}" -- \
            curl -s http://localhost:9090/metrics 2>/dev/null | \
            grep "nyx_cover_traffic_packets" | awk '{print $2}' || echo "0")
        
        if [ "${cover_packets%.*}" -gt 0 ]; then
            log_success "Cover traffic active: ${cluster} (${cover_packets} packets)"
            passed=$((passed + 1))
            PASSED_TESTS=$((PASSED_TESTS + 1))
            TEST_DETAILS+=("PASS|${cluster}|cover-traffic|${cover_packets} packets")
        else
            log_warning "No cover traffic detected: ${cluster}"
            FAILED_TESTS=$((FAILED_TESTS + 1))
            TEST_DETAILS+=("FAIL|${cluster}|cover-traffic|No activity")
        fi
    done
    
    echo ""
    log_info "Cover traffic tests completed: ${passed}/${test_count} passed"
}

# Generate test report
generate_report() {
    log_section "Generating Test Report"
    
    local end_time=$(date +%s)
    local duration=$((end_time - START_TIME))
    local success_rate=0
    
    if [ $TOTAL_TESTS -gt 0 ]; then
        success_rate=$((PASSED_TESTS * 100 / TOTAL_TESTS))
    fi
    
    mkdir -p "${TEST_RESULTS_DIR}"
    
    local timestamp=$(date +"%Y%m%d-%H%M%S")
    local json_file="${TEST_RESULTS_DIR}/nyx-test-results-${timestamp}.json"
    local html_file="${TEST_RESULTS_DIR}/nyx-test-results-${timestamp}.html"
    
    # Generate JSON report
    cat > "${json_file}" << EOF
{
  "timestamp": "$(date -Iseconds)",
  "duration_seconds": ${duration},
  "summary": {
    "total": ${TOTAL_TESTS},
    "passed": ${PASSED_TESTS},
    "failed": ${FAILED_TESTS},
    "success_rate": ${success_rate}
  },
  "test_details": [
EOF
    
    local first=true
    for detail in "${TEST_DETAILS[@]}"; do
        IFS='|' read -r status cluster target description <<< "$detail"
        
        if [ "$first" = true ]; then
            first=false
        else
            echo "," >> "${json_file}"
        fi
        
        cat >> "${json_file}" << EOF
    {
      "status": "${status}",
      "cluster": "${cluster}",
      "target": "${target}",
      "description": "${description}"
    }
EOF
    done
    
    cat >> "${json_file}" << EOF

  ]
}
EOF
    
    # Generate HTML report
    cat > "${html_file}" << 'EOF'
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>NyxNet Test Results</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; background: #f5f5f5; }
        .container { max-width: 1200px; margin: 0 auto; background: white; padding: 20px; border-radius: 8px; box-shadow: 0 2px 4px rgba(0,0,0,0.1); }
        h1 { color: #333; border-bottom: 2px solid #4CAF50; padding-bottom: 10px; }
        .summary { display: grid; grid-template-columns: repeat(4, 1fr); gap: 20px; margin: 20px 0; }
        .card { background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); color: white; padding: 20px; border-radius: 8px; text-align: center; }
        .card h3 { margin: 0; font-size: 24px; }
        .card p { margin: 10px 0 0; font-size: 14px; opacity: 0.9; }
        table { width: 100%; border-collapse: collapse; margin: 20px 0; }
        th, td { padding: 12px; text-align: left; border-bottom: 1px solid #ddd; }
        th { background: #4CAF50; color: white; }
        tr:hover { background: #f5f5f5; }
        .pass { color: #4CAF50; font-weight: bold; }
        .fail { color: #f44336; font-weight: bold; }
        .footer { margin-top: 30px; text-align: center; color: #666; font-size: 12px; }
    </style>
</head>
<body>
    <div class="container">
        <h1>🔐 NyxNet Mix Network Test Results</h1>
EOF
    
    cat >> "${html_file}" << EOF
        <div class="summary">
            <div class="card"><h3>${TOTAL_TESTS}</h3><p>Total Tests</p></div>
            <div class="card"><h3>${PASSED_TESTS}</h3><p>Passed</p></div>
            <div class="card"><h3>${FAILED_TESTS}</h3><p>Failed</p></div>
            <div class="card"><h3>${duration}s</h3><p>Duration</p></div>
        </div>
        <table>
            <tr>
                <th>Status</th>
                <th>Cluster</th>
                <th>Target</th>
                <th>Description</th>
            </tr>
EOF
    
    for detail in "${TEST_DETAILS[@]}"; do
        IFS='|' read -r status cluster target description <<< "$detail"
        local status_class="pass"
        [ "$status" = "FAIL" ] && status_class="fail"
        
        cat >> "${html_file}" << EOF
            <tr>
                <td class="${status_class}">${status}</td>
                <td>${cluster}</td>
                <td>${target}</td>
                <td>${description}</td>
            </tr>
EOF
    done
    
    cat >> "${html_file}" << EOF
        </table>
        <div class="footer">
            <p>Generated: $(date)</p>
            <p>NyxNet - Privacy-first, Post-Quantum Secure Network Stack</p>
        </div>
    </div>
</body>
</html>
EOF
    
    log_success "Reports generated:"
    log_info "  JSON: ${json_file}"
    log_info "  HTML: ${html_file}"
}

# Main execution
main() {
    log_section "NyxNet Multi-Cluster Mix Network Test"
    
    # Create clusters first
    create_clusters
    
    # Build image
    build_nyxnet_image
    
    # Load image
    load_image_to_clusters
    
    # Deploy NyxNet
    deploy_nyxnet
    
    # Run tests
    test_daemon_health
    test_socks5_proxy
    test_mix_network_routing
    test_anonymization
    test_cover_traffic
    
    # Generate report
    generate_report
    
    # Summary
    log_section "Test Summary"
    log_info "Total tests: ${TOTAL_TESTS}"
    log_info "Passed: ${PASSED_TESTS}"
    log_info "Failed: ${FAILED_TESTS}"
    
    if [ $FAILED_TESTS -eq 0 ]; then
        log_success "All tests passed! 🎉"
        return 0
    else
        log_warning "Some tests failed"
        return 1
    fi
}

# Run main
main "$@"
