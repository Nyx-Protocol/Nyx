#!/bin/bash
# Kubernetes inter-cluster communication and throughput testing
# Focuses on network performance without SOCKS5 proxy dependency

set -e

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Logging functions
log_info() {
    echo -e "${BLUE}ℹ️  [INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}✅  [SUCCESS]${NC} $1"
}

log_error() {
    echo -e "${RED}❌  [ERROR]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}⚠️  [WARNING]${NC} $1"
}

log_section() {
    echo ""
    echo -e "${BLUE}▶ 🚀 $1${NC}"
    date '+%Y-%m-%d %H:%M:%S'
}

# Test namespace
TEST_NAMESPACE="nyx-test"

# Clusters to test
CLUSTER_COUNT=${CLUSTER_COUNT:-3}
CLUSTERS=()
for i in $(seq 1 ${CLUSTER_COUNT}); do
    CLUSTERS+=("nyx-cluster-$i")
done

# Test counters
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

# Test inter-cluster network connectivity
test_network_connectivity() {
    log_section "Testing Inter-Cluster Network Connectivity"
    
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
            
            log_info "Testing: ${src_cluster} → ${dst_cluster}"
            
            # Get destination control plane IP
            local dst_ip=$(docker exec "${dst_cluster}-control-plane" hostname -i | awk '{print $1}')
            
            # Test connectivity using ping from test-client pod
            local ping_result=$(kubectl exec -n "${TEST_NAMESPACE}" test-client -- \
                ping -c 3 -W 2 "${dst_ip}" 2>&1)
            
            if echo "${ping_result}" | grep -q "3 received"; then
                log_success "Connectivity OK: ${src_cluster} → ${dst_cluster} (${dst_ip})"
                passed=$((passed + 1))
                PASSED_TESTS=$((PASSED_TESTS + 1))
            else
                log_error "Connectivity failed: ${src_cluster} → ${dst_cluster}"
                FAILED_TESTS=$((FAILED_TESTS + 1))
            fi
        done
    done
    
    echo ""
    log_info "Network connectivity tests: ${passed}/${test_count} passed"
}

# Test NyxNet daemon-to-daemon communication
test_daemon_communication() {
    log_section "Testing NyxNet Daemon-to-Daemon Communication"
    
    local test_count=0
    local passed=0
    
    for cluster in "${CLUSTERS[@]}"; do
        kubectl config use-context "kind-${cluster}" > /dev/null
        
        test_count=$((test_count + 1))
        TOTAL_TESTS=$((TOTAL_TESTS + 1))
        
        log_info "Testing daemon communication in: ${cluster}"
        
        # Get daemon pods
        local daemon_pods=$(kubectl get pods -n "${TEST_NAMESPACE}" -l app=nyx-daemon \
            -o jsonpath='{.items[*].metadata.name}')
        
        if [ -z "${daemon_pods}" ]; then
            log_error "No daemon pods found in ${cluster}"
            FAILED_TESTS=$((FAILED_TESTS + 1))
            continue
        fi
        
        local pod_count=$(echo "${daemon_pods}" | wc -w)
        log_info "Found ${pod_count} daemon pods in ${cluster}"
        
        # Check if daemons can see each other's metrics
        local first_pod=$(echo "${daemon_pods}" | awk '{print $1}')
        local metrics=$(kubectl exec -n "${TEST_NAMESPACE}" "${first_pod}" -- \
            curl -s http://localhost:9090/metrics 2>&1 | grep "nyx_" | wc -l)
        
        if [ "${metrics}" -gt 0 ]; then
            log_success "Daemon communication OK in ${cluster} (${metrics} metrics)"
            passed=$((passed + 1))
            PASSED_TESTS=$((PASSED_TESTS + 1))
        else
            log_warning "No metrics found in ${cluster}"
            FAILED_TESTS=$((FAILED_TESTS + 1))
        fi
    done
    
    echo ""
    log_info "Daemon communication tests: ${passed}/${test_count} passed"
}

# Test network throughput using iperf3
test_network_throughput() {
    log_section "Testing Network Throughput (iperf3)"
    
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
            
            log_info "Throughput test: ${src_cluster} → ${dst_cluster}"
            
            # Switch to destination cluster and start iperf3 server
            kubectl config use-context "kind-${dst_cluster}" > /dev/null
            
            # Start iperf3 server in background in destination test-client
            kubectl exec -n "${TEST_NAMESPACE}" test-client -- \
                bash -c "pkill iperf3 2>/dev/null; iperf3 -s -D" 2>&1 > /dev/null
            
            sleep 2
            
            # Get destination test-client IP
            local dst_ip=$(kubectl get pod -n "${TEST_NAMESPACE}" test-client \
                -o jsonpath='{.status.podIP}')
            
            # Switch back to source cluster
            kubectl config use-context "kind-${src_cluster}" > /dev/null
            
            # Run iperf3 client test (10 second test)
            log_info "Running iperf3 from ${src_cluster} to ${dst_cluster} (${dst_ip})..."
            local iperf_output=$(kubectl exec -n "${TEST_NAMESPACE}" test-client -- \
                iperf3 -c "${dst_ip}" -t 10 -J 2>&1)
            
            # Parse throughput from JSON output
            local throughput=$(echo "${iperf_output}" | grep -o '"bits_per_second":[0-9.]*' | \
                head -1 | cut -d: -f2)
            
            if [ -n "${throughput}" ] && [ "${throughput}" != "0" ]; then
                # Convert to Mbps
                local mbps=$(echo "scale=2; ${throughput} / 1000000" | bc)
                log_success "Throughput: ${src_cluster} → ${dst_cluster} = ${mbps} Mbps"
                passed=$((passed + 1))
                PASSED_TESTS=$((PASSED_TESTS + 1))
            else
                log_error "Throughput test failed: ${src_cluster} → ${dst_cluster}"
                FAILED_TESTS=$((FAILED_TESTS + 1))
            fi
            
            # Cleanup iperf3 server
            kubectl config use-context "kind-${dst_cluster}" > /dev/null
            kubectl exec -n "${TEST_NAMESPACE}" test-client -- \
                pkill iperf3 2>/dev/null || true
        done
    done
    
    echo ""
    log_info "Throughput tests: ${passed}/${test_count} passed"
}

# Test latency between clusters
test_network_latency() {
    log_section "Testing Network Latency"
    
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
            
            log_info "Latency test: ${src_cluster} → ${dst_cluster}"
            
            # Get destination nyx-daemon service IP
            kubectl config use-context "kind-${dst_cluster}" > /dev/null
            local dst_ip=$(kubectl get svc -n "${TEST_NAMESPACE}" nyx-daemon \
                -o jsonpath='{.spec.clusterIP}')
            
            # Switch back to source
            kubectl config use-context "kind-${src_cluster}" > /dev/null
            
            # Ping test
            local ping_output=$(kubectl exec -n "${TEST_NAMESPACE}" test-client -- \
                ping -c 10 -W 2 "${dst_ip}" 2>&1)
            
            if echo "${ping_output}" | grep -q "min/avg/max"; then
                local avg_latency=$(echo "${ping_output}" | grep "min/avg/max" | \
                    cut -d'=' -f2 | cut -d'/' -f2)
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
    log_info "Latency tests: ${passed}/${test_count} passed"
}

# Generate test report
generate_report() {
    log_section "Test Summary"
    
    local success_rate=0
    if [ ${TOTAL_TESTS} -gt 0 ]; then
        success_rate=$((PASSED_TESTS * 100 / TOTAL_TESTS))
    fi
    
    log_info "Total tests: ${TOTAL_TESTS}"
    log_info "Passed: ${PASSED_TESTS}"
    log_info "Failed: ${FAILED_TESTS}"
    log_info "Success rate: ${success_rate}%"
    
    if [ ${FAILED_TESTS} -eq 0 ]; then
        log_success "All tests passed! 🎉"
        return 0
    else
        log_warning "Some tests failed"
        return 1
    fi
}

# Main execution
main() {
    log_section "NyxNet Kubernetes Network Performance Tests"
    
    # Run tests
    test_network_connectivity
    test_daemon_communication
    test_network_throughput
    test_network_latency
    
    # Generate report
    generate_report
}

main "$@"
