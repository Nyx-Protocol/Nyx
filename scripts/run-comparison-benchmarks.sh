#!/bin/bash
# Comparison benchmarks with Tor and I2P
# This script measures baseline performance of existing anonymity networks

set -e

echo "======================================================"
echo "NyxNet Comparison Benchmarks (Tor & I2P)"
echo "======================================================"
echo ""

# Check dependencies
check_dependencies() {
    echo "Checking dependencies..."
    
    if ! command -v tor &> /dev/null; then
        echo "❌ Tor not found. Install with: sudo apt install tor"
        exit 1
    fi
    
    if ! command -v curl &> /dev/null; then
        echo "❌ curl not found. Install with: sudo apt install curl"
        exit 1
    fi
    
    echo "✅ Dependencies OK"
    echo ""
}

# Start Tor daemon
start_tor() {
    echo "Starting Tor daemon..."
    
    # Create temporary Tor config
    TOR_CONFIG=$(mktemp)
    cat > "$TOR_CONFIG" <<EOF
SocksPort 9050
ControlPort 9051
DataDirectory /tmp/tor_benchmark
Log notice stdout
EOF
    
    # Start Tor in background
    tor -f "$TOR_CONFIG" &
    TOR_PID=$!
    
    echo "Waiting for Tor to establish circuits..."
    sleep 10
    
    echo "✅ Tor started (PID: $TOR_PID)"
    echo ""
}

# Stop Tor daemon
stop_tor() {
    echo "Stopping Tor daemon..."
    if [ ! -z "$TOR_PID" ]; then
        kill $TOR_PID 2>/dev/null || true
    fi
    rm -rf /tmp/tor_benchmark
    echo "✅ Tor stopped"
}

# Benchmark file transfer over Tor
benchmark_tor_file_transfer() {
    echo "=== Tor File Transfer Benchmark ==="
    
    local FILE_URL="http://httpbin.org/bytes/10485760"  # 10 MB
    local ITERATIONS=3
    
    echo "Downloading 10 MB file through Tor ($ITERATIONS iterations)..."
    
    local total_time=0
    for i in $(seq 1 $ITERATIONS); do
        echo "  Iteration $i..."
        local start_time=$(date +%s.%N)
        
        curl --socks5 127.0.0.1:9050 -o /dev/null -s "$FILE_URL"
        
        local end_time=$(date +%s.%N)
        local elapsed=$(echo "$end_time - $start_time" | bc)
        total_time=$(echo "$total_time + $elapsed" | bc)
        
        echo "    Time: ${elapsed}s"
    done
    
    local avg_time=$(echo "scale=2; $total_time / $ITERATIONS" | bc)
    local throughput=$(echo "scale=2; 10 / $avg_time" | bc)
    
    echo "Average time: ${avg_time}s"
    echo "Average throughput: ${throughput} MB/s"
    echo ""
    
    # Save results
    echo "tor_file_transfer_throughput_mbps=$throughput" >> "$RESULTS_FILE"
}

# Benchmark messaging latency over Tor
benchmark_tor_messaging() {
    echo "=== Tor Messaging Latency Benchmark ==="
    
    local TEST_URL="http://httpbin.org/post"
    local MESSAGE_SIZE=1024
    local ITERATIONS=10
    
    echo "Sending $MESSAGE_SIZE byte messages through Tor ($ITERATIONS iterations)..."
    
    local total_time=0
    for i in $(seq 1 $ITERATIONS); do
        local start_time=$(date +%s.%N)
        
        curl --socks5 127.0.0.1:9050 -X POST -d "$(head -c $MESSAGE_SIZE /dev/zero | base64)" \
             -o /dev/null -s "$TEST_URL"
        
        local end_time=$(date +%s.%N)
        local elapsed=$(echo "($end_time - $start_time) * 1000" | bc)
        total_time=$(echo "$total_time + $elapsed" | bc)
    done
    
    local avg_latency=$(echo "scale=0; $total_time / $ITERATIONS" | bc)
    
    echo "Average latency: ${avg_latency}ms"
    echo ""
    
    # Save results
    echo "tor_messaging_latency_ms=$avg_latency" >> "$RESULTS_FILE"
}

# Benchmark direct connection (baseline)
benchmark_direct() {
    echo "=== Direct Connection Baseline ==="
    
    local FILE_URL="http://httpbin.org/bytes/10485760"  # 10 MB
    
    echo "Downloading 10 MB file directly..."
    
    local start_time=$(date +%s.%N)
    curl -o /dev/null -s "$FILE_URL"
    local end_time=$(date +%s.%N)
    
    local elapsed=$(echo "$end_time - $start_time" | bc)
    local throughput=$(echo "scale=2; 10 / $elapsed" | bc)
    
    echo "Time: ${elapsed}s"
    echo "Throughput: ${throughput} MB/s"
    echo ""
    
    # Save results
    echo "direct_file_transfer_throughput_mbps=$throughput" >> "$RESULTS_FILE"
    
    # Messaging latency
    echo "Testing direct messaging latency..."
    local start_time=$(date +%s.%N)
    curl -X POST -d "$(head -c 1024 /dev/zero | base64)" -o /dev/null -s "http://httpbin.org/post"
    local end_time=$(date +%s.%N)
    local latency=$(echo "($end_time - $start_time) * 1000" | bc)
    
    echo "Latency: ${latency}ms"
    echo ""
    
    echo "direct_messaging_latency_ms=$latency" >> "$RESULTS_FILE"
}

# Generate comparison report
generate_report() {
    echo "======================================================"
    echo "Comparison Benchmark Results"
    echo "======================================================"
    echo ""
    
    if [ -f "$RESULTS_FILE" ]; then
        cat "$RESULTS_FILE"
    else
        echo "❌ No results file found"
    fi
    
    echo ""
    echo "✅ Benchmark complete"
    echo "Results saved to: $RESULTS_FILE"
}

# Main execution
main() {
    RESULTS_FILE="benchmarks/results/comparison_results_$(date +%Y%m%d_%H%M%S).txt"
    mkdir -p "benchmarks/results"
    
    # Create results file
    echo "# NyxNet Comparison Benchmark Results" > "$RESULTS_FILE"
    echo "# Generated: $(date)" >> "$RESULTS_FILE"
    echo "" >> "$RESULTS_FILE"
    
    check_dependencies
    
    # Baseline measurements
    benchmark_direct
    
    # Tor measurements
    start_tor
    trap stop_tor EXIT
    
    benchmark_tor_file_transfer
    benchmark_tor_messaging
    
    stop_tor
    trap - EXIT
    
    generate_report
    
    echo ""
    echo "📊 To generate the full performance report with charts:"
    echo "    python scripts/generate-performance-report.py"
}

main "$@"
