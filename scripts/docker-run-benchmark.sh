#!/bin/bash
# Run real Criterion benchmarks in Docker environment

set -e

SCENARIO=${1:-"baseline"}

echo "=== Running NyxNet Benchmarks in Docker ==="
echo "Scenario: $SCENARIO"
echo ""

# Apply network delay if not baseline
if [ "$SCENARIO" != "baseline" ]; then
  echo "Applying $SCENARIO network delays..."
  bash scripts/docker-apply-delay.sh $SCENARIO
  sleep 2
fi

# Run benchmarks in the benchmark container
echo ""
echo "Running Criterion benchmarks..."
echo ""

docker exec nyx-benchmark bash -c "
  set -e
  cd /workspace
  
  # Install dependencies if needed
  apt-get update -qq && apt-get install -y -qq iproute2 > /dev/null 2>&1 || true
  
  # Run benchmarks
  cargo bench --package nyx-benchmarks --bench application_scenarios \
    -- --warm-up-time 1 --measurement-time 5 --sample-size 20 \
    2>&1 | tee /workspace/benchmarks/results/${SCENARIO}_bench_output.txt
"

EXIT_CODE=$?

# Clear delays
if [ "$SCENARIO" != "baseline" ]; then
  echo ""
  echo "Clearing network delays..."
  bash scripts/docker-apply-delay.sh none
fi

if [ $EXIT_CODE -eq 0 ]; then
  echo ""
  echo "✅ Benchmarks completed successfully!"
  echo "Results saved to: benchmarks/results/${SCENARIO}_bench_output.txt"
else
  echo ""
  echo "❌ Benchmarks failed with exit code $EXIT_CODE"
  exit $EXIT_CODE
fi
