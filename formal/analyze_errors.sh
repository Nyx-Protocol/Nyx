#!/bin/bash
# Systematically fix all TLA+ modules

cd "$(dirname "$0")"

echo "=========================================="
echo "Complete TLA+ Module Fix Process"
echo "=========================================="

# Step 1: Get list of all failed modules
echo ""
echo "Step 1: Identifying failed modules..."
failed_modules=()

for f in Nyx*.tla; do
    if [ "$f" = "NyxHelpers.tla" ]; then
        continue
    fi
    
    if java -cp tla2tools.jar tla2sany.SANY "$f" 2>&1 | grep -q "^*** Errors:"; then
        failed_modules+=("$f")
    fi
done

echo "Found ${#failed_modules[@]} modules with errors"

# Step 2: Analyze error patterns
echo ""
echo "Step 2: Analyzing error patterns..."

for module in "${failed_modules[@]}"; do
    echo ""
    echo "=== Analyzing $module ==="
    
    # Get error output
    error_output=$(java -cp tla2tools.jar tla2sany.SANY "$module" 2>&1)
    
    # Check for parse errors
    if echo "$error_output" | grep -q "Parse Error"; then
        echo "  Type: PARSE ERROR"
        echo "$error_output" | grep -A3 "Parse Error" | head -5
    elif echo "$error_output" | grep -q "Semantic errors"; then
        echo "  Type: SEMANTIC ERROR"
        error_count=$(echo "$error_output" | grep "*** Errors:" | head -1 | grep -oP '\d+')
        echo "  Error count: $error_count"
        echo "$error_output" | grep "Unknown operator" | head -5
    fi
done

echo ""
echo "=========================================="
echo "Analysis complete. Check output above."
echo "=========================================="
