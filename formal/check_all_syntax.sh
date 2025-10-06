#!/bin/bash
# Check syntax of all TLA+ modules

cd "$(dirname "$0")"

echo "======================================"
echo "TLA+ Syntax Check for All Modules"
echo "======================================"
echo ""

success=0
fail=0

for f in Nyx*.tla; do
    echo "Checking $f..."
    if java -cp tla2tools.jar tla2sany.SANY "$f" 2>&1 | grep -q "^*** Errors:"; then
        echo "  ❌ FAILED"
        java -cp tla2tools.jar tla2sany.SANY "$f" 2>&1 | grep -A10 "^*** Errors:"
        ((fail++))
    else
        echo "  ✅ OK"
        ((success++))
    fi
    echo ""
done

echo "======================================"
echo "Success: $success  Failed: $fail"
echo "======================================"

exit $fail
