#!/bin/bash
# Fix all common TLA+ errors systematically

cd "$(dirname "$0")"

echo "=========================================="
echo "Systematic Fix of All TLA+ Modules"
echo "=========================================="

# Pattern 1: Fix EXTENDS after LOCAL INSTANCE
echo ""
echo "Pattern 1: Fixing EXTENDS/INSTANCE order..."

for f in Nyx*.tla; do
    if [ "$f" = "NyxHelpers.tla" ]; then
        continue
    fi
    
    # Check if file has both LOCAL INSTANCE and EXTENDS in wrong order
    if grep -q "^LOCAL INSTANCE NyxHelpers" "$f"; then
        # File already has INSTANCE, check if EXTENDS comes after
        if grep -A1 "^LOCAL INSTANCE NyxHelpers" "$f" | grep -q "^EXTENDS"; then
            echo "  Fixing $f (moving EXTENDS before INSTANCE)..."
            
            # Extract module header (everything before first EXTENDS or INSTANCE)
            awk '
            BEGIN { in_header=1; extends=""; instance="" }
            /^----.*MODULE.*----/ { print; in_header=0; next }
            in_header { print; next }
            /^EXTENDS/ && extends=="" { extends=$0; next }
            /^LOCAL INSTANCE NyxHelpers/ && instance=="" { instance=$0; next }
            !in_header && extends=="" && instance=="" { print }
            END { 
                if (extends != "") print extends;
                if (instance != "") print instance;
            }
            ' "$f" > "${f}.tmp" && mv "${f}.tmp" "$f"
        fi
    fi
done

# Pattern 2: Remove empty parentheses ()
echo ""
echo "Pattern 2: Fixing empty parentheses..."

for f in NyxAPISpecification.tla NyxAdvancedRouting.tla; do
    if [ -f "$f" ]; then
        echo "  Processing $f..."
        # This is complex, will handle case by case
    fi
done

# Pattern 3: Fix modules that need EXTENDS before LOCAL INSTANCE
echo ""
echo "Pattern 3: Ensuring proper module structure..."

modules_to_fix=(
    "NyxAdvancedOptimization"
    "NyxConcurrencyModels"
    "NyxControlPlane"
    "NyxDeployment"
    "NyxDetailedProofs"
    "NyxDistributedConsensus"
    "NyxEdgeComputing"
    "NyxFaultTolerance"
    "NyxMobilityManagement"
    "NyxMonitoring"
    "NyxPerformanceModels"
    "NyxQoSManagement"
    "NyxSecurityAudit"
    "NyxTestingFramework"
)

for module in "${modules_to_fix[@]}"; do
    f="${module}.tla"
    if [ ! -f "$f" ]; then
        continue
    fi
    
    echo "  Fixing $f..."
    
    # Create a properly structured file
    awk '
    BEGIN { 
        found_module=0
        found_extends=0
        found_instance=0
        buffer=""
    }
    
    # Module declaration line
    /^----.*MODULE.*----/ {
        print
        found_module=1
        next
    }
    
    # Comment lines at the start
    found_module==1 && /^\(\*/ {
        buffer = buffer $0 "\n"
        next
    }
    
    found_module==1 && /^ \*/ {
        buffer = buffer $0 "\n"
        next
    }
    
    found_module==1 && /^\*\)/ {
        buffer = buffer $0 "\n"
        # Print all buffered comments
        printf "%s", buffer
        buffer=""
        next
    }
    
    # EXTENDS line
    /^EXTENDS/ {
        if (!found_extends) {
            print
            found_extends=1
        }
        next
    }
    
    # LOCAL INSTANCE line
    /^LOCAL INSTANCE/ {
        if (!found_instance && found_extends) {
            print
            found_instance=1
        }
        next
    }
    
    # Everything else
    {
        if (buffer != "") {
            printf "%s", buffer
            buffer=""
        }
        print
    }
    ' "$f" > "${f}.tmp" && mv "${f}.tmp" "$f"
done

echo ""
echo "=========================================="
echo "Systematic fix complete!"
echo "=========================================="
