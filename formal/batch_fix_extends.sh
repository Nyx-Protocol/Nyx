#!/bin/bash
# Batch fix EXTENDS/INSTANCE order for specific modules

cd "$(dirname "$0")"

echo "Fixing EXTENDS/INSTANCE order for specific modules..."

# List of modules that need LOCAL INSTANCE moved after EXTENDS
modules=(
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

for module in "${modules[@]}"; do
    file="${module}.tla"
    
    if [ ! -f "$file" ]; then
        echo "  Skipping $file (not found)"
        continue
    fi
    
    echo "  Processing $file..."
    
    # Check if file has the wrong order
    if grep -q "^LOCAL INSTANCE NyxHelpers" "$file"; then
        # Create temporary file with corrected order
        awk '
        BEGIN {
            in_module_header = 0
            module_line = ""
            comment_block = ""
            extends_line = ""
            instance_line = ""
            rest_started = 0
        }
        
        # Save module declaration
        /^----.*MODULE.*----$/ {
            module_line = $0
            in_module_header = 1
            next
        }
        
        # Collect comment block after module declaration
        in_module_header == 1 && /^\(\*/ {
            comment_block = comment_block $0 "\n"
            next
        }
        
        in_module_header == 1 && /^ \*/ {
            comment_block = comment_block $0 "\n"
            next
        }
        
        in_module_header == 1 && /^\*\)/ {
            comment_block = comment_block $0 "\n"
            in_module_header = 2
            next
        }
        
        # Collect EXTENDS line
        /^EXTENDS/ {
            extends_line = $0
            next
        }
        
        # Collect INSTANCE line
        /^LOCAL INSTANCE/ {
            instance_line = $0
            next
        }
        
        # First real line after headers - output everything in correct order
        !rest_started && module_line != "" && comment_block != "" && (extends_line != "" || instance_line != "") && NF > 0 && !/^EXTENDS/ && !/^LOCAL INSTANCE/ {
            rest_started = 1
            
            # Output in correct order
            print module_line
            printf "%s", comment_block
            print ""
            if (extends_line != "") print extends_line
            if (instance_line != "") print instance_line
            print ""
            print $0
            next
        }
        
        # Output remaining lines
        rest_started {
            print $0
        }
        ' "$file" > "${file}.tmp"
        
        # Check if temp file is valid and not empty
        if [ -s "${file}.tmp" ] && [ $(wc -l < "${file}.tmp") -gt 10 ]; then
            mv "${file}.tmp" "$file"
            echo "    ✓ Fixed $file"
        else
            rm -f "${file}.tmp"
            echo "    ✗ Failed to fix $file (keeping original)"
        fi
    else
        echo "    - $file already correct or no LOCAL INSTANCE"
    fi
done

echo ""
echo "Done!"
