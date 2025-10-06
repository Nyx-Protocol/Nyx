#!/bin/bash
# Fix common TLA+ syntax errors across all modules

cd "$(dirname "$0")"

echo "Fixing common TLA+ errors in all modules..."

# For each TLA file, add EXTENDS NyxHelpers if not present
for f in Nyx*.tla; do
    if [ "$f" = "NyxHelpers.tla" ]; then
        continue
    fi
    
    # Check if already extends NyxHelpers
    if ! grep -q "EXTENDS.*NyxHelpers" "$f"; then
        echo "Processing $f..."
        
        # Find the EXTENDS line and add NyxHelpers
        if grep -q "^EXTENDS " "$f"; then
            # Add NyxHelpers to existing EXTENDS
            sed -i 's/^EXTENDS \(.*\)$/EXTENDS NyxHelpers, \1/' "$f"
        else
            # Add new EXTENDS line after module declaration
            sed -i '/^----.*MODULE.*----$/a EXTENDS NyxHelpers' "$f"
        fi
    fi
done

echo "Done!"
