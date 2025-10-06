#!/bin/bash
# Fix EXTENDS/INSTANCE order in all TLA modules

cd "$(dirname "$0")"

echo "Fixing EXTENDS/INSTANCE order in all modules..."

for f in Nyx*.tla; do
    if [ "$f" = "NyxHelpers.tla" ]; then
        continue
    fi
    
    # Check if has both LOCAL INSTANCE NyxHelpers and EXTENDS
    if grep -q "^LOCAL INSTANCE NyxHelpers" "$f" && grep -q "^EXTENDS" "$f"; then
        echo "Fixing $f..."
        
        # Create temp file
        temp_file=$(mktemp)
        
        # Read file line by line
        in_header=true
        extends_line=""
        instance_line=""
        
        while IFS= read -r line; do
            if [[ "$line" =~ ^----.*MODULE.*---- ]]; then
                echo "$line" >> "$temp_file"
                in_header=false
            elif [ "$in_header" = true ]; then
                echo "$line" >> "$temp_file"
            elif [[ "$line" =~ ^EXTENDS ]]; then
                extends_line="$line"
            elif [[ "$line" =~ ^LOCAL\ INSTANCE\ NyxHelpers ]]; then
                instance_line="$line"
            else
                # Output EXTENDS first, then INSTANCE
                if [ -n "$extends_line" ] && [ -z "$extends_printed" ]; then
                    echo "$extends_line" >> "$temp_file"
                    extends_printed=true
                fi
                if [ -n "$instance_line" ] && [ -z "$instance_printed" ]; then
                    echo "$instance_line" >> "$temp_file"
                    instance_printed=true
                fi
                echo "$line" >> "$temp_file"
            fi
        done < "$f"
        
        # Replace original with fixed version
        mv "$temp_file" "$f"
    fi
done

echo "Done!"
