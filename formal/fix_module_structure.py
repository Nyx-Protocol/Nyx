#!/usr/bin/env python3
"""
Fix TLA+ module structure: ensure EXTENDS comes before LOCAL INSTANCE
"""

import re
import sys
from pathlib import Path

def fix_module_structure(filepath):
    """Fix a single TLA+ module"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    lines = content.split('\n')
    
    # Find key line indices
    module_line_idx = None
    extends_line_idx = None
    instance_line_idx = None
    first_other_idx = None
    
    in_comment_block = False
    
    for i, line in enumerate(lines):
        # Track comment blocks
        if line.strip().startswith('(*'):
            in_comment_block = True
        if line.strip().endswith('*)'):
            in_comment_block = False
            continue
        
        if in_comment_block:
            continue
            
        # Find module declaration
        if re.match(r'^----.*MODULE.*----', line):
            module_line_idx = i
            continue
        
        # Skip if still in header
        if module_line_idx is None:
            continue
        
        # Find EXTENDS
        if line.startswith('EXTENDS'):
            if extends_line_idx is None:
                extends_line_idx = i
            continue
        
        # Find LOCAL INSTANCE
        if line.startswith('LOCAL INSTANCE'):
            if instance_line_idx is None:
                instance_line_idx = i
            continue
        
        # Find first non-comment, non-blank line after module
        if (module_line_idx is not None and 
            first_other_idx is None and 
            line.strip() and 
            not line.strip().startswith('(*') and
            not line.strip().startswith('*)')):
            first_other_idx = i
    
    # If INSTANCE comes before EXTENDS, fix it
    if (extends_line_idx is not None and 
        instance_line_idx is not None and 
        instance_line_idx < extends_line_idx):
        
        print(f"  Fixing {filepath.name}: moving EXTENDS before INSTANCE")
        
        extends_line = lines[extends_line_idx]
        instance_line = lines[instance_line_idx]
        
        # Remove both lines
        new_lines = []
        for i, line in enumerate(lines):
            if i == extends_line_idx or i == instance_line_idx:
                continue
            new_lines.append(line)
        
        # Find where to insert (after module declaration and comments)
        insert_idx = module_line_idx + 1
        
        # Skip comment block
        while insert_idx < len(new_lines) and (
            new_lines[insert_idx].strip().startswith('(*') or
            new_lines[insert_idx].strip().startswith('*') or
            new_lines[insert_idx].strip().endswith('*)')):
            insert_idx += 1
        
        # Insert EXTENDS first, then INSTANCE
        new_lines.insert(insert_idx, extends_line)
        new_lines.insert(insert_idx + 1, instance_line)
        
        # Write back
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write('\n'.join(new_lines))
        
        return True
    
    return False

def main():
    formal_dir = Path(__file__).parent
    
    print("=" * 60)
    print("Fixing TLA+ Module Structure")
    print("=" * 60)
    print()
    
    fixed_count = 0
    
    for tla_file in sorted(formal_dir.glob('Nyx*.tla')):
        if tla_file.name == 'NyxHelpers.tla':
            continue
        
        if fix_module_structure(tla_file):
            fixed_count += 1
    
    print()
    print("=" * 60)
    print(f"Fixed {fixed_count} modules")
    print("=" * 60)

if __name__ == '__main__':
    main()
