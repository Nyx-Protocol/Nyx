#!/usr/bin/env python3
"""
Comprehensive TLA+ module fixer
Fixes common issues:
1. EXTENDS/LOCAL INSTANCE order
2. Broken EXTENDS lines with trailing commas
3. Module references after EXTENDS
"""

import re
from pathlib import Path

def fix_module(filepath):
    """Fix a single TLA+ module"""
    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except Exception as e:
        print(f"  ✗ Error reading {filepath.name}: {e}")
        return False
    
    original = content
    lines = content.split('\n')
    
    # Find module declaration
    module_idx = None
    for i, line in enumerate(lines):
        if re.match(r'^----.*MODULE.*----', line):
            module_idx = i
            break
    
    if module_idx is None:
        return False
    
    # Find end of comment block
    comment_end = module_idx + 1
    in_comment = False
    for i in range(module_idx + 1, len(lines)):
        line = lines[i].strip()
        if line.startswith('(*'):
            in_comment = True
        if in_comment and line.endswith('*)'):
            comment_end = i + 1
            break
    
    # Find EXTENDS and LOCAL INSTANCE lines
    extends_idx = None
    instance_idx = None
    
    for i in range(comment_end, min(comment_end + 10, len(lines))):
        line = lines[i]
        if line.startswith('EXTENDS'):
            extends_idx = i
        elif line.startswith('LOCAL INSTANCE'):
            instance_idx = i
    
    if extends_idx is None and instance_idx is None:
        return False
    
    # Extract EXTENDS line (handle multi-line)
    extends_lines = []
    if extends_idx is not None:
        i = extends_idx
        while i < len(lines):
            extends_lines.append(lines[i])
            # Check if line ends with comma (continuation)
            if not lines[i].rstrip().endswith(','):
                break
            i += 1
            # Stop if we hit something that's not a module name
            if i < len(lines) and not lines[i].strip():
                break
            if i < len(lines) and (lines[i].startswith('LOCAL') or 
                                   lines[i].startswith('CONSTANTS') or
                                   lines[i].startswith('VARIABLES')):
                break
        
        # Clean up EXTENDS line
        extends_text = ' '.join(extends_lines)
        # Remove trailing comma and any module references
        extends_text = re.sub(r',\s*$', '', extends_text)
        # Remove any module references after main imports
        extends_text = re.sub(r',\s+Nyx\w+.*$', '', extends_text)
        extends_lines = [extends_text]
    
    # Extract INSTANCE line
    instance_line = None
    if instance_idx is not None:
        instance_line = lines[instance_idx]
    
    # Rebuild the file
    new_lines = []
    
    # Add everything up to comment_end
    new_lines.extend(lines[:comment_end])
    new_lines.append('')
    
    # Add EXTENDS first
    if extends_lines:
        new_lines.extend(extends_lines)
    
    # Add INSTANCE second
    if instance_line:
        new_lines.append(instance_line)
    
    # Add remaining lines (skip old EXTENDS/INSTANCE)
    skip_until = max(extends_idx + len(extends_lines) if extends_idx else 0,
                     instance_idx + 1 if instance_idx else 0)
    
    for i in range(comment_end, len(lines)):
        if i < skip_until:
            # Skip old EXTENDS/INSTANCE lines and module references
            if (lines[i].startswith('EXTENDS') or 
                lines[i].startswith('LOCAL INSTANCE') or
                (lines[i].strip() and lines[i].strip().startswith('Nyx') and ',' not in lines[i][:10])):
                continue
        else:
            # Skip empty lines that were part of old structure
            if not lines[i].strip() and i < skip_until + 3:
                continue
            new_lines.append(lines[i])
    
    new_content = '\n'.join(new_lines)
    
    if new_content != original:
        try:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(new_content)
            print(f"  ✓ Fixed {filepath.name}")
            return True
        except Exception as e:
            print(f"  ✗ Error writing {filepath.name}: {e}")
            return False
    
    return False

def main():
    formal_dir = Path(__file__).parent
    
    print("=" * 70)
    print("Comprehensive TLA+ Module Fixer")
    print("=" * 70)
    print()
    
    fixed_count = 0
    skipped_count = 0
    
    for tla_file in sorted(formal_dir.glob('Nyx*.tla')):
        if tla_file.name == 'NyxHelpers.tla':
            continue
        
        if tla_file.name in ['NyxBasicVerification.tla', 'NyxComprehensiveVerification.tla',
                             'NyxNetworkLayer.tla', 'NyxStreamManagement.tla']:
            skipped_count += 1
            continue
        
        if fix_module(tla_file):
            fixed_count += 1
    
    print()
    print("=" * 70)
    print(f"Fixed: {fixed_count}, Skipped (already working): {skipped_count}")
    print("=" * 70)

if __name__ == '__main__':
    main()
