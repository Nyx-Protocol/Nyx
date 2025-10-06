#!/usr/bin/env python3
"""
TLA+ 構文エラー一括修正スクリプト
演算子の優先順位エラーを自動的に修正します
"""

import re
import sys
from pathlib import Path

def fix_precedence_errors(content):
    """演算子の優先順位エラーを修正"""
    
    # Pattern 1: a * b \div c -> (a * b) \div c
    content = re.sub(r'(\w+(?:\.\w+)*)\s*\*\s*(\w+(?:\.\w+)*)\s*(\\div)', r'(\1 * \2) \3', content)
    
    # Pattern 2: a * b / c -> (a * b) / c  
    content = re.sub(r'(\w+(?:\.\w+)*)\s*\*\s*(\w+(?:\.\w+)*)\s*/', r'(\1 * \2) /', content)
    
    # Pattern 3: a + b * c \div d -> a + (b * c) \div d (より複雑なケース)
    # すでに括弧がある場合はスキップ
    content = re.sub(r'([^(])\s*(\w+)\s*\*\s*(\w+)\s*(\\div|/)\s*(\w+)', 
                     r'\1 (\2 * \3) \4 \5', content)
    
    return content

def fix_set_comprehension(content):
    """集合内包表記のエラーを修正"""
    # {x : x \in S, condition} -> {x \in S : condition}
    # これは手動で確認する必要がある
    return content

def main():
    formal_dir = Path(__file__).parent
    tla_files = list(formal_dir.glob("Nyx*.tla"))
    
    print(f"修正するファイル数: {len(tla_files)}")
    
    for tla_file in tla_files:
        print(f"\n処理中: {tla_file.name}")
        
        try:
            with open(tla_file, 'r', encoding='utf-8') as f:
                original = f.read()
            
            fixed = fix_precedence_errors(original)
            
            if fixed != original:
                # バックアップ作成
                backup_file = tla_file.with_suffix('.tla.bak')
                with open(backup_file, 'w', encoding='utf-8') as f:
                    f.write(original)
                
                # 修正版を書き込み
                with open(tla_file, 'w', encoding='utf-8') as f:
                    f.write(fixed)
                
                print(f"  ✓ 修正完了 (バックアップ: {backup_file.name})")
            else:
                print(f"  - 修正不要")
                
        except Exception as e:
            print(f"  ✗ エラー: {e}")
            continue
    
    print("\n\n修正完了!")
    print("次のコマンドで検証を再実行してください:")
    print("  ./quick_verify.sh")

if __name__ == "__main__":
    main()
