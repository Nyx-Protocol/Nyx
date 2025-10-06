#!/bin/bash
# すべてのTLA+モジュールにヘルパー演算子を追加

cd "$(dirname "$0")"

echo "ヘルパー演算子の追加"
echo "==================="

# ヘルパー演算子の定義
HELPERS='(****************************************************************************)
(* Common Helper Operators                                                  *)
(****************************************************************************)

\* Minimum of a set
MIN(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \\A y \in S : x <= y

\* Maximum of a set
MAX(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \\A y \in S : x >= y

\* Minimum (lowercase alias)
Min(x, y) == IF x < y THEN x ELSE y

\* Maximum (lowercase alias)
Max(x, y) == IF x > y THEN x ELSE y

\* Absolute value
Abs(x) == IF x < 0 THEN -x ELSE x

\* Sum of set elements
Sum(S) == LET RECURSIVE SumRec(_)
              SumRec(T) == IF T = {} 
                          THEN 0 
                          ELSE LET x == CHOOSE y \in T : TRUE
                               IN x + SumRec(T \\ {x})
          IN SumRec(S)

\* Average
Average(S) == IF S = {} THEN 0 ELSE Sum(S) / Cardinality(S)

'

# 各.tlaファイルを処理
for file in NyxNetworkLayer.tla NyxStreamManagement.tla NyxQoSManagement.tla \
            NyxTimeSensitiveNetworking.tla NyxSecurityProperties.tla \
            NyxPerformanceModels.tla NyxStorageLayer.tla; do
    
    if [ -f "$file" ]; then
        # すでにヘルパーがあるかチェック
        if grep -q "Common Helper Operators" "$file"; then
            echo "⏭️  $file: すでにヘルパーあり"
        else
            echo "追加中: $file"
            
            # EXTENDS行の後にヘルパーを挿入
            awk -v helpers="$HELPERS" '
                /^EXTENDS/ { print; print ""; print helpers; next }
                { print }
            ' "$file" > "${file}.tmp" && mv "${file}.tmp" "$file"
            
            echo "✅ $file: ヘルパー追加完了"
        fi
    fi
done

echo ""
echo "完了!"
