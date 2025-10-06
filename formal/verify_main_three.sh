#!/bin/bash
# 主要な3つのモジュールを検証

cd "$(dirname "$0")"

echo "主要モジュールの検証を開始..."
echo ""

MODULES=("NyxCryptography" "NyxNetworkLayer" "NyxStreamManagement")

for module in "${MODULES[@]}"; do
    echo "検証中: $module"
    
    timeout 120 java -Xmx2G -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC \
        -workers 2 -deadlock -depth 10 \
        -config ${module}.cfg ${module} \
        > verification_logs/${module}.log 2>&1
    
    if grep -q "Finished computing initial states" verification_logs/${module}.log; then
        echo "✅ $module - 成功"
    elif grep -q "Parse Error" verification_logs/${module}.log; then
        echo "❌ $module - 構文エラー"
        grep "Parse Error" verification_logs/${module}.log -A 3
    else
        echo "❌ $module - 失敗"
    fi
    echo ""
done

echo "完了"
