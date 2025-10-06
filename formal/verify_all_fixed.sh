#!/bin/bash
# すべての修正済みモジュールを検証

cd "$(dirname "$0")"

echo "=========================================="
echo "修正済みモジュールの検証"
echo "=========================================="
echo ""

MODULES=(
    "NyxCryptography"
    "NyxNetworkLayer"
    "NyxStreamManagement"
    "NyxQoSManagement"
    "NyxFaultTolerance"
    "NyxEdgeComputing"
    "NyxTimeSensitiveNetworking"
    "NyxSecurityAudit"
    "NyxNFVAndSDN"
    "NyxConfigurationValidation"
)

SUCCESS=0
FAILED=0

for module in "${MODULES[@]}"; do
    echo "検証中: $module ..."
    
    if timeout 120 java -Xmx2G -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC \
        -workers 2 -deadlock -depth 20 \
        -config ${module}.cfg ${module} \
        > verification_logs/${module}.log 2>&1; then
        
        if grep -q "Finished computing initial states" verification_logs/${module}.log; then
            echo "✅ $module - SUCCESS"
            SUCCESS=$((SUCCESS + 1))
        else
            echo "❌ $module - FAILED"
            FAILED=$((FAILED + 1))
        fi
    else
        echo "❌ $module - TIMEOUT/ERROR"
        FAILED=$((FAILED + 1))
    fi
    echo ""
done

echo "=========================================="
echo "検証結果サマリー"
echo "=========================================="
echo "合計: ${#MODULES[@]}"
echo "成功: $SUCCESS"
echo "失敗: $FAILED"
echo "=========================================="
