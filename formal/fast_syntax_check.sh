#!/bin/bash
# 高速構文チェック(タイムアウト付き)

cd "$(dirname "$0")"

echo "TLA+ 簡易構文チェック"
echo "===================="

MODULES=(
    "NyxBasicVerification"
    "NyxCryptography"
    "NyxNetworkLayer"
    "NyxFaultTolerance"
    "NyxQoSManagement"
    "NyxDistributedConsensus"
    "NyxEdgeComputing"
    "NyxTimeSensitiveNetworking"
    "NyxSecurityAudit"
    "NyxNFVAndSDN"
    "NyxConfigurationValidation"
)

SUCCESS=0
FAILED=0

for module in "${MODULES[@]}"; do
    if [ -f "${module}.tla" ]; then
        printf "%-35s " "$module:"
        
        # 30秒のタイムアウトで構文チェック
        timeout 30 java -cp tla2tools.jar tla2sany.SANY "${module}.tla" > /tmp/${module}_syntax.log 2>&1
        
        if grep -q "Semantic processing of module $module" /tmp/${module}_syntax.log 2>/dev/null; then
            echo "✅ OK"
            SUCCESS=$((SUCCESS + 1))
        else
            echo "❌ FAIL"
            FAILED=$((FAILED + 1))
            grep -i "error\|parse" /tmp/${module}_syntax.log | head -2
        fi
    fi
done

echo ""
echo "成功: $SUCCESS  失敗: $FAILED"
