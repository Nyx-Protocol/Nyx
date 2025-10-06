#!/bin/bash
# 迅速な構文チェックのみ

cd "$(dirname "$0")"

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

echo "TLA+ 構文チェックのみ"
echo "===================="
echo ""

for module in "${MODULES[@]}"; do
    if [ -f "${module}.tla" ]; then
        printf "%-35s " "${module}:"
        
        timeout 30 java -cp tla2tools.jar tla2sany.SANY "${module}.tla" > /tmp/${module}_check.log 2>&1
        
        if grep -q "Semantic processing of module ${module}" /tmp/${module}_check.log; then
            echo "✅ OK"
            SUCCESS=$((SUCCESS + 1))
        else
            echo "❌ エラー"
            FAILED=$((FAILED + 1))
            grep -i "error\|parse\|unknown" /tmp/${module}_check.log | head -2
        fi
    fi
done

echo ""
echo "成功: $SUCCESS  失敗: $FAILED"

if [ $FAILED -eq 0 ]; then
    echo ""
    echo "🎉 すべて構文チェック成功!"
    exit 0
else
    exit 1
fi
