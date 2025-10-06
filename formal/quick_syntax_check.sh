#!/bin/bash
# 簡易TLA+構文チェックスクリプト

cd "$(dirname "$0")"

echo "TLA+ 構文チェック"
echo "=================="

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

mkdir -p syntax_logs

for module in "${MODULES[@]}"; do
    if [ -f "${module}.tla" ]; then
        echo "チェック中: $module"
        java -cp tla2tools.jar tla2sany.SANY "${module}.tla" > "syntax_logs/${module}_syntax.log" 2>&1
        
        if grep -q "Semantic processing of module $module" "syntax_logs/${module}_syntax.log"; then
            echo "  ✅ 構文OK"
        else
            echo "  ❌ 構文エラー"
            grep -i "error" "syntax_logs/${module}_syntax.log" | head -3
        fi
    fi
done

echo ""
echo "詳細ログ: syntax_logs/"
