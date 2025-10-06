#!/bin/bash

# 全TLA+モジュールをモデルチェック

echo "TLA+ 全モジュール モデルチェック"
echo "=============================="
echo ""

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
SKIPPED=0

for module in "${MODULES[@]}"; do
    # .cfg ファイルの存在を確認
    if [ ! -f "${module}.cfg" ]; then
        echo "${module}: ⚠️  SKIPPED (No .cfg file)"
        ((SKIPPED++))
        continue
    fi
    
    echo "検証中: ${module}..."
    
    # TLC モデルチェッカーを実行
    timeout 300 java -XX:+UseParallelGC -Xmx4g -cp tla2tools.jar tlc2.TLC -workers auto -cleanup "${module}.tla" > "${module}_verify.log" 2>&1
    
    # 結果を確認
    if grep -q "Model checking completed. No error has been found." "${module}_verify.log"; then
        echo "${module}: ✅ SUCCESS"
        ((SUCCESS++))
    elif grep -q "TLC threw an unexpected exception" "${module}_verify.log"; then
        echo "${module}: ❌ RUNTIME ERROR"
        ((FAILED++))
    elif grep -q "TLC Bug" "${module}_verify.log"; then
        echo "${module}: ❌ TLC BUG"
        ((FAILED++))
    elif grep -q "timeout" "${module}_verify.log"; then
        echo "${module}: ⏱️  TIMEOUT (5分超過)"
        ((FAILED++))
    else
        echo "${module}: ❌ FAILED"
        ((FAILED++))
    fi
    echo ""
done

echo ""
echo "=============================="
echo "成功: ${SUCCESS}  失敗: ${FAILED}  スキップ: ${SKIPPED}"
echo ""

if [ ${FAILED} -eq 0 ] && [ ${SKIPPED} -eq 0 ] && [ ${SUCCESS} -gt 0 ]; then
    echo "🎉 すべてモデルチェック成功!"
    exit 0
elif [ ${FAILED} -eq 0 ] && [ ${SUCCESS} -gt 0 ]; then
    echo "✅ すべて成功 (一部スキップ)"
    exit 0
else
    echo "⚠️  一部失敗またはエラーあり"
    exit 1
fi
