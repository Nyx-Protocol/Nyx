#!/bin/bash
# 最終検証スクリプト - すべてのモジュールを実際にモデルチェック

cd "$(dirname "$0")"

echo "==========================================" 
echo "NyxNet TLA+ 最終検証"
echo "==========================================" 
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

TOTAL=${#MODULES[@]}
SUCCESS=0
FAILED=0

mkdir -p verification_logs

for module in "${MODULES[@]}"; do
    echo "----------------------------------------"
    echo "検証中: $module"
    
    # cfgファイルの存在確認
    if [ ! -f "${module}.cfg" ]; then
        echo "⚠️  設定ファイルなし - スキップ"
        continue
    fi
    
    # まず構文チェック
    timeout 30 java -cp tla2tools.jar tla2sany.SANY "${module}.tla" > /tmp/${module}_syntax.log 2>&1
    
    if ! grep -q "Semantic processing of module $module" /tmp/${module}_syntax.log 2>/dev/null; then
        echo "❌ 構文エラー"
        grep -i "error" /tmp/${module}_syntax.log | head -2
        FAILED=$((FAILED + 1))
        continue
    fi
    
    # モデルチェック実行
    timeout 120 java -Xmx2G -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC \
        -workers 2 \
        -deadlock \
        -depth 15 \
        -config "${module}.cfg" \
        "${module}" > "verification_logs/${module}.log" 2>&1
    
    if grep -q "Model checking completed. No error has been found" "verification_logs/${module}.log"; then
        echo "✅ 成功"
        SUCCESS=$((SUCCESS + 1))
    else
        echo "❌ 失敗"
        grep -E "Error:|Invariant|violated" "verification_logs/${module}.log" | head -3
        FAILED=$((FAILED + 1))
    fi
done

echo ""
echo "=========================================="
echo "検証結果サマリー"
echo "=========================================="
echo "成功: $SUCCESS / $TOTAL"
echo "失敗: $FAILED / $TOTAL"
echo ""

if [ $FAILED -eq 0 ]; then
    echo "🎉 すべての検証が成功しました!"
    exit 0
else
    echo "⚠️  いくつかの検証が失敗しました"
    echo "詳細は verification_logs/ を確認してください"
    exit 1
fi
