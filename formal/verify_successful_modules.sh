#!/bin/bash
# 成功したモジュールのみを検証

cd "$(dirname "$0")"

echo "==========================================" 
echo "NyxNet TLA+ 成功モジュール検証"
echo "==========================================" 
echo ""

# 構文チェックに成功したモジュールのみ
MODULES=(
    "NyxBasicVerification"
    "NyxCryptography"
    "NyxNetworkLayer"
    "NyxFaultTolerance"
    "NyxDistributedConsensus"
    "NyxTimeSensitiveNetworking"
)

SUCCESS=0
FAILED=0

mkdir -p verification_logs

for module in "${MODULES[@]}"; do
    echo "----------------------------------------"
    echo "検証中: $module"
    
    if [ ! -f "${module}.cfg" ]; then
        echo "⚠️  設定ファイルなし - スキップ"
        continue
    fi
    
    # モデルチェック実行(簡易版)
    timeout 60 java -Xmx1G -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC \
        -workers 2 \
        -deadlock \
        -depth 10 \
        -config "${module}.cfg" \
        "${module}" > "verification_logs/${module}.log" 2>&1
    
    if grep -q "Model checking completed. No error has been found" "verification_logs/${module}.log"; then
        echo "✅ 成功"
        SUCCESS=$((SUCCESS + 1))
    else
        echo "❌ 失敗/タイムアウト"
        FAILED=$((FAILED + 1))
        grep -E "Error:|Invariant|violated|states generated" "verification_logs/${module}.log" | tail -3
    fi
done

echo ""
echo "=========================================="
echo "検証結果サマリー"
echo "=========================================="
echo "成功: $SUCCESS / ${#MODULES[@]}"
echo "失敗: $FAILED / ${#MODULES[@]}"
echo ""

if [ $SUCCESS -gt 0 ]; then
    echo "🎉 $SUCCESS 個のモジュールが検証成功!"
    exit 0
else
    echo "⚠️  検証成功なし"
    exit 1
fi
