#!/bin/bash
# 全モジュールの包括的検証

cd "$(dirname "$0")"

echo "==========================================" 
echo "NyxNet TLA+ 全モジュール検証"
echo "==========================================" 
echo ""

# すべての検証対象モジュール
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
SKIPPED=0

mkdir -p verification_logs

for module in "${MODULES[@]}"; do
    echo "----------------------------------------"
    echo "検証中: $module"
    
    # cfgファイルが存在するかチェック
    if [ ! -f "${module}.cfg" ]; then
        echo "⚠️  設定ファイルなし - スキップ"
        SKIPPED=$((SKIPPED + 1))
        continue
    fi
    
    # TLAファイルが存在するかチェック
    if [ ! -f "${module}.tla" ]; then
        echo "⚠️  TLA+ファイルなし - スキップ"
        SKIPPED=$((SKIPPED + 1))
        continue
    fi
    
    # 検証実行 (120秒タイムアウト)
    if timeout 120 java -Xmx2G -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC \
        -workers 2 -deadlock -depth 10 \
        -config ${module}.cfg ${module} \
        > verification_logs/${module}_final.log 2>&1; then
        
        # 成功判定
        if grep -q "Finished computing initial states" verification_logs/${module}_final.log; then
            echo "✅ 成功"
            SUCCESS=$((SUCCESS + 1))
        elif grep -q "Parse Error" verification_logs/${module}_final.log; then
            echo "❌ 構文エラー"
            grep "Parse Error" verification_logs/${module}_final.log -A 2 | head -5
            FAILED=$((FAILED + 1))
        else
            echo "❌ 検証失敗"
            tail -10 verification_logs/${module}_final.log
            FAILED=$((FAILED + 1))
        fi
    else
        # タイムアウトまたはエラー
        if grep -q "Parse Error" verification_logs/${module}_final.log; then
            echo "❌ 構文エラー (タイムアウト前)"
            grep "Parse Error" verification_logs/${module}_final.log -A 2 | head -5
        else
            echo "⏱️  タイムアウト/エラー"
        fi
        FAILED=$((FAILED + 1))
    fi
    
    echo ""
done

echo "==========================================" 
echo "検証結果サマリー"
echo "==========================================" 
echo "合計モジュール: $TOTAL"
echo "成功: $SUCCESS"
echo "失敗: $FAILED"
echo "スキップ: $SKIPPED"
echo "==========================================" 

if [ $SUCCESS -eq $TOTAL ]; then
    echo "🎉 すべてのモジュールが完璧に検証されました！"
    exit 0
else
    echo "⚠️  一部のモジュールに問題があります"
    exit 1
fi
