#!/bin/bash
# Quick TLA+ Verification Script
# 主要モジュールのみを高速検証

cd "$(dirname "$0")"

echo "================================================"
echo "NyxNet TLA+ 高速検証スクリプト"
echo "================================================"
echo ""

# 色定義
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# 統計
TOTAL=0
PASSED=0
FAILED=0
SKIPPED=0

# ログディレクトリ
mkdir -p verification_logs

# 検証関数
verify() {
    local module=$1
    local config=$2
    local timeout=${3:-120}
    
    TOTAL=$((TOTAL + 1))
    
    if [ ! -f "${module}.tla" ]; then
        echo -e "${YELLOW}SKIP${NC}: $module - TLA+ファイルなし"
        SKIPPED=$((SKIPPED + 1))
        return
    fi
    
    if [ ! -f "$config" ]; then
        echo -e "${YELLOW}SKIP${NC}: $module - 設定ファイルなし"
        SKIPPED=$((SKIPPED + 1))
        return
    fi
    
    echo -n "検証中: $module ... "
    
    if timeout $timeout java -Xmx2G -cp tla2tools.jar tlc2.TLC \
        -workers 2 -deadlock -depth 20 \
        -config "$config" "$module" > "verification_logs/${module}.log" 2>&1; then
        
        local states=$(grep -oP "states generated: \K\d+" "verification_logs/${module}.log" | tail -1)
        echo -e "${GREEN}OK${NC} (${states:-?} states)"
        PASSED=$((PASSED + 1))
    else
        echo -e "${RED}FAIL${NC}"
        FAILED=$((FAILED + 1))
        
        # エラー詳細
        if grep -q "Invariant.*is violated" "verification_logs/${module}.log"; then
            local inv=$(grep -oP "Invariant \K\w+" "verification_logs/${module}.log" | head -1)
            echo "  → Invariant violated: $inv"
        elif grep -q "Deadlock" "verification_logs/${module}.log"; then
            echo "  → Deadlock detected"
        fi
    fi
}

echo "開始時刻: $(date)"
echo ""

# レベル1: 基本検証
echo -e "${BLUE}[レベル1] 基本プロトコル${NC}"
verify "NyxBasicVerification" "NyxBasicVerification.cfg" 180

# レベル2: コア機能
echo ""
echo -e "${BLUE}[レベル2] コア機能${NC}"
verify "NyxCryptography" "NyxCryptography.cfg" 300
verify "NyxNetworkLayer" "NyxNetworkLayer.cfg" 300
verify "NyxStreamManagement" "NyxStreamManagement.cfg" 300

# レベル3: 高度な機能
echo ""
echo -e "${BLUE}[レベル3] 高度な機能${NC}"
verify "NyxFaultTolerance" "NyxFaultTolerance.cfg" 300
verify "NyxQoSManagement" "NyxQoSManagement.cfg" 300
verify "NyxDistributedConsensus" "NyxDistributedConsensus.cfg" 300

# レベル4: セキュリティとインフラ
echo ""
echo -e "${BLUE}[レベル4] セキュリティとインフラ${NC}"
verify "NyxSecurityAudit" "NyxSecurityAudit.cfg" 300
verify "NyxNFVAndSDN" "NyxNFVAndSDN.cfg" 300
verify "NyxEdgeComputing" "NyxEdgeComputing.cfg" 300
verify "NyxTimeSensitiveNetworking" "NyxTimeSensitiveNetworking.cfg" 300
verify "NyxConfigurationValidation" "NyxConfigurationValidation.cfg" 300

# サマリー
echo ""
echo "================================================"
echo -e "${BLUE}検証結果サマリー${NC}"
echo "================================================"
echo "合計: $TOTAL"
echo -e "${GREEN}成功: $PASSED${NC}"
echo -e "${RED}失敗: $FAILED${NC}"
echo -e "${YELLOW}スキップ: $SKIPPED${NC}"
echo ""
echo "終了時刻: $(date)"
echo ""

if [ $FAILED -gt 0 ]; then
    echo -e "${RED}失敗したモジュールがあります${NC}"
    echo "詳細: verification_logs/ を確認してください"
    exit 1
else
    echo -e "${GREEN}すべての検証に成功しました！${NC}"
    exit 0
fi
