#!/bin/bash

# TLA+ Full Verification Script for NyxNet
# このスクリプトは全32モジュールの完全な検証を実行します

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# カラー出力
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# ログファイル
LOG_DIR="verification_logs"
mkdir -p "$LOG_DIR"
SUMMARY_LOG="$LOG_DIR/verification_summary.txt"
echo "NyxNet TLA+ 完全検証レポート - $(date)" > "$SUMMARY_LOG"
echo "============================================" >> "$SUMMARY_LOG"

# 統計
TOTAL_MODULES=0
PASSED_MODULES=0
FAILED_MODULES=0
SKIPPED_MODULES=0

# TLCパラメータ
WORKERS=4
MEMORY="4G"
DEPTH=100

# ヘルパー関数
print_header() {
    echo -e "\n${BLUE}========================================${NC}"
    echo -e "${BLUE}$1${NC}"
    echo -e "${BLUE}========================================${NC}\n"
}

print_success() {
    echo -e "${GREEN}✓ $1${NC}"
}

print_error() {
    echo -e "${RED}✗ $1${NC}"
}

print_warning() {
    echo -e "${YELLOW}⚠ $1${NC}"
}

print_info() {
    echo -e "${BLUE}ℹ $1${NC}"
}

# TLC実行関数
run_tlc() {
    local module=$1
    local config=$2
    local log_file="$LOG_DIR/${module}.log"
    local timeout=${3:-600}  # デフォルト10分
    
    TOTAL_MODULES=$((TOTAL_MODULES + 1))
    
    print_info "検証中: $module (タイムアウト: ${timeout}秒)"
    
    # 設定ファイルチェック
    if [ ! -f "$config" ]; then
        print_warning "設定ファイルが見つかりません: $config - スキップ"
        SKIPPED_MODULES=$((SKIPPED_MODULES + 1))
        echo "SKIPPED: $module - No config file" >> "$SUMMARY_LOG"
        return 1
    fi
    
    # TLA+ファイルチェック
    if [ ! -f "${module}.tla" ]; then
        print_warning "TLA+ファイルが見つかりません: ${module}.tla - スキップ"
        SKIPPED_MODULES=$((SKIPPED_MODULES + 1))
        echo "SKIPPED: $module - No TLA file" >> "$SUMMARY_LOG"
        return 1
    fi
    
    # TLC実行
    local start_time=$(date +%s)
    
    if timeout $timeout java -Xmx$MEMORY -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC \
        -workers $WORKERS \
        -deadlock \
        -depth $DEPTH \
        -config "$config" \
        "$module" > "$log_file" 2>&1; then
        
        local end_time=$(date +%s)
        local duration=$((end_time - start_time))
        
        # 結果解析
        local states=$(grep -oP "states generated: \K\d+" "$log_file" | tail -1)
        local distinct=$(grep -oP "distinct states: \K\d+" "$log_file" | tail -1)
        local depth=$(grep -oP "state graph diameter: \K\d+" "$log_file" | tail -1)
        
        print_success "$module - 成功 (${duration}秒, ${states:-N/A}状態, ${distinct:-N/A}ユニーク)"
        echo "PASS: $module - ${duration}s, ${states:-N/A} states, ${distinct:-N/A} distinct" >> "$SUMMARY_LOG"
        PASSED_MODULES=$((PASSED_MODULES + 1))
        return 0
    else
        local exit_code=$?
        local end_time=$(date +%s)
        local duration=$((end_time - start_time))
        
        if [ $exit_code -eq 124 ]; then
            print_error "$module - タイムアウト (${timeout}秒)"
            echo "TIMEOUT: $module - ${timeout}s" >> "$SUMMARY_LOG"
        else
            print_error "$module - 失敗 (終了コード: $exit_code)"
            
            # エラー詳細抽出
            if grep -q "Invariant.*is violated" "$log_file"; then
                local violated=$(grep -oP "Invariant \K\w+" "$log_file" | head -1)
                echo "FAIL: $module - Invariant violated: $violated" >> "$SUMMARY_LOG"
            elif grep -q "Deadlock reached" "$log_file"; then
                echo "FAIL: $module - Deadlock detected" >> "$SUMMARY_LOG"
            elif grep -q "Error:" "$log_file"; then
                local error=$(grep "Error:" "$log_file" | head -1)
                echo "FAIL: $module - $error" >> "$SUMMARY_LOG"
            else
                echo "FAIL: $module - Unknown error" >> "$SUMMARY_LOG"
            fi
        fi
        
        FAILED_MODULES=$((FAILED_MODULES + 1))
        return 1
    fi
}

# メイン検証シーケンス
print_header "NyxNet TLA+ 完全検証開始"

# Java確認
if ! command -v java &> /dev/null; then
    print_error "Javaが見つかりません。インストールしてください。"
    exit 1
fi

# tla2tools.jar確認
if [ ! -f "tla2tools.jar" ]; then
    print_error "tla2tools.jarが見つかりません。"
    exit 1
fi

print_success "環境チェック完了"
print_info "ワーカー数: $WORKERS, メモリ: $MEMORY, 深さ制限: $DEPTH"

# レベル1: 基本検証 (5分)
print_header "レベル1: 基本プロトコル検証"
run_tlc "NyxBasicVerification" "NyxBasicVerification.cfg" 300

# レベル2: コアコンポーネント (各10分)
print_header "レベル2: コアコンポーネント検証"
run_tlc "NyxCryptography" "NyxCryptography.cfg" 600
run_tlc "NyxNetworkLayer" "NyxNetworkLayer.cfg" 600
run_tlc "NyxStreamManagement" "NyxStreamManagement.cfg" 600

# レベル3: 高度な機能 (各15分)
print_header "レベル3: 高度な機能検証"
run_tlc "NyxFaultTolerance" "NyxFaultTolerance.cfg" 900
run_tlc "NyxQoSManagement" "NyxQoSManagement.cfg" 900
run_tlc "NyxDistributedConsensus" "NyxDistributedConsensus.cfg" 900

# レベル4: セキュリティとインフラ (各15分)
print_header "レベル4: セキュリティとインフラ検証"
run_tlc "NyxSecurityAudit" "NyxSecurityAudit.cfg" 900
run_tlc "NyxNFVAndSDN" "NyxNFVAndSDN.cfg" 900
run_tlc "NyxEdgeComputing" "NyxEdgeComputing.cfg" 900
run_tlc "NyxTimeSensitiveNetworking" "NyxTimeSensitiveNetworking.cfg" 900
run_tlc "NyxConfigurationValidation" "NyxConfigurationValidation.cfg" 900

# レベル5: その他の重要モジュール (各10分)
print_header "レベル5: その他の重要モジュール検証"

# これらのモジュールの設定ファイルが存在する場合のみ実行
[ -f "NyxSecurityProperties.cfg" ] && run_tlc "NyxSecurityProperties" "NyxSecurityProperties.cfg" 600
[ -f "NyxProtocolIntegration.cfg" ] && run_tlc "NyxProtocolIntegration" "NyxProtocolIntegration.cfg" 600
[ -f "NyxPerformanceModels.cfg" ] && run_tlc "NyxPerformanceModels" "NyxPerformanceModels.cfg" 600
[ -f "NyxConcurrencyModels.cfg" ] && run_tlc "NyxConcurrencyModels" "NyxConcurrencyModels.cfg" 600
[ -f "NyxErrorHandling.cfg" ] && run_tlc "NyxErrorHandling" "NyxErrorHandling.cfg" 600
[ -f "NyxMonitoring.cfg" ] && run_tlc "NyxMonitoring" "NyxMonitoring.cfg" 600
[ -f "NyxMobilityManagement.cfg" ] && run_tlc "NyxMobilityManagement" "NyxMobilityManagement.cfg" 600
[ -f "NyxRoutingProtocols.cfg" ] && run_tlc "NyxRoutingProtocols" "NyxRoutingProtocols.cfg" 600
[ -f "NyxDataPlane.cfg" ] && run_tlc "NyxDataPlane" "NyxDataPlane.cfg" 600
[ -f "NyxControlPlane.cfg" ] && run_tlc "NyxControlPlane" "NyxControlPlane.cfg" 600
[ -f "NyxStorageLayer.cfg" ] && run_tlc "NyxStorageLayer" "NyxStorageLayer.cfg" 600
[ -f "NyxAPILayer.cfg" ] && run_tlc "NyxAPILayer" "NyxAPILayer.cfg" 600
[ -f "NyxTestingFramework.cfg" ] && run_tlc "NyxTestingFramework" "NyxTestingFramework.cfg" 600
[ -f "NyxDeploymentModels.cfg" ] && run_tlc "NyxDeploymentModels" "NyxDeploymentModels.cfg" 600
[ -f "NyxAdvancedOptimization.cfg" ] && run_tlc "NyxAdvancedOptimization" "NyxAdvancedOptimization.cfg" 600

# サマリー出力
print_header "検証完了サマリー"

echo "" >> "$SUMMARY_LOG"
echo "============================================" >> "$SUMMARY_LOG"
echo "サマリー:" >> "$SUMMARY_LOG"
echo "  合計モジュール: $TOTAL_MODULES" >> "$SUMMARY_LOG"
echo "  成功: $PASSED_MODULES" >> "$SUMMARY_LOG"
echo "  失敗: $FAILED_MODULES" >> "$SUMMARY_LOG"
echo "  スキップ: $SKIPPED_MODULES" >> "$SUMMARY_LOG"
echo "============================================" >> "$SUMMARY_LOG"

print_info "合計モジュール: $TOTAL_MODULES"
print_success "成功: $PASSED_MODULES"
print_error "失敗: $FAILED_MODULES"
print_warning "スキップ: $SKIPPED_MODULES"

# 成功率計算
if [ $TOTAL_MODULES -gt 0 ]; then
    SUCCESS_RATE=$((PASSED_MODULES * 100 / TOTAL_MODULES))
    print_info "成功率: ${SUCCESS_RATE}%"
    echo "成功率: ${SUCCESS_RATE}%" >> "$SUMMARY_LOG"
fi

print_info "詳細ログ: $LOG_DIR/"
print_info "サマリーレポート: $SUMMARY_LOG"

# 失敗したモジュールのリスト
if [ $FAILED_MODULES -gt 0 ]; then
    echo "" >> "$SUMMARY_LOG"
    echo "失敗したモジュール:" >> "$SUMMARY_LOG"
    grep "^FAIL:" "$SUMMARY_LOG" | sed 's/^FAIL: /  - /' >> "$SUMMARY_LOG"
    
    print_header "失敗したモジュール"
    grep "^FAIL:" "$SUMMARY_LOG" | sed 's/^FAIL: /  /'
fi

# 終了コード
if [ $FAILED_MODULES -gt 0 ]; then
    print_error "検証に失敗したモジュールがあります"
    exit 1
else
    print_success "すべてのモジュールが検証に成功しました！"
    exit 0
fi
