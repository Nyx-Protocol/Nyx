#!/usr/bin/env bash

# カラーコード
export RED='\033[0;31m'
export GREEN='\033[0;32m'
export YELLOW='\033[1;33m'
export BLUE='\033[0;34m'
export MAGENTA='\033[0;35m'
export CYAN='\033[0;36m'
export WHITE='\033[1;37m'
export BOLD='\033[1m'
export DIM='\033[2m'
export NC='\033[0m' # No Color

# 絵文字
export EMOJI_ROCKET="🚀"
export EMOJI_CHECK="✅"
export EMOJI_CROSS="❌"
export EMOJI_WARNING="⚠️"
export EMOJI_INFO="ℹ️"
export EMOJI_FIRE="🔥"
export EMOJI_STAR="⭐"
export EMOJI_CLOCK="⏱️"
export EMOJI_SPARKLES="✨"
export EMOJI_PACKAGE="📦"
export EMOJI_HAMMER="🔨"
export EMOJI_GLOBE="🌐"
export EMOJI_LINK="🔗"
export EMOJI_CHART="📊"
export EMOJI_TROPHY="🏆"

# タイムスタンプ取得
timestamp() {
    date +"%Y-%m-%d %H:%M:%S"
}

# ログレベル別出力
log_header() {
    echo -e "\n${BOLD}${CYAN}╔════════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${BOLD}${CYAN}║${NC} ${EMOJI_SPARKLES} ${BOLD}${WHITE}$1${NC}"
    echo -e "${BOLD}${CYAN}╚════════════════════════════════════════════════════════════════╝${NC}\n"
}

log_section() {
    echo -e "\n${BOLD}${BLUE}▶ ${EMOJI_ROCKET} $1${NC}"
    echo -e "${DIM}$(timestamp)${NC}"
}

log_info() {
    echo -e "${CYAN}${EMOJI_INFO}  [INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}${EMOJI_CHECK}  [SUCCESS]${NC} ${BOLD}$1${NC}"
}

log_warning() {
    echo -e "${YELLOW}${EMOJI_WARNING}  [WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}${EMOJI_CROSS}  [ERROR]${NC} ${BOLD}$1${NC}"
}

log_step() {
    local step=$1
    local total=$2
    local message=$3
    echo -e "${MAGENTA}${EMOJI_STAR}  [${step}/${total}]${NC} ${WHITE}${message}${NC}"
}

# プログレスバー
show_progress() {
    local current=$1
    local total=$2
    local width=50
    local percentage=$((current * 100 / total))
    local filled=$((width * current / total))
    local empty=$((width - filled))
    
    printf "\r${CYAN}${EMOJI_CLOCK}  Progress: [${NC}"
    printf "%${filled}s" | tr ' ' '█'
    printf "%${empty}s" | tr ' ' '░'
    printf "${CYAN}] ${BOLD}${WHITE}%3d%%${NC}" $percentage
    
    if [ $current -eq $total ]; then
        echo ""
    fi
}

# スピナー
spinner() {
    local pid=$1
    local message=$2
    local spinstr='⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏'
    local i=0
    
    while kill -0 $pid 2>/dev/null; do
        i=$(( (i+1) %10 ))
        printf "\r${CYAN}${spinstr:$i:1}  ${NC}${message}..."
        sleep 0.1
    done
    printf "\r"
}

# ボックス描画
draw_box() {
    local title=$1
    local content=$2
    local width=66
    
    echo -e "${BOLD}${BLUE}┌$(printf '─%.0s' $(seq 1 $width))┐${NC}"
    echo -e "${BOLD}${BLUE}│${NC} ${BOLD}${WHITE}${title}${NC}"
    echo -e "${BOLD}${BLUE}├$(printf '─%.0s' $(seq 1 $width))┤${NC}"
    echo -e "${content}" | while IFS= read -r line; do
        printf "${BOLD}${BLUE}│${NC} %-${width}s ${BOLD}${BLUE}│${NC}\n" "$line"
    done
    echo -e "${BOLD}${BLUE}└$(printf '─%.0s' $(seq 1 $width))┘${NC}"
}

# テーブルヘッダー
table_header() {
    echo -e "\n${BOLD}${CYAN}╔══════════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${BOLD}${CYAN}║${NC} $1"
    echo -e "${BOLD}${CYAN}╠══════════════════════════════════════════════════════════════════╣${NC}"
}

table_row() {
    local col1=$1
    local col2=$2
    local col3=$3
    printf "${BOLD}${CYAN}║${NC} %-20s ${BOLD}${CYAN}│${NC} %-20s ${BOLD}${CYAN}│${NC} %-18s ${BOLD}${CYAN}║${NC}\n" "$col1" "$col2" "$col3"
}

table_footer() {
    echo -e "${BOLD}${CYAN}╚══════════════════════════════════════════════════════════════════╝${NC}\n"
}

# サマリーボックス
show_summary() {
    local total=$1
    local passed=$2
    local failed=$3
    local duration=$4
    
    echo -e "\n${BOLD}${CYAN}╔══════════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${BOLD}${CYAN}║${NC}  ${EMOJI_TROPHY} ${BOLD}${WHITE}TEST SUMMARY${NC}"
    echo -e "${BOLD}${CYAN}╠══════════════════════════════════════════════════════════════════╣${NC}"
    echo -e "${BOLD}${CYAN}║${NC}  ${EMOJI_CHART} Total Tests:      ${BOLD}${WHITE}${total}${NC}"
    echo -e "${BOLD}${CYAN}║${NC}  ${EMOJI_CHECK} Passed:           ${BOLD}${GREEN}${passed}${NC}"
    echo -e "${BOLD}${CYAN}║${NC}  ${EMOJI_CROSS} Failed:           ${BOLD}${RED}${failed}${NC}"
    echo -e "${BOLD}${CYAN}║${NC}  ${EMOJI_CLOCK} Duration:         ${BOLD}${YELLOW}${duration}s${NC}"
    echo -e "${BOLD}${CYAN}║${NC}  ${EMOJI_FIRE} Success Rate:     ${BOLD}${GREEN}$((passed * 100 / total))%${NC}"
    echo -e "${BOLD}${CYAN}╚══════════════════════════════════════════════════════════════════╝${NC}\n"
}

# バナー表示
show_banner() {
    echo -e "\n${BOLD}${CYAN}════════════════════════════════════════════════════════════════════${NC}"
    echo -e "${BOLD}${MAGENTA}    🚀 NYX MULTI-CLUSTER KUBERNETES TEST FRAMEWORK 🚀${NC}"
    echo -e "${BOLD}${CYAN}════════════════════════════════════════════════════════════════════${NC}\n"
    echo -e "${DIM}Multi-Cluster Inter-Communication Test System${NC}"
    echo -e "${DIM}Automated Setup | Beautiful Logs | Fast Results${NC}\n"
}

# クラスター情報表示
show_cluster_info() {
    local cluster_name=$1
    local status=$2
    local pods=$3
    
    if [ "$status" = "ready" ]; then
        echo -e "  ${GREEN}${EMOJI_CHECK}${NC} ${BOLD}${cluster_name}${NC} - ${GREEN}Ready${NC} (${pods} pods)"
    else
        echo -e "  ${RED}${EMOJI_CROSS}${NC} ${BOLD}${cluster_name}${NC} - ${RED}Not Ready${NC}"
    fi
}

# エクスポート関数
export -f timestamp
export -f log_header
export -f log_section
export -f log_info
export -f log_success
export -f log_warning
export -f log_error
export -f log_step
export -f show_progress
export -f spinner
export -f draw_box
export -f table_header
export -f table_row
export -f table_footer
export -f show_summary
export -f show_banner
export -f show_cluster_info
