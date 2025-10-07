#!/usr/bin/env bash

##############################################################################
# Nyx Multi-Cluster Test - One-Click Setup & Test Script
# 
# This script will:
# 1. Check system requirements
# 2. Install all dependencies (Docker, kubectl, kind)
# 3. Create multiple Kubernetes clusters
# 4. Deploy test pods
# 5. Run inter-cluster communication tests
# 6. Generate beautiful test reports
# 7. Cleanup resources
#
# Usage: bash setup-and-test.sh
##############################################################################

set -euo pipefail

# 色とスタイル
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
MAGENTA='\033[0;35m'
CYAN='\033[0;36m'
WHITE='\033[1;37m'
BOLD='\033[1m'
DIM='\033[2m'
NC='\033[0m'

# 絵文字
ROCKET="🚀"
CHECK="✅"
CROSS="❌"
WARNING="⚠️"
INFO="ℹ️"
FIRE="🔥"
PACKAGE="📦"
WRENCH="🔧"
SPARKLES="✨"

echo -e "\n${BOLD}${CYAN}════════════════════════════════════════════════════════════════════${NC}"
echo -e "${BOLD}${MAGENTA}    ${ROCKET} NYX MULTI-CLUSTER TEST - AUTO SETUP ${ROCKET}${NC}"
echo -e "${BOLD}${CYAN}════════════════════════════════════════════════════════════════════${NC}\n"

# スクリプトディレクトリ
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo -e "${CYAN}${INFO}  Detected script directory: ${SCRIPT_DIR}${NC}\n"

# rootチェック（sudoは使うがrootでは実行しない）
if [ "$EUID" -eq 0 ]; then
    echo -e "${RED}${CROSS}  Please do not run this script as root!${NC}"
    echo -e "${YELLOW}${WARNING}  Run as a regular user. The script will use sudo when needed.${NC}"
    exit 1
fi

# OSチェック
if [ -f /etc/os-release ]; then
    . /etc/os-release
    echo -e "${GREEN}${CHECK}  Detected OS: ${NAME} ${VERSION}${NC}"
    
    if [[ "$ID" != "ubuntu" ]] && [[ "$ID_LIKE" != *"ubuntu"* ]] && [[ "$ID_LIKE" != *"debian"* ]]; then
        echo -e "${YELLOW}${WARNING}  This script is optimized for Ubuntu/Debian.${NC}"
        echo -e "${YELLOW}${WARNING}  It may not work correctly on ${NAME}.${NC}"
        read -p "Continue anyway? (y/N) " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            exit 1
        fi
    fi
else
    echo -e "${YELLOW}${WARNING}  Could not detect OS. Proceeding with caution...${NC}"
fi

echo ""

# sudoパスワードを先に取得
echo -e "${CYAN}${WRENCH}  This script requires sudo privileges for installation.${NC}"
echo -e "${DIM}You may be prompted for your password...${NC}\n"
sudo -v

# バックグラウンドでsudoを維持
while true; do sudo -n true; sleep 60; kill -0 "$$" || exit; done 2>/dev/null &

# 必要なディレクトリ作成
mkdir -p "${SCRIPT_DIR}/scripts"
mkdir -p "${SCRIPT_DIR}/logs"

# スクリプトファイルが存在するか確認
if [ ! -f "${SCRIPT_DIR}/scripts/k8s-test-logger.sh" ]; then
    echo -e "${RED}${CROSS}  Required file not found: scripts/k8s-test-logger.sh${NC}"
    echo -e "${YELLOW}${WARNING}  Please ensure all script files are present.${NC}"
    exit 1
fi

if [ ! -f "${SCRIPT_DIR}/scripts/k8s-multi-cluster-test.sh" ]; then
    echo -e "${RED}${CROSS}  Required file not found: scripts/k8s-multi-cluster-test.sh${NC}"
    echo -e "${YELLOW}${WARNING}  Please ensure all script files are present.${NC}"
    exit 1
fi

# スクリプトに実行権限を付与
chmod +x "${SCRIPT_DIR}/scripts/"*.sh

# メインテストスクリプトを実行
echo -e "${GREEN}${SPARKLES}  Starting main test script...${NC}\n"

cd "${SCRIPT_DIR}"
bash "${SCRIPT_DIR}/scripts/k8s-multi-cluster-test.sh" "$@"

exit_code=$?

if [ $exit_code -eq 0 ]; then
    echo -e "\n${GREEN}${FIRE}  ALL TESTS COMPLETED SUCCESSFULLY! ${FIRE}${NC}\n"
else
    echo -e "\n${RED}${CROSS}  Tests completed with errors (exit code: ${exit_code})${NC}\n"
fi

exit $exit_code
