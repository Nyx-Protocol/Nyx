#!/usr/bin/env bash

##############################################################################
# NyxNet Mix Network Test - Setup and Test Script
# 
# This script automates the complete NyxNet Mix Network verification:
# 1. Install dependencies (Docker, kubectl, kind, Rust, Go)
# 2. Build NyxNet components
# 3. Create Kubernetes clusters
# 4. Deploy NyxNet Mix Network
# 5. Run anonymization tests
# 6. Generate reports
##############################################################################

set -euo pipefail

# Colors and styles
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

# Emojis
ROCKET="🚀"
CHECK="✅"
CROSS="❌"
WARNING="⚠️"
INFO="ℹ️"
FIRE="🔥"
PACKAGE="📦"
WRENCH="🔧"
SPARKLES="✨"
LOCK="🔐"

echo -e "\n${BOLD}${CYAN}════════════════════════════════════════════════════════════════════${NC}"
echo -e "${BOLD}${MAGENTA}    ${LOCK} NYXNET MIX NETWORK TEST - AUTO SETUP ${LOCK}${NC}"
echo -e "${BOLD}${CYAN}════════════════════════════════════════════════════════════════════${NC}\n"

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo -e "${CYAN}${INFO}  Detected script directory: ${SCRIPT_DIR}${NC}\n"

# Root check
if [ "$EUID" -eq 0 ]; then
    echo -e "${YELLOW}${WARNING}  Running as root user detected.${NC}"
    IS_ROOT=true
    SUDO_CMD=""
else
    IS_ROOT=false
    SUDO_CMD="sudo"
fi

# OS check
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

# Get sudo password upfront
if [ "$IS_ROOT" = false ]; then
    echo -e "${CYAN}${WRENCH}  This script requires sudo privileges for installation.${NC}"
    echo -e "${DIM}You may be prompted for your password...${NC}\n"
    $SUDO_CMD -v

    # Keep sudo alive
    while true; do $SUDO_CMD -n true; sleep 60; kill -0 "$$" || exit; done 2>/dev/null &
else
    echo -e "${INFO}  Running with root privileges - no sudo needed.${NC}\n"
fi

# Create necessary directories
mkdir -p "${SCRIPT_DIR}/scripts"
mkdir -p "${SCRIPT_DIR}/logs"

# Check for required scripts
if [ ! -f "${SCRIPT_DIR}/scripts/k8s-test-logger.sh" ]; then
    echo -e "${RED}${CROSS}  Required file not found: scripts/k8s-test-logger.sh${NC}"
    exit 1
fi

if [ ! -f "${SCRIPT_DIR}/scripts/k8s-nyx-test.sh" ]; then
    echo -e "${RED}${CROSS}  Required file not found: scripts/k8s-nyx-test.sh${NC}"
    exit 1
fi

# Load logger
source "${SCRIPT_DIR}/scripts/k8s-test-logger.sh"

# Install Rust
install_rust() {
    log_section "Installing Rust toolchain"
    
    if command -v rustc >/dev/null 2>&1; then
        log_info "Rust already installed: $(rustc --version)"
        return 0
    fi
    
    log_info "Installing Rust via rustup..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    
    # Source cargo env
    source "$HOME/.cargo/env"
    
    log_success "Rust installed: $(rustc --version)"
}

# Install Go
install_go() {
    log_section "Installing Go"
    
    if command -v go >/dev/null 2>&1; then
        local go_version=$(go version | awk '{print $3}')
        log_info "Go already installed: ${go_version}"
        return 0
    fi
    
    log_info "Installing Go 1.21..."
    
    local GO_VERSION="1.21.5"
    local GO_ARCH="amd64"
    
    wget "https://go.dev/dl/go${GO_VERSION}.linux-${GO_ARCH}.tar.gz" -O /tmp/go.tar.gz
    $SUDO_CMD rm -rf /usr/local/go
    $SUDO_CMD tar -C /usr/local -xzf /tmp/go.tar.gz
    rm /tmp/go.tar.gz
    
    # Add to PATH
    if ! grep -q "/usr/local/go/bin" ~/.profile; then
        echo 'export PATH=$PATH:/usr/local/go/bin' >> ~/.profile
    fi
    
    export PATH=$PATH:/usr/local/go/bin
    
    log_success "Go installed: $(go version)"
}

# Install Docker
install_docker() {
    log_section "Installing Docker"
    
    if command -v docker >/dev/null 2>&1; then
        log_info "Docker already installed: $(docker --version)"
        return 0
    fi
    
    log_info "Installing Docker..."
    
    # Remove old versions
    $SUDO_CMD apt-get remove -y docker docker-engine docker.io containerd runc 2>/dev/null || true
    
    # Install dependencies
    $SUDO_CMD apt-get update
    $SUDO_CMD apt-get install -y \
        ca-certificates \
        curl \
        gnupg \
        lsb-release
    
    # Add Docker GPG key
    $SUDO_CMD install -m 0755 -d /etc/apt/keyrings
    curl -fsSL https://download.docker.com/linux/ubuntu/gpg | $SUDO_CMD gpg --dearmor -o /etc/apt/keyrings/docker.gpg
    $SUDO_CMD chmod a+r /etc/apt/keyrings/docker.gpg
    
    # Add Docker repository
    echo \
      "deb [arch=$(dpkg --print-architecture) signed-by=/etc/apt/keyrings/docker.gpg] https://download.docker.com/linux/ubuntu \
      $(lsb_release -cs) stable" | $SUDO_CMD tee /etc/apt/sources.list.d/docker.list > /dev/null
    
    # Install Docker
    $SUDO_CMD apt-get update
    $SUDO_CMD apt-get install -y docker-ce docker-ce-cli containerd.io docker-buildx-plugin
    
    # Start Docker
    $SUDO_CMD systemctl start docker
    $SUDO_CMD systemctl enable docker
    
    # Add user to docker group
    if [ "$IS_ROOT" = false ]; then
        $SUDO_CMD usermod -aG docker "$USER"
        log_warning "You may need to log out and back in for docker group changes to take effect"
    fi
    
    log_success "Docker installed: $(docker --version)"
}

# Install kubectl
install_kubectl() {
    log_section "Installing kubectl"
    
    if command -v kubectl >/dev/null 2>&1; then
        log_info "kubectl already installed: $(kubectl version --client --short 2>/dev/null || kubectl version --client)"
        return 0
    fi
    
    log_info "Installing kubectl..."
    
    curl -LO "https://dl.k8s.io/release/$(curl -L -s https://dl.k8s.io/release/stable.txt)/bin/linux/amd64/kubectl"
    $SUDO_CMD install -o root -g root -m 0755 kubectl /usr/local/bin/kubectl
    rm kubectl
    
    log_success "kubectl installed: $(kubectl version --client --short 2>/dev/null || kubectl version --client)"
}

# Install kind
install_kind() {
    log_section "Installing kind"
    
    if command -v kind >/dev/null 2>&1; then
        log_info "kind already installed: $(kind version)"
        return 0
    fi
    
    log_info "Installing kind..."
    
    curl -Lo /tmp/kind https://kind.sigs.k8s.io/dl/v0.20.0/kind-linux-amd64
    $SUDO_CMD install -o root -g root -m 0755 /tmp/kind /usr/local/bin/kind
    rm /tmp/kind
    
    log_success "kind installed: $(kind version)"
}

# Main execution
main() {
    log_section "NyxNet Mix Network Test - Automated Setup"
    
    echo -e "${CYAN}${INFO}  This script will:${NC}"
    echo -e "${DIM}  1. Install dependencies (Rust, Go, Docker, kubectl, kind)${NC}"
    echo -e "${DIM}  2. Build NyxNet components (~30 minutes first time)${NC}"
    echo -e "${DIM}  3. Create 3 Kubernetes clusters${NC}"
    echo -e "${DIM}  4. Deploy NyxNet Mix Network${NC}"
    echo -e "${DIM}  5. Run anonymization tests${NC}"
    echo -e "${DIM}  6. Generate test reports${NC}"
    echo ""
    
    read -p "Continue? (y/N) " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        exit 0
    fi
    
    # Install dependencies
    install_rust
    install_go
    install_docker
    install_kubectl
    install_kind
    
    log_section "Running NyxNet Mix Network Test"
    
    # Run the main test script
    bash "${SCRIPT_DIR}/scripts/k8s-nyx-test.sh"
    
    log_section "Setup Complete!"
    log_success "NyxNet Mix Network test completed successfully! ${SPARKLES}"
}

main "$@"
