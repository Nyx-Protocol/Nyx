#!/bin/bash
################################################################################
# ONE-LINER: Complete NyxNet Multi-VM Setup
# すべてのセットアップを自動実行
################################################################################

# VM番号を指定して実行
# curl -sSL https://raw.githubusercontent.com/SeleniaProject/NyxNet/main/scripts/oneliner-setup.sh | bash -s 1

VM_NUM=${1:-1}

echo "🚀 Starting NyxNet automated setup for VM-${VM_NUM}..."
echo ""

# Step 1: 基本システムセットアップ
echo "📦 Step 1/5: Installing system components..."
curl -sSL https://raw.githubusercontent.com/SeleniaProject/NyxNet/main/scripts/setup-vm-complete.sh | bash -s ${VM_NUM}

# Step 2: 再ログイン（Dockerグループ反映のため）
echo ""
echo "⚠️  Logout and login required for Docker group!"
echo "After re-login, run:"
echo ""
echo "# Step 2: Initialize K8s cluster"
echo "bash ~/NyxNet/scripts/init-k8s-cluster.sh control-plane ${VM_NUM}"
echo ""
echo "# Step 3: Clone and build NyxNet"
echo "cd ~/nyxnet/src && git clone https://github.com/SeleniaProject/NyxNet.git && cd NyxNet"
echo ""
echo "# Step 4: Deploy NyxNet"
echo "bash ~/NyxNet/scripts/deploy-nyxnet-multivm.sh"
echo ""
echo "# Step 5: Setup cross-VM network"
echo "bash ~/NyxNet/scripts/setup-cross-vm-network.sh"
echo ""
echo "# Step 6: Run tests"
echo "bash ~/NyxNet/scripts/test-cross-vm.sh"
