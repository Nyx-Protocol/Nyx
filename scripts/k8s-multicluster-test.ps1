#!/usr/bin/env pwsh
# Nyx Multi-Cluster Interconnection Test Script
# 1つのサーバー内で複数のKubernetesクラスタを構築してNyxノード間の相互接続をテスト

param(
    [int]$NumClusters = 2,
    [switch]$CleanFirst
)

Write-Host "🚀 Starting Nyx Multi-Cluster Test Setup" -ForegroundColor Cyan

# クリーンアップ
if ($CleanFirst) {
    Write-Host "🧹 Cleaning up existing clusters..." -ForegroundColor Yellow
    1..$NumClusters | ForEach-Object {
        kind delete cluster --name "nyx-cluster-$_" 2>$null
    }
}

# クラスタの作成
Write-Host "🏗️  Creating $NumClusters Kind clusters..." -ForegroundColor Green
1..$NumClusters | ForEach-Object {
    $clusterName = "nyx-cluster-$_"
    Write-Host "  Creating $clusterName..." -ForegroundColor Gray
    kind create cluster --config kind-config.yaml --name $clusterName --wait 60s
}

# Dockerイメージのビルド
Write-Host "🔨 Building Nyx daemon Docker image..." -ForegroundColor Green
docker build -t nyx-daemon:latest .

# 各クラスタにイメージをロード
Write-Host "📦 Loading Docker image to clusters..." -ForegroundColor Green
1..$NumClusters | ForEach-Object {
    $clusterName = "nyx-cluster-$_"
    Write-Host "  Loading to $clusterName..." -ForegroundColor Gray
    kind load docker-image nyx-daemon:latest --name $clusterName
}

# Nyxノードのデプロイ
Write-Host "🚢 Deploying Nyx nodes to clusters..." -ForegroundColor Green
1..$NumClusters | ForEach-Object {
    $clusterName = "nyx-cluster-$_"
    $context = "kind-$clusterName"
    Write-Host "  Deploying to $clusterName..." -ForegroundColor Gray
    kubectl --context $context apply -f k8s-nyx-multinode.yaml
}

# 起動待機
Write-Host "⏳ Waiting for pods to be ready..." -ForegroundColor Yellow
Start-Sleep -Seconds 15

# 状態確認
Write-Host "`n📊 Cluster Status:" -ForegroundColor Cyan
1..$NumClusters | ForEach-Object {
    $clusterName = "nyx-cluster-$_"
    $context = "kind-$clusterName"
    Write-Host "`n🔍 $clusterName:" -ForegroundColor Green
    kubectl --context $context get pods -n nyxnet-test -o wide
}

# ノード間接続テスト
Write-Host "`n🔗 Testing inter-node connectivity..." -ForegroundColor Cyan
1..$NumClusters | ForEach-Object {
    $clusterName = "nyx-cluster-$_"
    $context = "kind-$clusterName"
    Write-Host "`n📡 Logs from $clusterName (mix-node-1):" -ForegroundColor Green
    kubectl --context $context logs -n nyxnet-test mix-node-1 --tail=20 2>$null
}

Write-Host "`n✅ Multi-cluster setup complete!" -ForegroundColor Green
Write-Host "`nUseful commands:" -ForegroundColor Yellow
Write-Host "  kubectl --context kind-nyx-cluster-1 get pods -n nyxnet-test"
Write-Host "  kubectl --context kind-nyx-cluster-1 logs -n nyxnet-test mix-node-1 -f"
Write-Host "  kubectl --context kind-nyx-cluster-1 exec -n nyxnet-test mix-node-1 -it -- /bin/bash"
Write-Host "`nTo cleanup:"
Write-Host "  1..$NumClusters | ForEach-Object { kind delete cluster --name nyx-cluster-`$_ }"
