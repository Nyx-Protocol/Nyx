# NyxNet Multi-VM Testing - Quick Reference

## 🎯 超簡単ワンライナーセットアップ

### 各VMで実行するコマンド一覧

```bash
# ============================================================
# VM1 のセットアップ
# ============================================================

# 1. システム完全セットアップ（Docker, K8s, Rust）
curl -sSL https://raw.githubusercontent.com/SeleniaProject/NyxNet/main/scripts/setup-vm-complete.sh | bash -s 1

# ログアウト・ログイン後に以下を実行:

# 2. K8s Control Plane初期化
cd ~/NyxNet/scripts && bash init-k8s-cluster.sh control-plane 1

# 3. NyxNetクローン＆ビルド
cd ~/nyxnet/src && git clone https://github.com/SeleniaProject/NyxNet.git && cd NyxNet && cargo build --release

# 4. NyxNetデプロイ
bash ~/NyxNet/scripts/deploy-nyxnet-multivm.sh

# 5. クロスVM通信設定
bash ~/NyxNet/scripts/setup-cross-vm-network.sh

# 6. IPアドレス編集（実際のIPに変更）
vim ~/nyxnet/config/clusters/global-directory.yaml

# 7. テスト実行
bash ~/NyxNet/scripts/test-cross-vm.sh


# ============================================================
# VM2 のセットアップ
# ============================================================

# 1. システム完全セットアップ
curl -sSL https://raw.githubusercontent.com/SeleniaProject/NyxNet/main/scripts/setup-vm-complete.sh | bash -s 2

# ログアウト・ログイン後:

# 2-7. VM1と同じコマンド（VM番号だけ変える）
cd ~/NyxNet/scripts && bash init-k8s-cluster.sh control-plane 2
cd ~/nyxnet/src && git clone https://github.com/SeleniaProject/NyxNet.git && cd NyxNet && cargo build --release
bash ~/NyxNet/scripts/deploy-nyxnet-multivm.sh
bash ~/NyxNet/scripts/setup-cross-vm-network.sh
vim ~/nyxnet/config/clusters/global-directory.yaml
bash ~/NyxNet/scripts/test-cross-vm.sh


# ============================================================
# VM3 のセットアップ
# ============================================================

# 同様にVM番号を3に変更して実行
curl -sSL https://raw.githubusercontent.com/SeleniaProject/NyxNet/main/scripts/setup-vm-complete.sh | bash -s 3
# ... 以下同様


# ============================================================
# 全VM共通: global-directory.yaml設定
# ============================================================

# VM1で編集後、他のVMにコピー
scp ~/nyxnet/config/clusters/global-directory.yaml user@192.168.1.102:~/nyxnet/config/clusters/
scp ~/nyxnet/config/clusters/global-directory.yaml user@192.168.1.103:~/nyxnet/config/clusters/
```

## 📋 チェックリスト

### VM準備
- [ ] Proxmoxで3つのVMを作成 (各VM: 2 CPU, 4GB RAM)
- [ ] Ubuntu 22.04 LTSをインストール
- [ ] 固定IPアドレス設定 (192.168.1.101-103)
- [ ] SSH接続確認

### セットアップ実行
- [ ] 各VMで `setup-vm-complete.sh` 実行
- [ ] ログアウト・ログイン実行
- [ ] 各VMでK8sクラスタ初期化
- [ ] NyxNetクローン＆ビルド
- [ ] NyxNetデプロイ

### ネットワーク設定
- [ ] `global-directory.yaml` のIPアドレス編集
- [ ] 全VMに設定ファイルコピー
- [ ] ファイアウォールルール確認

### テスト実行
- [ ] 各VMでローカルテスト実行
- [ ] クロスVM通信確認
- [ ] パフォーマンステスト

## 🔍 確認コマンド

```bash
# K8s状態確認
kubectl get nodes
kubectl get pods -n nyxnet-vm1
kubectl get svc -n nyxnet-vm1

# NyxNetログ確認
kubectl logs -n nyxnet-vm1 mix-node-1 -f

# ポート疎通確認
nc -zv 192.168.1.102 30101

# リソース使用状況
kubectl top pods -n nyxnet-vm1
kubectl top nodes

# VM情報確認
cat ~/nyxnet/vm-info.json
cat ~/nyxnet/deployment-info.json
cat ~/nyxnet/network-info.json
cat ~/nyxnet/test-results.json
```

## 🐛 よくある問題と解決法

### 問題1: Docker権限エラー
```bash
# 解決策: ログアウト・ログインする
# または
newgrp docker
```

### 問題2: K8s Podが起動しない
```bash
# CNI確認
kubectl get pods -n kube-system

# Flannel再起動
kubectl delete pods -n kube-system -l app=flannel
```

### 問題3: クロスVM通信不可
```bash
# ファイアウォール無効化（テスト時）
sudo ufw disable

# ルート確認
ip route
ping 192.168.1.102
```

### 問題4: ビルドエラー
```bash
# Rust更新
rustup update stable

# 依存関係再取得
cargo clean && cargo build --release
```

## 📊 期待される結果

### テスト成功時
```
========================================
Test Results Summary
========================================
Total Tests:  15
Passed:       15
Failed:       0
Pass Rate:    100%

All tests passed! ✓
```

### デプロイ成功時
```
NAME          READY   STATUS    RESTARTS   AGE
mix-node-1    1/1     Running   0          2m
mix-node-2    1/1     Running   0          2m
mix-node-3    1/1     Running   0          2m
```

## 🚀 次のステップ

1. **パフォーマンステスト**
   ```bash
   docker-compose -f docker-compose.benchmark.yml up
   ```

2. **Grafanaモニタリング**
   ```bash
   docker-compose -f docker-compose.grafana.yml up -d
   # http://<VM-IP>:3000
   ```

3. **本番環境デプロイ準備**
   - TLS証明書設定
   - RBAC設定
   - リソースリミット調整

## 📞 サポート

詳細ガイド: `docs/MULTI_VM_TESTING_GUIDE.md`
Issue報告: https://github.com/SeleniaProject/NyxNet/issues
