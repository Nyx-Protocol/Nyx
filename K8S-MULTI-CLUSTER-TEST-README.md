# Nyx Multi-Cluster Kubernetes Test Framework

## 🚀 概要

このフレームワークは、1つのサーバー内で複数のKubernetesクラスター(Kind)を立ち上げ、クラスター間の相互通信をテストするための統合テストシステムです。

**素のUbuntuで実行可能！** 必要な依存関係を全て自動インストールします。

## ✨ 特徴

- 🎯 **完全自動セットアップ**: Docker、kubectl、kindを自動インストール
- 🔧 **ゼロコンフィグ**: 素のUbuntuで即実行可能
- ⚡ **高速テスト実行**: 並列処理による効率的なテスト実行
- 📊 **詳細なレポート**: JSON/HTML形式での美麗なテスト結果出力
- 🔗 **クラスター間通信テスト**: Pod間、DNS、ネットワーク接続の包括的なテスト
- 🧹 **自動クリーンアップ**: テスト終了後に全リソースを自動削除

## 📋 前提条件

**必要なのはUbuntu/Debianだけ！**

- Ubuntu 20.04 LTS以降 (または Debian系Linux)
- 最低4GB RAM (推奨: 8GB以上)
- 最低10GB空きディスク容量 (推奨: 20GB以上)
- インターネット接続 (初回のみ)

その他の依存関係は**全て自動でインストール**されます！

## 🎯 クイックスタート

### 素のUbuntuでワンコマンド実行

```bash
# リポジトリをクローン（まだの場合）
git clone https://github.com/Aqua-218/NyxNet.git
cd NyxNet

# これだけで全てOK！
bash setup-and-test.sh
```

**たったこれだけです！** スクリプトが以下を全て自動で行います：

1. ✅ システム要件チェック
2. ✅ Docker自動インストール
3. ✅ kubectl自動インストール  
4. ✅ kind自動インストール
5. ✅ クラスター作成
6. ✅ テスト実行
7. ✅ レポート生成
8. ✅ クリーンアップ

### 実行例

```bash
ubuntu@server:~$ cd Nyx
ubuntu@server:~/Nyx$ bash setup-and-test.sh

════════════════════════════════════════════════════════════════════
    🚀 NYX MULTI-CLUSTER TEST - AUTO SETUP 🚀
════════════════════════════════════════════════════════════════════

✅  Detected OS: Ubuntu 22.04.3 LTS
✅  Memory: 8GB
✅  Disk space: 45GB available
✅  CPU cores: 4

📦  Installing Docker...
📦  Installing kubectl...
📦  Installing kind...
🚀  Creating cluster: nyx-cluster-1...
🚀  Creating cluster: nyx-cluster-2...
🚀  Creating cluster: nyx-cluster-3...
✅  All clusters ready!

🧪  Running tests...
✅  12/12 tests passed

📊  Report saved to: test-results/test-results-20251007-120000.html
```

### 何が起きるか

1. **システムチェック** - メモリ、ディスク、CPUを確認
2. **依存関係インストール** - Docker、kubectl、kindを自動インストール
3. **クラスター作成** - 3つのKindクラスターを並列に作成
4. **環境準備** - 各クラスターにテスト用の名前空間とリソースを作成
5. **Pod展開** - ネットワークテスト用のPodを各クラスターに展開
6. **テスト実行**:
   - Pod健全性チェック
   - DNS解決テスト
   - クラスター間ネットワーク接続テスト
7. **結果出力** - JSON/HTML形式でテスト結果を保存
8. **自動クリーンアップ** - 全クラスターを削除

## 📁 ファイル構成

```
Nyx/
├── setup-and-test.sh                 # 🚀 メインエントリーポイント（これを実行）
├── k8s-multi-cluster-config-1.yaml   # Cluster 1設定
├── k8s-multi-cluster-config-2.yaml   # Cluster 2設定
├── k8s-multi-cluster-config-3.yaml   # Cluster 3設定
├── k8s-test-manifests.yaml           # テスト用Kubernetesマニフェスト
├── scripts/
│   ├── k8s-test-logger.sh            # ログ出力ヘルパー
│   └── k8s-multi-cluster-test.sh     # メインテストスクリプト
└── test-results/                      # テスト結果出力ディレクトリ
    ├── test-results-YYYYMMDD-HHMMSS.json
    └── test-results-YYYYMMDD-HHMMSS.html
```

## 🔧 設定詳細

### クラスター構成

各クラスターは以下の構成で作成されます:

| クラスター名 | API Port | Pod Subnet | Service Subnet | NodePort範囲 |
|------------|----------|------------|----------------|-------------|
| nyx-cluster-1 | 6443 | 10.240.0.0/16 | 10.96.0.0/16 | 30080, 30443 |
| nyx-cluster-2 | 6444 | 10.241.0.0/16 | 10.97.0.0/16 | 30081, 30444 |
| nyx-cluster-3 | 6445 | 10.242.0.0/16 | 10.98.0.0/16 | 30082, 30445 |

### ノード構成

各クラスターは以下のノードで構成されます:

- 1 x Control Plane Node
- 2 x Worker Nodes

## 🧪 テスト内容

### 1. Pod健全性テスト
各クラスター内のPodが正常に起動し、コマンドを実行できることを確認

### 2. DNS解決テスト
Kubernetes内部DNSが正常に機能していることを確認

### 3. クラスター間通信テスト
Dockerネットワーク経由で、異なるクラスター間でのネットワーク接続を確認

## 📊 テスト結果

### JSON出力例

```json
{
  "timestamp": "2025-10-07T12:00:00+09:00",
  "duration_seconds": 245,
  "summary": {
    "total": 12,
    "passed": 11,
    "failed": 1,
    "success_rate": 91
  },
  "test_details": [...]
}
```

### HTML出力

美しいグラデーションとカラフルなデザインのHTMLレポートが生成されます:

- サマリーカード(総テスト数、成功、失敗、実行時間)
- 詳細なテスト結果テーブル
- レスポンシブデザイン

## 🎨 ログ出力の特徴

- 🚀 絵文字による視覚的な情報表示
- 🌈 カラフルなログレベル表示
- 📊 プログレスバー
- ⏱️ スピナーアニメーション
- 📦 美しいボックス描画

## 🛠️ カスタマイズ

### クラスター数の変更

`scripts/k8s-multi-cluster-test.sh`の以下の行を編集:

```bash
CLUSTERS=("nyx-cluster-1" "nyx-cluster-2" "nyx-cluster-3" "nyx-cluster-4")
```

対応する設定ファイルも追加してください。

### テスト内容の追加

`test_*`関数を追加することで、独自のテストを実装できます:

```bash
test_custom_feature() {
    log_section "Testing custom feature"
    
    # テストロジック
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    PASSED_TESTS=$((PASSED_TESTS + 1))
    TEST_DETAILS+=("PASS|cluster|target|description")
}
```

## 🧹 クリーンアップ

テストは自動的にクリーンアップされますが、手動でクリーンアップする場合:

```bash
# すべてのKindクラスターを削除
kind delete cluster --name nyx-cluster-1
kind delete cluster --name nyx-cluster-2
kind delete cluster --name nyx-cluster-3

# またはすべて削除
kind delete clusters --all
```

## 📝 トラブルシューティング

### 依存関係のインストールに失敗

スクリプトは自動でインストールしますが、失敗する場合：

```bash
# システムパッケージを更新
sudo apt-get update
sudo apt-get upgrade

# 再度実行
bash setup-and-test.sh
```

### Docker権限エラー

```bash
# dockerグループに追加後、ログアウト/ログインが必要な場合があります
sudo usermod -aG docker $USER
# ログアウトして再ログイン、または
newgrp docker
```

### ポート競合

他のサービスがポート6443-6445を使用している場合、設定ファイルのapiServerPortを変更してください。

### メモリ不足

最低4GB必要ですが、8GB以上推奨です。クラスター数を減らすことで対応可能：

```bash
# scripts/k8s-multi-cluster-test.sh を編集
CLUSTERS=("nyx-cluster-1" "nyx-cluster-2")  # 3→2に減らす
```

### "Too many open files" エラー

システムのファイル監視制限に達した場合、スクリプトが自動で調整しますが、手動で設定する場合：

```bash
# 一時的な対応
sudo sysctl fs.inotify.max_user_watches=524288
sudo sysctl fs.inotify.max_user_instances=512

# 永続化
echo "fs.inotify.max_user_watches=524288" | sudo tee -a /etc/sysctl.conf
echo "fs.inotify.max_user_instances=512" | sudo tee -a /etc/sysctl.conf
sudo sysctl -p
```

## 🚀 パフォーマンス

- システム制限調整: ~5秒
- 依存関係インストール: ~5-10分 (初回のみ)
- クラスター作成: ~2-3分 (並列処理)
- テスト実行: ~30-60秒
- 合計実行時間: ~3-5分 (2回目以降), ~10-15分 (初回)

## 📄 ライセンス

このプロジェクトは、親プロジェクト(Nyx)のライセンスに従います。

## 🤝 コントリビューション

プルリクエストを歓迎します!大きな変更の場合は、まずissueを開いて変更内容を議論してください。

## 📧 サポート

問題が発生した場合は、GitHubのissueを作成してください。

---

Made with ❤️ for Nyx Network Project
