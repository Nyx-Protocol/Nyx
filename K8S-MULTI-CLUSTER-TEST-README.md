# Nyx Multi-Cluster Kubernetes Test Framework

## 🚀 概要

このフレームワークは、1つのサーバー内で複数のKubernetesクラスター(Kind)を立ち上げ、クラスター間の相互通信をテストするための統合テストシステムです。

## ✨ 特徴

- 🎯 **複数クラスター自動セットアップ**: 3つの独立したKindクラスターを自動構築
- 🌈 **かっこいいログ出力**: カラフルな絵文字とプログレスバー付きの視覚的なログ
- ⚡ **高速テスト実行**: 並列処理による効率的なテスト実行
- 📊 **詳細なレポート**: JSON/HTML形式での美麗なテスト結果出力
- 🔗 **クラスター間通信テスト**: Pod間、DNS、ネットワーク接続の包括的なテスト

## 📋 前提条件

以下のツールがインストールされている必要があります:

- Docker
- kubectl
- kind (Kubernetes in Docker)
- bash

### インストール方法

```bash
# Docker (Windows)
winget install Docker.DockerDesktop

# kubectl
curl.exe -LO "https://dl.k8s.io/release/v1.28.0/bin/windows/amd64/kubectl.exe"

# kind
curl.exe -Lo kind-windows-amd64.exe https://kind.sigs.k8s.io/dl/v0.20.0/kind-windows-amd64
Move-Item .\kind-windows-amd64.exe c:\some-dir-in-your-PATH\kind.exe
```

## 🎯 クイックスタート

### 1. テストの実行

```bash
# WSL/Git Bash環境で実行
cd /c/Users/Aqua/Programming/SeleniaProject/NyxNet
bash scripts/k8s-multi-cluster-test.sh
```

### 2. 何が起きるか

1. **クラスター作成** - 3つのKindクラスターを並列に作成
2. **環境準備** - 各クラスターにテスト用の名前空間とリソースを作成
3. **Pod展開** - ネットワークテスト用のPodを各クラスターに展開
4. **テスト実行**:
   - Pod健全性チェック
   - DNS解決テスト
   - クラスター間ネットワーク接続テスト
5. **結果出力** - JSON/HTML形式でテスト結果を保存

## 📁 ファイル構成

```
NyxNet/
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

### エラー: "kind not found"

```bash
# kindをインストール
curl -Lo ./kind https://kind.sigs.k8s.io/dl/v0.20.0/kind-linux-amd64
chmod +x ./kind
sudo mv ./kind /usr/local/bin/kind
```

### エラー: "Docker daemon not running"

```bash
# Dockerを起動
sudo systemctl start docker
```

### ポート競合

他のサービスがポート6443-6445を使用している場合、設定ファイルのapiServerPortを変更してください。

## 🚀 パフォーマンス

- クラスター作成: ~2-3分 (並列処理)
- テスト実行: ~30-60秒
- 合計実行時間: ~3-5分

## 📄 ライセンス

このプロジェクトは、親プロジェクト(Nyx)のライセンスに従います。

## 🤝 コントリビューション

プルリクエストを歓迎します!大きな変更の場合は、まずissueを開いて変更内容を議論してください。

## 📧 サポート

問題が発生した場合は、GitHubのissueを作成してください。

---

Made with ❤️ for Nyx Network Project
