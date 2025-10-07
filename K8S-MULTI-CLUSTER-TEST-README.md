# Nyx Multi-Cluster Kubernetes Test Framework

## 概要

1つのサーバー内で複数のKubernetesクラスター(Kind)を立ち上げ、クラスター間の相互通信とパフォーマンスをテストするためのフレームワークです。

## 特徴

- 完全自動セットアップ: Docker、kubectl、kindを自動インストール
- ゼロコンフィグ: 素のUbuntuで即実行可能
- 高速テスト実行: 並列処理による効率的なテスト実行
- 詳細なレポート: JSON/HTML形式でのテスト結果出力
- クラスター間通信テスト: レイテンシ、スループット、パケットロスの測定
- 自動クリーンアップ: テスト終了後に全リソースを自動削除

## 前提条件

- Ubuntu 20.04 LTS以降 (または Debian系Linux)
- 最低4GB RAM (推奨: 8GB以上)
- 最低10GB空きディスク容量 (推奨: 20GB以上)
- インターネット接続 (初回のみ)

その他の依存関係(Docker、kubectl、kind等)は全て自動でインストールされます。

## クイックスタート

### 基本的な実行方法

```bash
# リポジトリをクローン
git clone https://github.com/Aqua-218/NyxNet.git
cd NyxNet

# テスト実行
bash setup-and-test.sh
```

スクリプトは以下を自動で実行します:

1. システム要件チェック
2. Docker自動インストール
3. kubectl自動インストール
4. kind自動インストール
5. 3つのKubernetesクラスター作成
6. テストPod展開
7. 通信テスト実行
8. レポート生成
9. クリーンアップ

### 実行の流れ

1. システムチェック - メモリ、ディスク、CPUを確認
2. システム制限調整 - inotify、ファイルディスクリプタ制限を最適化
3. 依存関係インストール - Docker、kubectl、kindを自動インストール
4. クラスター作成 - 3つのKindクラスターを並列に作成
5. 環境準備 - 各クラスターにテスト用の名前空間とリソースを作成
6. Pod展開 - ネットワークテスト用のPod(netshoot + iperf3)を各クラスターに展開
7. テスト実行:
   - Pod健全性チェック
   - DNS解決テスト
   - クラスター間ネットワーク接続テスト (レイテンシ・パケットロス測定)
   - スループット測定 (iperf3による実速度計測)
8. 結果出力 - JSON/HTML形式でテスト結果を保存
9. 自動クリーンアップ - 全クラスターを削除

## ファイル構成

```
Nyx/
├── setup-and-test.sh                 # メインエントリーポイント
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

## 設定詳細

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

## テスト内容

### 1. Pod健全性テスト
各クラスター内のPodが正常に起動し、コマンドを実行できることを確認します。

### 2. DNS解決テスト
Kubernetes内部DNSが正常に機能していることを確認します。

### 3. クラスター間通信テスト
Dockerネットワーク経由で、異なるクラスター間でのネットワーク接続を確認します。
- レイテンシ測定: 10回のpingで平均レイテンシを計測
- パケットロス: パケット損失率を測定
- 結果例: Latency: 0.234ms | Loss: 0%

### 4. スループット測定テスト
iperf3を使用してクラスター間の実際の通信速度を測定します。
- 送信速度: Mbits/sec単位で測定
- 再送信回数: TCP再送信の回数
- 測定時間: 各接続で5秒間
- 結果例: Throughput: 2847.53 Mbits/sec | Retransmits: 0

## テスト結果

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

HTMLレポートが生成されます:

- サマリーカード(総テスト数、成功、失敗、実行時間)
- 詳細なテスト結果テーブル
- レスポンシブデザイン

## カスタマイズ

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

## 手動クリーンアップ

テストは自動的にクリーンアップされますが、手動でクリーンアップする場合:

```bash
# すべてのKindクラスターを削除
kind delete cluster --name nyx-cluster-1
kind delete cluster --name nyx-cluster-2
kind delete cluster --name nyx-cluster-3

# またはすべて削除
kind delete clusters --all
```

## トラブルシューティング

### 重要: 失敗時の対処方法

**テストが失敗した場合や、途中でエラーが発生した場合は、以下の手順を実行してください:**

```bash
# 1. プロジェクトディレクトリを完全に削除
cd ~
rm -rf NyxNet

# 2. 再度クローンしてやり直す
git clone https://github.com/Aqua-218/NyxNet.git
cd NyxNet
bash setup-and-test.sh
```

この方法により、中途半端な状態や残存リソースによる問題を回避できます。

### Docker/Kubernetesインストール後の再起動

DockerやKubernetesのインストール後、システムから再起動を求められる場合があります。

**再起動が必要な場合の手順:**

```bash
# 1. システムを再起動
sudo reboot

# 2. 再起動後、プロジェクトディレクトリを削除
cd ~
rm -rf NyxNet

# 3. 再度クローンして実行
git clone https://github.com/Aqua-218/NyxNet.git
cd NyxNet
bash setup-and-test.sh
```

再起動後は必ずクリーンな状態から始めることを推奨します。

### その他のエラー

#### 依存関係のインストールに失敗

```bash
# システムパッケージを更新
sudo apt-get update
sudo apt-get upgrade

# プロジェクトを削除して再クローン
cd ~
rm -rf NyxNet
git clone https://github.com/Aqua-218/NyxNet.git
cd NyxNet
bash setup-and-test.sh
```

#### Docker権限エラー

```bash
# dockerグループに追加後、ログアウト/ログインが必要な場合があります
sudo usermod -aG docker $USER
# ログアウトして再ログイン、または
newgrp docker
```

#### ポート競合

他のサービスがポート6443-6445を使用している場合、設定ファイルのapiServerPortを変更してください。

#### メモリ不足

最低4GB必要ですが、8GB以上推奨です。クラスター数を減らすことで対応可能：

```bash
# scripts/k8s-multi-cluster-test.sh を編集
CLUSTERS=("nyx-cluster-1" "nyx-cluster-2")  # 3→2に減らす
```

#### "Too many open files" エラー

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

## パフォーマンス目安

- システム制限調整: 約5秒
- 依存関係インストール: 約5-10分 (初回のみ)
- クラスター作成: 約2-3分 (並列処理)
- テスト実行: 約30-60秒
- 合計実行時間: 約3-5分 (2回目以降), 約10-15分 (初回)

## 注意事項

- このフレームワークは動作確認用のテストツールです
- 本番環境での使用は想定していません
- テスト実行後はリソースが自動的にクリーンアップされます
- 問題が発生した場合は、プロジェクトディレクトリを削除して再クローンすることを推奨します

## ライセンス

このプロジェクトは、親プロジェクト(Nyx)のライセンスに従います。
