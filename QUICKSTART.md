# Nyx Multi-Cluster Test - Quick Reference

## ワンコマンド実行

```bash
bash setup-and-test.sh
```

これだけで以下が全て自動実行されます：

## 実行内容

### 1️⃣ システムチェック
- メモリ、CPU、ディスク容量の確認
- OS互換性チェック

### 2️⃣ 依存関係の自動インストール
- ✅ Docker CE (最新安定版)
- ✅ kubectl v1.28.0
- ✅ kind v0.20.0
- ✅ 必要なシステムパッケージ

### 3️⃣ クラスター構築
3つの独立したKindクラスターを作成：
- `nyx-cluster-1` (API: 6443, Pods: 10.240.0.0/16)
- `nyx-cluster-2` (API: 6444, Pods: 10.241.0.0/16)
- `nyx-cluster-3` (API: 6445, Pods: 10.242.0.0/16)

各クラスター: 1 control-plane + 2 workers

### 4️⃣ テスト実行
- ✅ Pod健全性テスト (各クラスター)
- ✅ DNS解決テスト (各クラスター)
- ✅ クラスター間ネットワーク接続テスト (全組み合わせ)

### 5️⃣ レポート生成
- `test-results/test-results-TIMESTAMP.json` - 詳細データ
- `test-results/test-results-TIMESTAMP.html` - 美しいHTMLレポート

### 6️⃣ 自動クリーンアップ
テスト完了後、全クラスターを自動削除

## 所要時間

- 初回実行（依存関係インストール含む）: 約10-15分
- 2回目以降: 約3-5分

## システム要件

| 項目 | 最低 | 推奨 |
|------|------|------|
| RAM | 4GB | 8GB+ |
| Disk | 10GB | 20GB+ |
| CPU | 2コア | 4コア+ |

## よくある質問

**Q: rootで実行する必要がありますか？**
A: いいえ。通常ユーザーで実行してください。必要に応じてsudoパスワードを聞かれます。

**Q: 既にDockerがインストールされている場合は？**
A: スキップされます。既存のインストールを使用します。

**Q: クラスターは残りますか？**
A: いいえ。テスト終了後に自動削除されます。

**Q: WSLで動きますか？**
A: はい、WSL2のUbuntuで問題なく動作します。

**Q: 途中で止めたい場合は？**
A: Ctrl+C で停止。クリーンアップは自動で実行されます。

## 手動実行（上級者向け）

個別にスクリプトを実行したい場合：

```bash
# 依存関係のみインストール
bash scripts/k8s-multi-cluster-test.sh --install-only

# テストのみ実行（依存関係は既にある前提）
bash scripts/k8s-multi-cluster-test.sh

# クリーンアップのみ
kind delete clusters --all
```

## サポート

問題が発生した場合：
1. `setup-and-test.sh` を再実行してみてください
2. それでも解決しない場合は、GitHubでissueを作成してください
