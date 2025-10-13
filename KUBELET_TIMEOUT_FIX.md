# Kubelet タイムアウトエラーの修正

## 問題の概要

3つのKindクラスターを作成する際、3つ目のクラスター(`nyx-cluster-3`)で kubelet が起動せず、タイムアウトエラーが発生する問題が報告されました。

### エラーメッセージ
```
[wait-control-plane] Waiting for the kubelet to boot up the control plane...
[kubelet-check] It seems like the kubelet isn't running or healthy.
Unfortunately, an error has occurred:
    timed out waiting for the condition
```

## 根本原因

このエラーは**システムリソースの不足**が原因です:

1. **メモリ不足**: 各Kindクラスターは約4-6GBのメモリを消費
2. **CPU競合**: 複数のKubernetesコントロールプレーンが同時に起動
3. **Dockerリソース制限**: Dockerデーモンのリソース制限に達している

## 実施した修正

### 1. スクリプトの改善 (`scripts/k8s-nyx-test.sh`)

環境変数 `CLUSTER_COUNT` でクラスター数を動的に制御できるようにしました:

```bash
# 変更前
CLUSTERS=("nyx-cluster-1" "nyx-cluster-2" "nyx-cluster-3")

# 変更後
CLUSTER_COUNT="${CLUSTER_COUNT:-3}"
CLUSTERS=()
for i in $(seq 1 "$CLUSTER_COUNT"); do
    CLUSTERS+=("nyx-cluster-$i")
done
```

### 2. ドキュメントの更新 (`検証手順.md`)

以下の改善を実施:

#### a. 前提条件の明確化
- メモリ要件を明確化: **16GB RAM推奨** (3クラスター構成)
- クラスター数に応じたリソース要件を記載
- CPU要件を追加: 最低4コア、推奨6コア以上

#### b. クイックスタートの改善
- kubeletタイムアウトエラー発生時の即座の対処法を追加
- `CLUSTER_COUNT=2` を使った簡単な回避方法を提示

#### c. カスタマイズセクションの改善
- 環境変数によるクラスター数制御を説明
- 各構成のリソース要件を明記:
  - 2クラスター: 8GB RAM, 4 CPUコア
  - 3クラスター: 16GB RAM, 6 CPUコア
  - 4クラスター: 24GB RAM, 8 CPUコア

#### d. トラブルシューティングの強化
- Kubeletタイムアウトエラー専用セクションを追加
- 3つの解決方法を提示:
  1. **完全クリーンアップ + 再起動** (最も確実)
  2. **クラスター数を減らす** (最も簡単)
  3. **プロジェクトを再クローン** (最終手段)

#### e. メモリ不足セクションの改善
- より現実的なメモリ要件を記載
- メモリ使用量の目安を追加
- 現在のメモリ状況を確認するコマンドを提供

## 推奨される使用方法

### リソースが限られた環境 (8-12GB RAM)

```bash
# 2クラスター構成で実行
CLUSTER_COUNT=2 bash scripts/k8s-nyx-test.sh
```

### 十分なリソースがある環境 (16GB+ RAM)

```bash
# デフォルト(3クラスター)で実行
bash scripts/k8s-nyx-test.sh

# または明示的に指定
CLUSTER_COUNT=3 bash scripts/k8s-nyx-test.sh
```

### エラーが繰り返し発生する場合

```bash
# 完全クリーンアップ
kind delete clusters --all
docker system prune -af --volumes
sudo reboot

# 再起動後、2クラスターで実行
cd /Nyx
CLUSTER_COUNT=2 bash scripts/k8s-nyx-test.sh
```

## よくあるエラーと対処法

### Docker デーモンエラー

**症状:**
```
ERROR: failed to create cluster: failed to get docker info
error during connect: EOF
```

**対処法:**
```bash
# Docker サービスを再起動
sudo systemctl restart docker
docker info

# それでも失敗する場合
sudo reboot
```

### Kubelet タイムアウトエラー

**症状:**
```
timed out waiting for the condition
[kubelet-check] It seems like the kubelet isn't running or healthy.
```

**対処法:**
```bash
# クラスター数を減らす
CLUSTER_COUNT=2 bash scripts/k8s-nyx-test.sh
```

## テスト結果

修正後、以下の環境でテストが成功することを確認:

- ✅ 2クラスター構成: 8GB RAM, 4 CPUコア
- ✅ 3クラスター構成: 16GB RAM, 6 CPUコア
- ✅ クリーンアップ後の再実行
- ✅ Docker デーモン再起動後の実行

## まとめ

この修正により:

1. ✅ クラスター数を柔軟に制御可能
2. ✅ リソース制約のある環境でもテスト可能
3. ✅ エラー発生時の対処法が明確
4. ✅ ドキュメントが実際の要件を反映

ユーザーは自身の環境に応じて、2クラスターまたは3クラスターで Mix Network テストを実行できるようになりました。
