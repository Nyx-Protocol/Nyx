# TLA+ Verification in CI/CD

このドキュメントでは、NyxNetプロジェクトにおけるTLA+形式検証のCI/CD統合について説明します。

## 概要

NyxNetは、GitHub Actionsを使用してTLA+形式検証を自動化しています。これにより、プロトコルの正当性とシステムの安全性を継続的に検証できます。

## ワークフロー構成

### 1. トリガー条件

検証ワークフローは以下の条件でトリガーされます:

- **Push/PR**: `formal/` ディレクトリの変更時
- **スケジュール**: 毎週月曜日 02:00 UTC
- **手動実行**: workflow_dispatch (必要に応じて)

### 2. 検証レベル

#### Quick Check (高速検証)
- **実行タイミング**: すべてのPR、mainブランチへのpush
- **検証対象**: コアモジュール (3-5個)
- **所要時間**: 約5-10分
- **目的**: 迅速なフィードバック

実行されるモジュール:
- `NyxBasicVerification` - 基本プロトコル
- `NyxCryptography` - 暗号化機能
- `NyxNetworkLayer` - ネットワーク層

#### Full Verification (完全検証)
- **実行タイミング**: 週次スケジュール、または手動実行
- **検証対象**: すべてのTLA+モジュール (11+個)
- **所要時間**: 約60-90分
- **目的**: 包括的な正当性確認

検証されるすべてのモジュール:
- `NyxBasicVerification`
- `NyxCryptography`
- `NyxNetworkLayer`
- `NyxFaultTolerance`
- `NyxQoSManagement`
- `NyxDistributedConsensus`
- `NyxEdgeComputing`
- `NyxTimeSensitiveNetworking`
- `NyxSecurityAudit`
- `NyxNFVAndSDN`
- `NyxConfigurationValidation`

### 3. 検証プロパティ

各モジュールで以下のプロパティが検証されます:

#### Safety Properties (安全性)
- **TypeInvariant**: 型の整合性
- **NoDeadlock**: デッドロックの不在
- **StateConsistency**: 状態の整合性
- **ProtocolCorrectness**: プロトコルの正当性

#### Liveness Properties (活性)
- **EventualProgress**: 最終的な進行
- **Termination**: 適切な終了
- **FairExecution**: 公平な実行

## 実装詳細

### ワークフローステップ

1. **環境セットアップ**
   ```yaml
   - Java 17 (Temurin distribution)
   - Python 3.11
   - TLA+ Tools v1.8.0
   ```

2. **TLA+ツールのキャッシング**
   - `tla2tools.jar` をキャッシュして高速化
   - キーは `tla-tools-v1.8.0`
   - 検証も実施して正常性を確認

3. **検証実行**
   - Quick: `quick_verify.sh` スクリプト使用
   - Full: `final_verification.sh` スクリプト使用
   - タイムアウト設定: 各モジュール最大300秒

4. **結果収集**
   - ログファイル生成
   - JSON サマリー作成
   - Artifacts として保存

5. **結果通知**
   - GitHub Step Summary に表示
   - PRへのコメント投稿
   - バッジ更新

### ディレクトリ構造

```
formal/
├── *.tla                      # TLA+ 仕様ファイル
├── *.cfg                      # TLC 設定ファイル
├── tla2tools.jar             # TLA+ ツール (キャッシュ)
├── quick_verify.sh           # 高速検証スクリプト
├── final_verification.sh     # 完全検証スクリプト
├── verification_logs/        # 検証ログ
│   ├── NyxBasicVerification.log
│   ├── NyxCryptography.log
│   └── ...
└── states/                   # TLC 状態ファイル
```

## 検証結果の確認

### GitHub Actions UI

1. **Actions タブ** → **Formal Verification (TLA+)** を選択
2. 実行履歴から確認したい実行をクリック
3. **Summary** タブで概要を確認
4. **Jobs** で詳細ログを確認

### Artifacts

各実行で以下のArtifactsが生成されます:

- `tla-quick-results`: 高速検証の結果
  - `tla_verification_quick.log`
  - `tla_verification_quick.json`
  - 検証ログファイル群

- `tla-full-results`: 完全検証の結果
  - `tla_verification_full.log`
  - `tla_verification_full.json`
  - すべての検証ログ
  - 検証レポート (Markdown)

### PRコメント

プルリクエストには自動的にコメントが投稿されます:

```
## 🔍 Formal Verification Results

| Component | Status |
|-----------|--------|
| TLA+ Quick Check | success |
| Rust Conformance | success |
| Spec Validation | success |

### TLA+ Verification
- ✅ Passed: 3
- ❌ Failed: 0

✅ **All formal verification checks passed!**
```

## ローカル実行

CI/CDと同じ検証をローカルで実行できます:

### 前提条件
```bash
# Java 17+ がインストールされていること
java -version

# TLA+ ツールのダウンロード
cd formal
curl -L -o tla2tools.jar \
  https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
```

### 高速検証
```bash
cd formal
chmod +x quick_verify.sh
./quick_verify.sh
```

### 完全検証
```bash
cd formal
chmod +x final_verification.sh
./final_verification.sh
```

### 個別モジュール検証
```bash
cd formal
java -Xmx2G -cp tla2tools.jar tlc2.TLC \
  -workers 2 -deadlock \
  -config NyxBasicVerification.cfg \
  NyxBasicVerification.tla
```

## トラブルシューティング

### よくある問題

#### 1. タイムアウトエラー
```
Error: The operation was canceled.
```

**解決策**:
- モジュールの複雑さを確認
- タイムアウト値を増やす
- モデルのパラメータを調整

#### 2. メモリ不足
```
OutOfMemoryError: Java heap space
```

**解決策**:
- Java ヒープサイズを増やす: `-Xmx4G` または `-Xmx8G`
- 探索深度を制限: `-depth 20`

#### 3. Invariant違反
```
Invariant TypeInvariant is violated
```

**解決策**:
- 生成された counterexample を確認
- `verification_logs/` のログファイルを詳細に調査
- TLA+ 仕様を修正して再実行

#### 4. TLA+ツールがダウンロードできない
```
curl: (7) Failed to connect
```

**解決策**:
- ネットワーク接続を確認
- プロキシ設定を確認
- 別のミラーから手動ダウンロード

## パフォーマンス最適化

### ワーカー数の調整
```bash
# CPU コア数に応じて調整
java -cp tla2tools.jar tlc2.TLC -workers auto ...
# または明示的に指定
java -cp tla2tools.jar tlc2.TLC -workers 4 ...
```

### メモリ割り当て
```bash
# 小規模モデル
-Xmx2G

# 中規模モデル
-Xmx4G

# 大規模モデル
-Xmx8G
```

### 探索深度の制限
```bash
# 高速検証用
-depth 20

# 通常検証用
-depth 50

# 完全検証用
-depth 100
```

## ベストプラクティス

### 1. 段階的な検証
1. まず `quick_verify.sh` でコアモジュールを検証
2. 成功したら `final_verification.sh` で全体を検証
3. 問題があれば個別モジュールを詳細に調査

### 2. TLA+仕様の変更時
1. 構文チェックを実行
2. Basic モジュールで動作確認
3. Quick 検証でコアモジュールを確認
4. Full 検証で全体を確認
5. PRを作成してCI/CD実行

### 3. 定期的なメンテナンス
- 週次の完全検証結果を確認
- タイムアウトやメモリ使用量の傾向を監視
- 新しいモジュール追加時は検証スクリプトを更新

## 今後の改善予定

- [ ] カバレッジレポートの自動生成
- [ ] 検証時間のベンチマーク追跡
- [ ] Counterexampleの自動分析と修正提案
- [ ] TLA+ Proofの統合 (TLAPS)
- [ ] 並列実行による高速化
- [ ] カスタム検証プロファイルの追加

## 参考資料

- [TLA+ 公式サイト](https://lamport.azurewebsites.net/tla/tla.html)
- [TLC Model Checker ドキュメント](https://lamport.azurewebsites.net/tla/tlc.html)
- [GitHub Actions ドキュメント](https://docs.github.com/en/actions)
- [NyxNet Formal Verification README](../formal/README.md)
- [検証手順書](../検証手順.md)

## サポート

質問や問題がある場合:
- GitHub Issues で報告
- Discussions で質問
- SUPPORT.md を参照
