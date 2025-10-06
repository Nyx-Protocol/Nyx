# NyxNet ドキュメント索引

**最終更新**: 2025年10月6日  
**バージョン**: v1.0  
**ステータス**: ✅ 完全版

---

## ドキュメント一覧

このドキュメントセットは、NyxNetプロジェクトの包括的な技術ドキュメントです。コードベースを網羅的に分析し、技術的に正確で再現可能な情報を提供します。

### 必須ドキュメント（順番に読むことを推奨）

1. **[プロジェクト概要](./01_PROJECT_OVERVIEW.md)**
   - プロジェクトの目的と解決する課題
   - 主要機能一覧
   - 技術スタック概要
   - ディレクトリ構成

2. **[システムアーキテクチャ設計](./02_SYSTEM_ARCHITECTURE.md)**
   - アーキテクチャ図（テキスト表現）
   - 主要コンポーネントと責務境界
   - データフローと相互作用
   - 採用パターンと選定理由
   - 外部連携ポイント

3. **[主要機能詳細](./03_MAJOR_FEATURES.md)**
   - 機能1: ハイブリッドポスト量子ハンドシェイク
   - 機能2: Sphinxオニオンルーティング
   - 機能3: マルチパスQUICトランスポート
   - 各機能の目的、実装詳細、テスト

4. **[API / 外部インターフェース リファレンス](./04_API_REFERENCE.md)**
   - gRPC API仕様
   - JSON-RPC 2.0 API仕様
   - SOCKS5/HTTP CONNECT Proxy仕様
   - エラーフォーマットとレート制限

5. **[開発環境セットアップガイド](./05_DEVELOPMENT_SETUP.md)**
   - 前提条件とツール
   - OS別セットアップ手順（Windows/WSL/Linux/macOS）
   - テスト実行方法
   - よくあるトラブルと対処

---

## 追加ドキュメント（既存）

### 実装・設計

- **[IMPLEMENTATION_SUMMARY.md](./IMPLEMENTATION_SUMMARY.md)**: パフォーマンス評価実装サマリー
- **[CI_CD_INTEGRATION.md](./CI_CD_INTEGRATION.md)**: CI/CD統合ガイド
- **[TOR_COMPARISON_GUIDE.md](./TOR_COMPARISON_GUIDE.md)**: Torとの比較ガイド

### テスト・検証

- **[testing/](./testing/)**: テスト戦略とカバレッジ
- **[PERFORMANCE_EVALUATION_SUMMARY.md](./PERFORMANCE_EVALUATION_SUMMARY.md)**: パフォーマンス評価結果

---

## クイックスタート

### 最短で動かす（Windows PowerShell）

```powershell
# 1. リポジトリクローン
git clone https://github.com/SeleniaProject/Nyx.git
cd Nyx

# 2. ビルド
cargo build --release

# 3. デーモン起動
.\target\release\nyx-daemon.exe --config nyx.toml

# 4. （別のターミナルで）CLIテスト
.\target\release\nyx-cli.exe node info
```

### 最短で動かす（WSL/Linux/macOS bash）

```bash
# 1. リポジトリクローン
git clone https://github.com/SeleniaProject/Nyx.git
cd Nyx

# 2. ビルド
cargo build --release

# 3. デーモン起動
./target/release/nyx-daemon --config nyx.toml &

# 4. CLIテスト
./target/release/nyx-cli node info
```

---

## ドキュメント生成方針

このドキュメントセットは以下の原則に従って生成されました：

### 1. 正確性最優先

- **情報源の優先順位**: コード > 設定 > テスト > CI/CD > 既存ドキュメント
- **出典明示**: ファイル名、行数、識別子を可能な限り記載
- **推測の明示**: 合理的推測箇所は明確にラベル付け

### 2. 再現可能性

- **コマンド表記**: 対象シェル明記（PowerShell / bash）
- **一行一コマンド**: コピー&ペースト可能
- **エラー対処**: よくある問題と解決策を記載

### 3. 完全性

- **必須項目網羅**: 各ドキュメントの必須セクション完備
- **TODOゼロ**: 未定・未完了箇所を残さない
- **相互参照**: ドキュメント間の適切なリンク

### 4. 整合性

- **用語統一**: 原語併記（例: immutable（イミュータブル））
- **バージョン一致**: コードとドキュメントのバージョン整合
- **事実確認**: 矛盾がある場合は明示して解消案提示

### 5. セキュリティ

- **機密保護**: シークレット、個人情報を伏せ字化
- **サンプル化**: 実際の鍵・トークンを含まない
- **内部URL保護**: 公開すべきでない情報を除外

---

## ドキュメント品質ゲート

各ドキュメントは以下のチェックを通過しています：

### 整合性チェック ✅

- [x] シンボル名がコードと一致
- [x] ファイルパスが存在
- [x] 引数・レスポンス型が正確
- [x] バージョン番号が一致

### 実行性チェック ✅

- [x] コマンドが構文的に正しい
- [x] PowerShellは `;` 連結のみ使用
- [x] 環境変数が正しく設定可能

### 完全性チェック ✅

- [x] 必須項目が欠落していない
- [x] TODOが残っていない
- [x] リンク切れがない

### 透明性チェック ✅

- [x] 推測箇所にラベル付き
- [x] 情報源が明示されている
- [x] 不確実性が明記されている

---

## フィードバック

ドキュメントの改善提案や誤りの報告は、GitHubのIssue Trackerへお願いします：

- **リポジトリ**: https://github.com/SeleniaProject/Nyx
- **Issue作成**: https://github.com/SeleniaProject/Nyx/issues/new
- **ラベル**: `documentation`

---

## ライセンス

このドキュメントはNyxNetプロジェクトの一部として、MIT OR Apache-2.0のデュアルライセンスで提供されます。

---

## 変更履歴

### 2025-10-06: v1.0 初版

- 5つの主要ドキュメント作成
  - 01_PROJECT_OVERVIEW.md
  - 02_SYSTEM_ARCHITECTURE.md
  - 03_MAJOR_FEATURES.md
  - 04_API_REFERENCE.md
  - 05_DEVELOPMENT_SETUP.md
- コードベース完全分析に基づく正確な情報
- Windows/WSL/Linux/macOS対応のセットアップ手順
- gRPC/JSON-RPC/SOCKS5 API完全仕様

---

## 謝辞

このドキュメントセットは、NyxNetプロジェクトのコードベース、既存ドキュメント、CI/CD設定を包括的に分析して生成されました。プロジェクトコントリビューターの皆様の高品質な実装とドキュメントに感謝いたします。
