# NyxNet Presentation for U-22 Programming Contest

U-22プログラミングコンテスト用のNyxNetプレゼンテーションスライドです。

## Setup

```bash
cd presentation
npm install
```

## Development

```bash
npm run dev
```

ブラウザで `http://localhost:3030` が開きます。

## Build

```bash
npm run build
```

静的サイトが `dist/` に生成されます。

## Export to PDF

```bash
npm run export
```

`slides-export.pdf` が生成されます。

## Keyboard Shortcuts

- `Space` / `→`: 次のスライド
- `←`: 前のスライド
- `f`: フルスクリーン
- `o`: スライド一覧
- `d`: ダークモード切り替え
- `g`: グリッド表示

## Features

- **Mermaid図**: システム構成図やシーケンス図を含む
- **コードハイライト**: Shikiによるシンタックスハイライト
- **アニメーション**: v-clicksでステップバイステップ表示
- **数式表示**: KaTeXによる数式レンダリング
- **レスポンシブ**: 様々な画面サイズに対応

## スライド構成

1. タイトル
2. Why NyxNet? - 問題提起
3. NyxNetとは - 3つの核心技術
4. System Architecture - システム構成図
5. 工夫した点① - ハイブリッド量子耐性暗号
6. 工夫した点② - Sphinxオニオンルーティング
7. 工夫した点③ - マルチパスQUICトランスポート
8. Performance Comparison - パフォーマンス比較
9. Technology Stack - 技術スタック
10. 実装完成度 - Feature Matrix
11. Use Cases - ユースケース
12. Demo Screenshots - デモ画面
13. 競合比較
14. 開発で得た学び
15. 今後の展望
16. まとめ
17. 最終スライド

## 注意事項

- パフォーマンス数値は実測値と推定値を明確に区別
- 「295倍」などの非現実的な数値は使用していません
- Torとの比較は公正な条件で実測・推定

## Customization

`slides.md` を編集してスライドをカスタマイズできます。

- テーマ: `theme: default`（他のテーマも利用可能）
- 背景画像: Unsplashの高品質画像を使用
- レイアウト: center, two-cols, defaultなど

