# NyxNet Presentations

This directory contains presentation materials for NyxNet.

## Contents

- `slides.md` - Main presentation slides
- `slides_3min.md` - Short 3-minute presentation version

## Setup

```bash
cd presentation
npm install
```

## Development

Start the development server:

```bash
npm run dev
```

For the 3-minute version:

```bash
npx slidev slides_3min.md
```

The presentation will open in your browser at `http://localhost:3030`.

## Build

Build for production:

```bash
npm run build
```

Static files will be generated in the `dist/` directory.

## Export to PDF

```bash
npm run export
```

This will generate `slides-export.pdf`.

## Keyboard Shortcuts

- `Space` / `→`: Next slide
- `←`: Previous slide
- `f`: Fullscreen
- `o`: Slides overview
- `d`: Toggle dark mode
- `g`: Grid view

## Features

- **Mermaid Diagrams**: System architecture and sequence diagrams
- **Code Highlighting**: Syntax highlighting with Shiki
- **Animations**: Step-by-step display with v-clicks
- **Math Rendering**: Formula rendering with KaTeX
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

