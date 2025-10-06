# TLA+ 検証セットアップガイド

## 必要なツール

### 1. TLA+ Toolbox (推奨)
TLA+ Toolboxは完全な統合開発環境です:
- **ダウンロード**: https://github.com/tlaplus/tlaplus/releases
- **インストール**: `TLAToolbox-1.7.1-win32.win32.x86_64.zip` をダウンロードして解凍
- **使用方法**: Toolboxを起動してspecificationを開く

### 2. コマンドラインTLC
スタンドアロンのTLCツール:
```bash
# tla2tools.jarをダウンロード
curl -LO https://github.com/tlaplus/tlaplus/releases/download/v1.7.1/tla2tools.jar

# 検証実行
java -jar tla2tools.jar tlc2.TLC NyxBasicVerification -config NyxBasicVerification.cfg
```

## 現在作成済みのTLA+モジュール

### 検証可能な基本モジュール
1. **NyxBasicVerification.tla** (簡易版)
   - 3ノード、2ストリーム、5メッセージまで
   - TypeInvariant: 型の正当性
   - NoMessageDuplication: メッセージ重複なし
   - MessageOrdering: メッセージ順序保証
   - NoDeadlock: デッドロックなし

### コア機能モジュール (詳細版)
2. **NyxCryptography.cfg**
   - CryptoSpec: 暗号化プロトコル
   - 検証項目: Forward Secrecy, Post-Compromise Security

3. **NyxNetworkLayer.cfg**
   - NetworkSpec: ネットワーク層
   - 検証項目: Eventual Delivery, Bounded Latency, Packet Ordering

4. **NyxStreamManagement.cfg**
   - StreamSpec: ストリーム管理
   - 検証項目: Deadlock Freedom, Fair Scheduling, Backpressure

### 高度なモジュール (32モジュール総計20,106行)
- NyxFaultTolerance: 障害検出と回復
- NyxQoSManagement: QoS保証
- NyxDistributedConsensus: Paxos/Raft/PBFT
- NyxSecurityAudit: セキュリティ監査
- NyxNFVAndSDN: NFV/SDN統合
- NyxEdgeComputing: エッジコンピューティング
- NyxTimeSensitiveNetworking: TSN (IEEE 802.1)
- その他25モジュール...

## 検証手順

### ステップ1: TLA+ Toolboxのセットアップ
```powershell
# ダウンロードディレクトリに移動
cd ~/Downloads

# 最新版をダウンロード
Invoke-WebRequest -Uri "https://github.com/tlaplus/tlaplus/releases/download/v1.7.1/TLAToolbox-1.7.1-win32.win32.x86_64.zip" -OutFile "TLAToolbox.zip"

# 解凍
Expand-Archive -Path TLAToolbox.zip -DestinationPath "C:\TLAToolbox"

# toolbox.exeを起動
Start-Process "C:\TLAToolbox\toolbox\toolbox.exe"
```

### ステップ2: Specificationの作成
1. Toolboxで新しいSpecificationを作成
2. `NyxBasicVerification.tla` を追加
3. Model Checkerの設定:
   - Constants: Nodes = {n1, n2, n3}, MaxMessages = 5, MaxStreamId = 2
   - Invariants: TypeInvariant, NoMessageDuplication, MessageOrdering
   - Properties: NoDeadlock

### ステップ3: TLCモデルチェック実行
```bash
# Toolbox経由 (推奨)
Toolbox → TLC Model Checker → Run TLC on Model

# コマンドライン (tla2tools.jar必要)
java -jar tla2tools.jar tlc2.TLC NyxBasicVerification -config NyxBasicVerification.cfg -workers 4 -deadlock
```

### ステップ4: 結果の確認
TLCは以下を報告:
- **States explored**: 探索した状態数
- **Distinct states**: 異なる状態数
- **State graph depth**: 状態グラフの深さ
- **Invariant violations**: 不変条件違反
- **Deadlocks**: デッドロック検出
- **Property violations**: 性質違反

## 検証レベル

### レベル1: 基本検証 (NyxBasicVerification)
- **状態数**: ~1000-10000
- **実行時間**: 数秒~数分
- **目的**: 基本的な型安全性とメッセージ配送

### レベル2: コア機能検証
- **状態数**: ~10000-100000
- **実行時間**: 数分~数十分
- **目的**: 暗号化、ネットワーク、ストリーム管理

### レベル3: 統合検証 (NyxComprehensiveVerification)
- **状態数**: ~100000-1000000+
- **実行時間**: 数時間~数日
- **目的**: エンドツーエンドのプロトコル検証

## トラブルシューティング

### メモリ不足
```bash
# JVMヒープサイズを増やす
java -Xmx8g -jar tla2tools.jar tlc2.TLC ...
```

### 状態空間爆発
```
# 定数を小さくする
MaxNodes = 3 → 2
MaxMessages = 10 → 5

# Symmetryを活用
SYMMETRY Permutations(Nodes)
```

### デッドロック誤検出
```
# -deadlockフラグで明示的にチェック
java -jar tla2tools.jar tlc2.TLC ... -deadlock
```

## 次のステップ

1. **TLA+ Toolboxをインストール**して基本検証を実行
2. **NyxBasicVerification**で基本的な正当性を確認
3. **コアモジュール**の検証に進む
4. **統合検証**で全体の整合性を確認
5. **TLAPS**で形式証明を実施 (NyxMasterProofs.tla)

## 検証の期待結果

### 成功例
```
TLC2 Version 2.16
Running in TLC mode
Starting... (2024-XX-XX XX:XX:XX)
Computing initial states...
Finished computing initial states: 1 distinct state generated.
Progress(10) at 2024-XX-XX XX:XX:XX: 1234 states generated, 987 distinct states.
Model checking completed. No error has been found.
  States generated: 5432
  Distinct states: 3456
  State graph depth: 15
Finished in 12s at 2024-XX-XX XX:XX:XX
```

### エラー例
```
Error: Invariant TypeInvariant is violated.
The behavior up to this point is:
State 1: <Initial predicate>
/\ messages = {}
/\ received = {}
...
State 5: <Action SendMessage line 123>
/\ messages = {[id |-> 1, source |-> n1, ...]}
...
```

この場合、State 5でTypeInvariantが破られているため、
SendMessageアクションを修正する必要があります。

## 参考資料

- TLA+ ホームページ: https://lamport.azurewebsites.net/tla/tla.html
- TLA+ GitHubリポジトリ: https://github.com/tlaplus/tlaplus
- Learn TLA+: https://learntla.com/
- TLA+ Examples: https://github.com/tlaplus/Examples
