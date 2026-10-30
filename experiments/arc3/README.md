# ARC実験と原始の形式化の接続

公開ゲームの位置づけは **Public Demo（形式・基本的な仕組みの例示）**です。
公開25本も本番の未知環境を代表する評価集合とは扱いません。
以下の既知3本の結果は接続・回帰確認です。`hybrid` のゲームID別の切替は
例示上の診断用に残し、未知環境向けの汎用方策の改善として採用しません。
汎化性能の確認は、方策を固定して競技の未知環境で測る段階に分けます。
出典: [公式技術報告 Table 1 / Section 3.6](https://arcprize.org/media/ARC_AGI_3_Technical_Report.pdf)。

**配布版0.1.1の使い方は [QUICKSTART.md](QUICKSTART.md) を参照してください。**
ft09 の seed 0・2・4 の RESET 後の停止については、
[原因・接続側の修正・回帰検査と再実行](FT09_REGRESSION.md) を参照してください。
`run.py` の既定エージェントは公開の既存探索器 `explore` です。

`core.py` の有限モデル用 `solve` と証明書の `verify` は、深い方策でも
Python の再帰上限に依存せず走査します。探索順序・予算・`max_nodes` の
意味は従来どおりです。これは公開ゲーム上の成績改善を示すものではありません。

既存のLeanライブラリを原本として参照し、操作・観測を記号として学ぶ試作と、
以前の観測グラフ型エージェントを同じ評価器から実行できるようにした実験です。
原始の形式化の定理をARCに無条件で適用したものではありません。

[公開の既存エージェントの調査・接続](EXISTING_AGENTS.md)も参照してください。
MITライセンスの既存探索器を `--agents explore` として追加しました。
公開3ゲームの同じseed・上限で0・0・2レベル突破、共通検証164テスト合格です。
既存探索器のソース、出典ハッシュ、ライセンス、接続時の変更を記録しています。

## 接続したもの

- `theorems475/index.json`: 原本61ソースの公開定理214＋251＋10＝475本の宣言索引。
  各項目は既存ファイルへのパス・行番号・固定コミット・Git blob SHAを持ちます。
  後に追加された19定理をこの475件の索引に含めていません。
- `core.py`, `learner.py`: 有限候補モデルの全継続同値・履歴整合性・共通方策探索、
  観測列からの有界有限機械の列挙。有限性などの条件は各モジュールに明記しています。
- `trace_structure.py`, `online.py`: 意味づけ前の記録と経験的な履歴モデル。
  複数の結果が出たら最大4操作まで履歴を増やし、全経験を再集計します。
- `arc_agent.py`: SDKの合法操作、画面、リセット、外部の進捗・終了信号との接続。
- `runtime/arc3`: 以前の観測グラフ型モデル、ランダム版、構造版に共通のSDK評価器。
- `affine_belief.py`, `parity_probe.py`: 条件を指定したGF(2)信念と観測・復元の別実験。
  これらの線形性・可逆性をARC全体に仮定していません。

`LinearInputObservation` の定理には任意の型・関数で述べられた部分があります。
例えば `F_u=A-uX` を同じ状態で測れるなら、異なる二入力から `(A,X)` を復元できます。
しかし、この入力形を実際のARCから発見する部分は未実装です。
現在のオンライン学習器は475定理を自動適用する証明探索器ではありません。
有限回の一致を全継続同値と認定することもありません。

## 共通入口

GitHub Actionsでの通常検証と、Kaggle公開環境を使ったseed比較は [ACTIONS.md](ACTIONS.md) を参照してください。

リポジトリ直下で、Python 3.12の仮想環境を使って実行します。

```bash
python -m pip install -r experiments/arc3/runtime/requirements.lock
python -X utf8 tools/verify.py --arc3-only
python experiments/arc3/run.py --help
```

`--arc3-only` は原本61ソースのblob照合と研究コア・旧SDK実装のテストを行います。
結果は `experiments/arc3/reports/integration-check.json` に記録します。
Lean再ビルドや公理監査、ゲーム評価は実行しません。
従来のLean検査は `python -X utf8 tools/verify.py --proof-only` です。

公開ゲームの環境ファイルは別途必要です。既存のファイルを指定して3方式を比較します。

```bash
python experiments/arc3/run.py --agents model structure random --games ls20 ft09 vc33 --seeds 3 --budget 500 --environments /path/to/environment_files --output experiments/arc3/runs/comparison
```

`--output` は未作成のディレクトリを指定します。座標操作の構造版は全画素から一様に候補を抽出し、
物体分割・色の役割・移動方向・カウンタ除去を使いません。旧モデルには別の前提があります。
構造版では勝敗・進捗を接続部から数値評価として渡します。
これらの前提と探索ヒューリスティクスは証明された数学的帰結とは別です。

## 実行結果の範囲

`reports/summary.json` と `reports/metadata.json` は統合前に行った構造版・ランダム版の
公開3ゲーム、seed=3、最大500呼び出し、追加リセット最大8回の測定です。
全ゲームで突破レベル0、完全クリア0でした。構造版の反復予測は20・255・189回で一致しましたが、
探索成功や未知場面への一般化を示していません。履歴の細分化はこの3試行では発生していません。
無変化の画面も予測の一致に含みます。公式提出や隠れゲームの成績ではありません。
統合後の再実行結果は別の `runs/` に保存します。

今回の統合後の比較を `reports/integrated-summary.json` と
`reports/integrated-metadata.json` に保存しました。同じseed・上限で旧モデルは3ゲームとも
1レベル突破、構造版とランダム版は3ゲームとも0でした。完全クリアはいずれも0です。
`reports/integration-20261027.json` は共通検証入口での156テスト合格と原本blob照合の記録です。
統合による成績向上を示した結果ではなく、旧モデルの挙動を保った接続確認です。

475定理の元のLean検査実績はリポジトリ本体の検証記録を参照してください。
今回の実験テスト合格をLean証明やARC攻略の成功とは数えません。

## 参照

- [統合本文](../../原始の形式化.md)
- [既存の検証と再実行](../../検証と再実行.md)
- [作業方針](../../AGENTS.md)
