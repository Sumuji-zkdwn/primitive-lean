# 曲線文字追補の検証 — 2026-11-10

実装コミット `be2d206881527eb21fcb62d58323225b2d930ebe` に対し、`python -B -X utf8 tools/verify.py --integration-only` の **26段階すべてが成功**した。開始時の作業ツリーはクリーン。機械可読の結果・ソースSHA-256・各新規宣言の公理は [validation.json](validation.json)、宣言一覧と原文の来歴は [provenance.json](../../sources/curve_word_chain_20261110/provenance.json) にある。

## 今回確認したこと

- 新規 `CurveWordAlgebra.inc` は32定理・47宣言、`CurveWordFinite.inc` は23定理・34宣言。合計 **55定理・81宣言**。
- 共通結合検査は **3466定理・4698宣言**。これは共通検査の件数で、独立モジュールを含むリポジトリ全体の総数ではない。
- `--trust=0` でコンパイルし、全宣言を公理監査。許容公理は `propext`、`Quot.sound`、`Classical.choice`。許可外公理、禁止トークン、Lean警告、検査中のソース変更はすべて0件。
- 229件の既存unittest、関連する曲線文字・楕円曲線のpytest 9件、出典監査、整数・有理数の有限検算が成功。
- 原文Markdownと元Python2本はバイト一致で保存。元の `check_chain_exact.py` も別途再実行し成功。元のsignature近似コードは保存のみで、今回の証明結果として数えない。
- 新規語集合の個数は `toFinset.card = 20/70` を通常の `decide` で証明。`native_decide` は使用しない。

## 実行環境と失敗記録

Lean (version 4.30.0-rc2, x86_64-w64-windows-gnu, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)。mathlibと推移依存を含む固定revisionを検査前後で照合した。新しい作業ツリーでElasticaを構築し、既存の固定依存キャッシュを利用した。mathlib全体をソースから再構築したという意味ではない。

最初はPython環境のpytest不足で既存テストの読込に失敗した。作業専用の依存先へpytest 9.2.0を導入した。Gitの改行設定を一時的に上書きした再試行では、Windowsの既存テストfixtureと不一致になり、上書きを取り除いた。全体Lean検査では空語リストの `[[]]` がimport済み記法と衝突したため、`([] : List Bool) :: []` と明示した。定理文や意味を弱める変更はない。失敗した検査が生成した未解決プレースホルダーは公理監査で拒否されており、成功結果へ混ぜていない。

失敗・成功の生ログは作業用 `curve-word-chain-evidence/` に保存した。成功原ログのハッシュは `validation.json` の `local_raw_evidence` を参照する。ローカル記録とGitHub Actionsの実行結果は別であり、この文書はCI成功やmainへのマージを主張しない。

## 境界

代数状態と整数語の形式証明であり、円弧積分との完全な形式的同定、一般の滑らかな接合、最小平均閉路・スペクトル半径の一般定理、三次線積分、全次数Chen・Hambly–Lyons・BCHはここに含めない。[A〜Mの対応表](README.md)に各項目の根拠を分けて記載した。
