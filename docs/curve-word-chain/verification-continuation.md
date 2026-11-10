# 曲線文字チェイン追補の検証 — 2026-11-10

実装コミット `1683b54db2514a09da6125904e0dfdd193906393` に対して `python -B -X utf8 tools/verify.py --integration-only` の **26段階すべてが成功**した。検証開始時の作業ツリーはクリーン。第一段階の55定理の記録は変更せず、今回の結果を [validation-continuation.json](validation-continuation.json) と [continuation-provenance.json](continuation-provenance.json) に分けて保存する。

## 今回の追加と共通検証

| 原稿 | 定理 | 全宣言 |
|---|---:|---:|
| CurveWordArc.inc | 18 | 25 |
| CurveWordFiniteState.inc | 26 | 37 |
| CurveWordCycleLimit.inc | 17 | 22 |
| CurveWordRealization.inc | 28 | 35 |
| CurveWordThermodynamics.inc | 17 | 21 |
| CurveWordSignature.inc | 14 | 18 |
| CurveWordCircularMoment.inc | 30 | 38 |
| 合計 | 150 | 196 |

- 共通結合検査は **3,616定理・4,894宣言**。この件数は共通検査対象であり、独立モジュールを含む全リポジトリの総数ではない。
- `--trust=0` でコンパイルし、全4,894宣言の公理を監査。許容するのは `propext`、`Quot.sound`、`Classical.choice`。
- Lean警告、禁止トークン、許可外公理、検証中のソース変更は0件。固定依存revisionは実行前後とも一致。
- 既存unittest 229件、出典・登録監査、整数/有理数検算、ARC3のオフライン検査、独立MovingCurve/Okanohara/FiniteMarkov検査を含む全26段階が成功。
- 7本の新原稿は先に個別probeでも検査した。共通結果を個別結果から推測せず、実際の全組立で再確認した。

## 環境と記録

Lean (version 4.30.0-rc2, x86_64-w64-windows-gnu, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)。既存の固定依存キャッシュを使用した。mathlib全体をソースから再構築したという意味ではない。Pythonテストには作業専用のpytest 9.2.0・NumPy 2.4.4を使用した。

本文HTMLは作業専用Markdown 3.8.2と既存チェックアウトのKaTeX資産を使って再生成した。初回のMarkdown不足と、この作業ツリーでのvendor資産不足はローカル補助環境を整えて解決した。これらはLean証明の失敗とは別である。追加文書のリンク、数式生成、重複アンカー、ローカルフォントの[表示検査記録](render-validation-continuation.json)も保存した。ブラウザ視覚確認は主張しない。

個別証明の開発中には積分の測度/関数の型推論不足、未使用tactic、ASCII `pi` の解釈を修正した。定理文を目標結論の仮定に置き換えてはいない。成功した共通検証の生ログは作業用 `curve-word-chain-continuation-evidence/passing-integration/` に保存し、機械可読記録にハッシュを載せた。

## 証明の範囲

円弧の実積分から任意語の状態評価、Bellman全語最小化と四状態の物理単位長時間極限、固定有限族の零温度極限、全有限次数の積分相似、明示円周列の面積一致と三次差までを追加した。詳細は [continuation.md](continuation.md)。

任意Boolean語を単一の区分曲線へ構成する橋、滑らかな継ぎ目、一般グラフの最小閉路平均、一般のラプラス一意性・スペクトル極限、全次数Chen・Hambly–Lyons・完備自由リー代数・BCHは別に残る。この記録はローカル結果であり、CI成功やmainへのマージを主張しない。
