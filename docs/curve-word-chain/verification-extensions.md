# 曲線文字チェイン拡張の検証 — 2026-11-11

実装コミット `890740320956b718c5117e9dc28b2f3fc761f06b` のクリーンな独立worktreeで、`python -B -X utf8 tools/verify.py --integration-only` の **26段階すべてが成功**した。この記録は同コミットの証明範囲を固定するものであり、一般Hambly–Lyonsの全体完成やCI成功を意味しない。

機械可読の [validation-extensions.json](validation-extensions.json) は、実行対象コミット、全ソースハッシュ、依存revision、追加宣言ごとの公理、生ログのハッシュを保持する。第一段階・PR #129の記録は変更していない。

## 検証結果

- 共通検査は **4,383定理・5,847宣言**。
- 今回の追加は **43ファイル・767定理・953宣言**。宣言数は既存checkerが索引化する theorem/lemma/def/abbrev の数で、structure/instanceを含めない。
- `--trust=0`、全対象宣言の公理監査、Lean警告・禁止トークン・許可外公理・検証中のソース変更はすべて0件。
- 許容する公理は `propext`、`Quot.sound`、`Classical.choice`。固定依存revisionは実行前後とも一致。
- 既存unittest **229件**、登録・出典監査、17本の独立検算、ARC3オフライン検査、独立MovingCurve/Okanohara/FiniteMarkovを含めて全段階が成功。

## 数学上の範囲

任意語の実曲線と整数状態・明示円周列の一致、一般有限グラフの最小平均閉路、ラプラス一意性、通常のスペクトル半径と零温度極限、全次数Chen/shuffle/通常の対数/実自由Lie次数別展開/BCH、実母関数の有理性を追加した。一般BV曲線から直接定義するcanonical署名と、一様収束・一様変動上界の下での全係数収束も含む。

**tree-like ⇒ 全署名自明** は任意有限次元の連続BV曲線について、実際の有限高さ標本・非巡回グラフ・折れ線積・極限を通じて証明した。逆方向と二曲線同値への最終接続は、このコミットでは未完。詳しい仮定と対応は [extensions.md](extensions.md) を参照する。

## 統合時の修正と再現範囲

新しいFreeLie importが一般のModuleインスタンスを加えたため、組立時に `attribute [instance 90] LieAlgebra.toModule` を記録付きで追加し、既存の解析インスタンスを優先した。既存の証明原稿は変更していない。新原稿のopenはnamespace内へ閉じ、既存Finset/Polynomial名と競合する参照を完全修飾した。失敗した組立ログと成功ログは作業用証拠ディレクトリに保持している。

検証には固定依存キャッシュを使った。mathlib全体のソース再構築ではない。本文HTMLの構文・数式・アンカー・ローカルフォント・文書リンクは [render-validation-extensions.json](render-validation-extensions.json) に別記録し、ブラウザ視覚確認とは区別する。

## 追加原稿

| 原稿 | 定理 | 索引化宣言 |
|---|---:|---:|
| CurveWordPiecewise.inc | 54 | 70 |
| CurveWordCircleWords.inc | 44 | 53 |
| CurveWordGraphLimit.inc | 22 | 28 |
| CurveWordDirectedGraph.inc | 10 | 21 |
| CurveWordLaplace.inc | 11 | 13 |
| CurveWordSpectral.inc | 19 | 21 |
| CurveWordTransfer.inc | 16 | 20 |
| CurveWordChen.inc | 11 | 13 |
| CurveWordFormalSeries.inc | 46 | 58 |
| CurveWordCoproduct.inc | 54 | 61 |
| CurveWordFriedrichs.inc | 43 | 55 |
| CurveWordTreeLike.inc | 13 | 16 |
| CurveWordSignatureTopology.inc | 17 | 24 |
| CurveWordReparametrization.inc | 5 | 5 |
| CurveWordBoundedVariation.inc | 23 | 27 |
| CurveWordStieltjes.inc | 20 | 34 |
| CurveWordBVSignature.inc | 9 | 10 |
| CurveWordBVReparam.inc | 17 | 20 |
| CurveWordBVChen.inc | 5 | 5 |
| CurveWordBVShuffle.inc | 10 | 10 |
| CurveWordSignatureTree.inc | 9 | 11 |
| CurveWordHeightMetric.inc | 28 | 34 |
| CurveWordScalarLog.inc | 5 | 5 |
| CurveWordLogFormula.inc | 18 | 18 |
| CurveWordBVTopology.inc | 12 | 18 |
| CurveWordBVAlgebra.inc | 6 | 6 |
| CurveWordConvexObservation.inc | 6 | 7 |
| CurveWordSignatureBounds.inc | 26 | 28 |
| CurveWordSignatureUniform.inc | 10 | 13 |
| CurveWordConvexSeparation.inc | 3 | 3 |
| CurveWordLinearAction.inc | 12 | 16 |
| CurveWordBVCanonical.inc | 28 | 34 |
| CurveWordWordSignature.inc | 6 | 7 |
| CurveWordGenerating.inc | 8 | 12 |
| CurveWordWordGenerating.inc | 5 | 8 |
| CurveWordSamplingOrder.inc | 10 | 13 |
| CurveWordTreeSignature.inc | 17 | 22 |
| CurveWordPolygonal.inc | 44 | 53 |
| CurveWordBVSubinterval.inc | 14 | 15 |
| CurveWordTreeSampling.inc | 31 | 39 |
| CurveWordTreeSampleProduct.inc | 4 | 4 |
| CurveWordTreeLimit.inc | 8 | 9 |
| CurveWordArcGenerating.inc | 8 | 14 |
