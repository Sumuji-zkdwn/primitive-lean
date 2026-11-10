# 曲線文字チェイン完成原稿の検証 — 2026-11-11

実装コミット `956fe5c9f18f1360a84a1736dcf038ebc0cdf7b3` のクリーンな独立worktreeで、`python -B -X utf8 tools/verify.py --integration-only` の **26段階すべてが成功**した。A〜Mの補助曲線文字模型と、今回指定された一般グラフ・ラプラス・スペクトル・全次数Chen・Hambly–Lyons・形式Lie/BCHの接続を、各定理の明示した仮定の下で検証した。

機械可読の [validation-completion.json](validation-completion.json) は、検査対象コミット、全ソースハッシュ、依存revision、追加宣言ごとの公理、生ログのハッシュを保持する。43ファイル時点の [途中検証記録](verification-extensions.md)、PR #128・#129の記録は保持した。

## 検証結果

- 共通検査は **4,673定理・6,194宣言**。
- 今回の追加は **56ファイル・1,057定理・1,300宣言**。宣言数は既存checkerが索引化する theorem/lemma/def/abbrev の数で、structure/instanceを含めない。
- `--trust=0`、全対象宣言の公理監査、Lean警告・禁止トークン・許可外公理・検証中のソース変更はすべて0件。
- 許容する公理は `propext`、`Quot.sound`、`Classical.choice`。固定依存revisionは実行前後とも一致。
- 既存unittest **229件**、登録・出典監査、17本の独立検算、ARC3オフライン検査、独立MovingCurve/Okanohara/FiniteMarkovを含めて全段階が成功。

## 最終定理の範囲

`CurveWordBVHamblyLyons.treeLike_iff_pathSignature_eq_unit` は、有限実座標空間の連続BV曲線について、実Stieltjes全署名の自明性と、独立な連続高さ関数によるtree-like性の同値を証明する。逆方向には、実曲線のコンパクト性・最小化・loop削除・弧の一意性・最小実変動量の距離・等長測地線・四点不等式を構成して使う。結論を新しい公理や最終定理の仮定へ移していない。

`CurveWordBVEquivalence.based_pathSignature_eq_iff_tree_equivalent` は同じcompact区間・同じ始点の二曲線について、全署名の一致を終点一致と実forward/reverse接合のtree-like性へ接続する。`CurveWordBVCoordinates.finiteDimensionalSignature_eq_unit_iff` は実有限基底と作用素ノルムによる高さ移送で任意有限次元実ノルム空間へ拡張し、署名の自明性の座標選択独立性も証明する。

全次数は任意の有限語の係数すべてを意味し、固定次数までの有限検算ではない。形式指数・通常の対数・各次数の実自由Lie元・BCHも全次数で扱う。自由Lie係数写像の単射性やPBW同型は追加主張しない。

曲線文字は接線が連続で曲率が継ぎ目で跳びうる補助模型である。滑らかなエラスティカの拘束付き停留性・最小性、無条件の二重極限交換、一般Fenchel–Moreau、独立した動力学はこの完成範囲に含めない。各項目の正確な前提は [extensions.md](extensions.md) と [A〜M対応表](README.md) に記す。

## 再現と保存

既存の証明原稿と添付原文のバイト列を保持し、新しい`.inc`を既存checkerへ加えた。FreeLieの一般Moduleインスタンスについて、記録された組立preludeで優先度を調整する。新原稿内で既存Finset/Setの名前と競合した参照は完全修飾し、失敗した検査ログも別に保存した。

検証には固定依存キャッシュを使った。mathlib全体のソース再構築ではない。本文HTMLの構文・数式・アンカー・ローカルフォント・文書リンクは [render-validation-extensions.json](render-validation-extensions.json) に別記録し、ブラウザ視覚確認とは区別する。この記録は上記コミットのローカル検査であり、GitHub CIの成否はその実行記録と区別する。

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
| CurveWordBVPathOperations.inc | 42 | 47 |
| CurveWordBVCompactness.inc | 20 | 26 |
| CurveWordBVLoopErase.inc | 28 | 32 |
| CurveWordBVReduced.inc | 13 | 14 |
| CurveWordBVArc.inc | 6 | 6 |
| CurveWordBVOrientation.inc | 2 | 2 |
| CurveWordGeodesicTree.inc | 9 | 11 |
| CurveWordBVArcUnique.inc | 24 | 26 |
| CurveWordBVIntrinsic.inc | 96 | 124 |
| CurveWordBVIntrinsicTree.inc | 10 | 13 |
| CurveWordBVHamblyLyons.inc | 27 | 31 |
| CurveWordBVEquivalence.inc | 7 | 7 |
| CurveWordBVCoordinates.inc | 6 | 8 |
