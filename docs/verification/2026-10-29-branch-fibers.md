# 三分岐ラベルのファイバーと実逆像数 — 2026-10-29

**40定理・7定義を追加し、既存分を含む603定理・675宣言のLean証明・公理検査が、今回のWindows環境で成功した。**

基準コミットは `986d8cdfd09e8c1cef01b8c2fa9b1b9a702c1991`。既存68証明原稿を保持し、[BranchFibers.inc](../../linear_input/lean_check/BranchFibers.inc) を第9追補として登録した。有限回の列挙による推測ではなく、任意の自然数nを量化した実数上の定理である。

## 証明した内容

| 内容 | 結論 |
|---|---|
| 有限ラベルの候補値 | d>0、0≤t≤π、j∈Fin dに対するcos((t+2πj)/d) |
| 候補の等値条件 | 同一ラベル、またはt+(j+k)π=dπ |
| 通常値 | 0<t<πで単射、相異なる候補はd個 |
| 奇数次数の臨界値 | d=2m+1で相異なる候補はm+1個 |
| 代表元 | min(j,d−j)、min(j,d−1−j)を明示。候補値の保存と代表元上の単射性 |
| 冪等写像 | 代表ラベルへ写すKについてK(K(j))=K(j) |
| ファイバー | t=0ではj=0、t=πではj=mだけが単元。他は明示した相手との2要素集合 |
| 網羅性 | T₃のn回反復の実逆像集合と有限候補集合が等しい |
| 実逆像数 | −1<y<1で3^n、y=±1で(3^n+1)/2 |
| 反例 | n=1の異なる2ラベルの衝突。n=2,y=1で実解数5≠2^2 |

主定理は `real_inverse_card_regular`、`real_inverse_card_one`、`real_inverse_card_neg_one`。`Set.ncard`で数えるのは相異なる実数解であり、ラベル数や代数的重複度ではない。n=0も恒等写像として扱う。

既存の `LinearInputBranchForgetting.ternaryIterate`、`ternaryIterate_cos`、`iterated_inverse_candidate` をそのまま使う。区間外の点が目標区間へ入らないことと、arccosによる解の表示から候補の網羅性を証明している。

本文は [第8.14節](../../原始の形式化.md)、宣言の正確なヘッダー・行番号・使用公理・ハッシュは [導出台帳](../../sources/branch_fibers_2026-10-29.json) に保存した。

## 今回の実行

```powershell
python -B -X utf8 tools/verify.py --proof-only
```

- 終了コード0。2段階の所要時間は合計126.099秒。
- Elasticaビルドを含む既存部分の検査63.682秒、9追補を含む全体の検査62.417秒。
- 両統合Leanファイルを `--trust=0` で検査し、全675宣言の公理監査に成功。
- 警告、コンパイルエラー、許可外公理、禁止トークン、検査中の対象ソース変更は0件。
- 公理依存は `propext`、`Classical.choice`、`Quot.sound` の範囲。
- Lean `4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。依存9件の固定リビジョンを照合。
- 既存68証明原稿を基準コミットと照合し、改行形式を除く内容が不変であることを確認。Git blobと作業コピーの生SHA-256、改行差も記録。

今回の追加後の検査では `--rebuild` を指定していない。固定依存と直前に構築したプロジェクトのビルドキャッシュを使用し、統合Leanファイルは新たに生成・検査した。開発時の補助モジュールを最終検査の入力には使っていない。

## 保存した証拠

- [監査結果・既存原稿照合・ハッシュ](../../evidence/local/2026-10-29-branch-fibers/audit.json)
- [統合入口の結果](../../evidence/local/2026-10-29-branch-fibers/proof-only.json)
- [全675宣言・公理・ソースハッシュ](../../evidence/local/2026-10-29-branch-fibers/main-result.json)
- [追補を含むLean生ログ](../../evidence/local/2026-10-29-branch-fibers/main-result.log)
- [既存部分の結果](../../evidence/local/2026-10-29-branch-fibers/joint.json)・[生ログ](../../evidence/local/2026-10-29-branch-fibers/joint.log)
- [Elasticaビルドログ](../../evidence/local/2026-10-29-branch-fibers/elastica-build.log)

## 範囲

この追補は候補等値条件から代表元・ファイバー・実逆像数までを扱う。目標値が[-1,1]の外の場合の実逆像数、分岐語から整数への基数3符号化、別モデルのK,S,C遷移則との一致、観測履歴の復元、ベイズ更新との可換性は追加していない。既存の最小値観測による忘却定理とは区別する。

保存ZIP・HTML描画・人間データの校正・ARCの方策性能は今回の検査対象外である。
