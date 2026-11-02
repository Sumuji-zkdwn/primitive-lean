# F16実左作用の完全階数分類（2026-11-01）

## 最終結果

元の十六元数（sedenion）符号表に従う実16次元左乗法行列 `L(t)=L_(e3)+tL_(e10)` について、任意の `t:ℝ` に対するMathlibの実際の `Matrix.rank` をLeanで完全に分類した。

```lean
theorem rank_classification (t : ℝ) :
    (realPencilAll t).rank =
      if t = 1 ∨ t = -1 then 12 else 16

theorem rank_twelve_iff (t : ℝ) :
    (realPencilAll t).rank = 12 ↔ t = 1 ∨ t = -1

theorem rank_sixteen_iff (t : ℝ) :
    (realPencilAll t).rank = 16 ↔ t ≠ 1 ∧ t ≠ -1
```

## 証明構造

1. 前段階の `F16RankCertificate.inc` が証明した整数パラメータ版 `realPencil` と、`F16RealDeterminant.inc` の実パラメータ版 `realPencilAll` の同一性を任意の整数について成分ごとに証明 (`realPencilAll_of_int`)。
2. この同一性により、`t=±1` の階数がそれぞれ正確に12であることを既存の検証済み定理から輸送。
3. 前段階の `realPencilAll_det` と実数上の `1+t²>0` から、`det L(t)=0 ↔ t=±1` を証明。
4. `t≠±1` では行列式が非零であるため、Mathlibの `Matrix.isUnit_iff_isUnit_det`、`Matrix.rank_of_isUnit` によって階数16を証明。
5. 最終的なif式と二つの必要十分条件を導出。

## 検証と統合

- 新原稿：`linear_input/lean_check/F16CompleteRank.inc`
- PR：https://github.com/Sumuji-zkdwn/primitive-lean/pull/22
- 検証対象HEAD：`86847645648657cfcf2ef2bbfa38e994b2cdba71`
- GitHub Actions：https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41236706388
- `completed / success`、`python -B -X utf8 tools/verify.py --proof-only` に成功
- 固定Lean `4.30.0-rc2`、固定mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、`--trust=0`
- **828定理・1,026宣言**、旧819定理・1,017宣言に対し9定理・9宣言を追加
- 全宣言公理監査成功。警告・エラー・禁止トークン・許可外公理は0。
- PR #22からPR #3の研究ブランチにマージ。統合コミット：`b82cf216a8905d5a16ed548a159552b942beedd8`。
- `main` は変更しない。

## 境界

この定理は符号表を明示的に与えた有限16次元実線形作用の結果。元のCayley–Dickson再帰から符号表をLean内で生成する一般定理、非結合十六元数の全ての積の性質、全スペクトル、21断面の幾何分類を証明したものではない。

今回の目標だった「全16×16行列式公式」と「全実パラメータの階数分類」の形式化・結合監査は完了。
