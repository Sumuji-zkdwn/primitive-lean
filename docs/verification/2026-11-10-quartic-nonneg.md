# 四次模型の支持分類を λ ≥ 0 へ拡張する（2026-11-10）

## 主張

`LinearInputQuarticClassification` は `0 < lam` を仮定して、スカラー四次模型
`lam x^4/4 + r x^2/2 - u x` の支持・厳密支持を分類している。
新しい原稿 `linear_input/lean_check/QuarticNonneg.inc`（名前空間
`LinearInputQuarticNonneg`）は、仮定を `0 ≤ lam` に緩め、四次項を除いた
`lam = 0` を含めて次を証明する。

```text
gap_factor:      V(x) - V(a) - input(a) (x - a)
                   = (x - a)^2 (lam (x + a)^2 / 4 + (lam a^2 + r) / 2)
support_iff_input_and_margin (0 ≤ lam):
                 a を支持する u  ⇔  u = input lam r a ∧ 0 ≤ lam a^2 + r
strict_support_iff (0 ≤ lam):
                 a を厳密に支持する u
                   ⇔  u = input lam r a ∧ (0 < lam a^2 + r ∨ (0 < lam ∧ a = 0 ∧ r = 0))
```

`strict_criterion_agrees_of_pos` は、`0 < lam` のとき右辺が既存の
`0 < lam a^2 + r ∨ (a = 0 ∧ r = 0)` と同値であることを示す。既存の例外項
`a = r = 0` は、四次項が残る場合にだけ現れる。

`lam = 0` の系として、厳密支持は `u = r a ∧ 0 < r` に限ること
（`zero_quartic_strict_support_iff`）、`r = u = 0` では全点が大域最小点であること
（`zero_quartic_flat_all_minimal`）、`r < 0` または `r = 0, u ≠ 0` では大域最小点が
存在しないこと（`zero_quartic_no_minimum_of_neg`、
`zero_quartic_no_minimum_of_flat_input`）を証明する。`quartic_scaling` は
`lam = s^2, s ≠ 0` での尺度変換 `f(s^2, r, u, x) = f(1, r, s u, s x) / s^2` である。

## 依存と範囲

既存の定義 `LinearInputDesign.f`・`LinearInputDesign.input` と、
`LinearInputCalculus.global_minimum_forces_input`（λ の符号を仮定しない微分による
入力の特定）だけを使う。既存の原稿・定理名・構成は変更していない。

結論はスカラー四次模型の支持と最小に限る。`lam → 0` での最小点の脱出・選択などの
漸近挙動、力学的な結論、一般のポテンシャルへの拡張は主張しない。漸近挙動の手証明と
有限有理数検算は、Research 側の研究ノート `05_Notes/quartic_removal_2026-11-10`
にあり、この原稿の Lean の結論とは区別する。

## 実行した検証

親コミット `389bcf585e206fdf4241f73e75dc3f40a27ad43e` に、この原稿と登録の変更を
加えた未コミットの作業木で、2026-11-10（日本時間）に実行した。

- `python -B -X utf8 tools/verify.py --integration-only`：全段階成功
  （`passed: true`。作業木が未コミットのため記録上は `dirty: true`）
- 共通 Lean 検証：3,424定理・4,630名前付き宣言（変更前 3,411・4,617 から +13・+13）、
  `--trust=0`
- 公理監査：追加の13定理はいずれも `propext`、`Classical.choice`、`Quot.sound`
  のみに依存。`sorryAx` なし
- unittest：既存の全テストが成功（このPCの Python 3.14 に pytest 9.2.0・numpy 2.5.4 を
  入れた仮想環境で実行。CI の指定版と同じ）
- Lean：`lean/lean-toolchain` の `leanprover/lean4:v4.30.0-rc2`、
  固定された Mathlib（`lean/lake-manifest.json`）

`--rebuild` は使っていない（同じ日にこの作業木で先に実行したときのビルド出力を再利用）。CI での実行結果は、この記録の
時点では未確認である。
