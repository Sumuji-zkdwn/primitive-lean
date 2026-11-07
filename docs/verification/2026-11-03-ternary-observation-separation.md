# 三進零配置と有限識別作用素 — 検証記録

- 日付: 2026-11-03 (JST)
- 研究PR: https://github.com/Sumuji-zkdwn/primitive-lean/pull/36
- 独立Lean検証済みコミット: `140c8e648e89400959d15ce7c2459ce45e635364`
- 独立Lean検証: https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41545652923 (success)
- ツールチェーン: `leanprover/lean4:v4.30.0-rc2`, Mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`
- 実行: `lake env lean --trust=0 TernaryZeroCesaroProbe.lean`
- source SHA256:
  - `linear_input/lean_check/TernaryZeroCesaro.inc`: `9015645e6ab0f748e28f4edf1516a1526df31f058d623cbdeea0822dc4ae1776`
  - `linear_input/lean_check/FiniteObservationSeparation.inc`: `431492dd7339e1f66dd91d331475058102d8bfe463e7eb87eef4d7bbc96fb2a8`

## 数学的な主張

1. 三進配置は `ternaryPosition k r = 3*k+r.val` として構成。隣接ブロックに対して添字の増加性と剰余の復元を証明。
2. 二つのブロック `+1,-1` の非零項の順序を固定したとき、六時刻の部分和平均は `(3 + q - p)/6`。全9通りをLeanで網羅。
3. 任意の有限滞在時間列 `(s,d)` に対して、各状態 `s` を `d` 回繰り返した列の総和は `Σ d*s`。
4. 任意の `K : α → β`, `P : α → γ` に対し、
   `(K x,P x)=(K y,P y) ↔ (K x=K y ∧ P x=P y)`。
5. `K x=K y` かつ `P x≠P y` であれば、`P` は `K` のみの後処理では生成できない。
6. `Fin 3` 上の冪等な忘却写像と補助マーカーは、単独では非単射だが対にすると単射。2種類からなる **明示的に制限した観測ライブラリ** での必要最小数は2。
7. `Fin 2 × Fin 3` の6状態は、偶奇座標あるいは三進座標だけでは識別できず、両座標を用いれば復元できる。
8. 零削除した非零項の順序と最終和が一致する二つの具体的配置において、チェザロ平均は `5/6` と `1/6` で異なる。この平均は非零項列のみを入力として復元できない。

## 検証範囲と留保

独立テストは `import Mathlib` の後ろに二つの `.inc` を順番に結合したLeanファイルを作り、`--trust=0` で検査する。ソースには `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` を許容しない。

既存の統合検査には二つの宣言群を登録済みだが、**全体統合の結果は別途確認する**: https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41546060390

無限チェザロ極限、一般 `n_k` の無条件な分類、一般モノイドの一意分解、任意写像まで許す場合の最小観測数、計算量の下界は証明対象外。

今回の有限モデルは既存の `LinearInputF0.Idempotent` と同じ形の冪等性を満たすが、既存F0定理群から新定理が自動的に導出されることまでは主張しない。分解の最終評価と履歴識別の差異を形式的に比較するための最小の独立実験である。
