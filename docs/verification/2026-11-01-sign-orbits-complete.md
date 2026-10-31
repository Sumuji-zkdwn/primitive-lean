# 32符号パターンの8反転軌道への厳密商化（Lean検証）

2026年11月1日。先行するPR #8の `VariablePairGaloisBridge.inc`（21定理・10定義）を、PR #10で加法的に拡張した。

## 今回証明した命題

形式的符号パターン `σ : Fin 5 → Bool` に対して、以前に定義した反転 `flipX`（混合項・入力項の符号を反転）と `flipY`（混合項だけを反転）を使用する。

```text
sameReflectionOrbit σ τ :=
 τ=σ ∨ τ=flipY σ ∨ τ=flipX σ ∨ τ=flipX (flipY σ)

signShape σ : Fin 3 → Bool
```

新たな `sameReflectionOrbit_iff_signShape` により

```text
sameReflectionOrbit σ τ ↔ signShape τ = signShape σ
```

を**必要十分条件**として証明した。先行PR #8の単なる `signShape_flipX` / `signShape_flipY`（不変性）より強い命題である。

- `sameReflectionOrbit_canonical`: 各軌道は正規代表元 `signCanonical (signShape σ)` を含む。
- `signOrbitSetoid`: この同一視に対応する同値関係。
- `sameReflectionOrbit_iff_setoid`: 実際の反転軌道と同値関係の関係が一致する。
- `signOrbitEquiv`: `Quotient signOrbitSetoid ≃ (Fin 3 → Bool)`。
- `reflectionOrbit_count_eight`: 商集合の要素数が8。
- `sameReflectionOrbit_energy`: 同じ軌道なら、適切な x/y 符号反転によって既存 `signedEnergy` が一致する。

`bool_eq_not_of_ne` はBoolに関する補助定理。新規6定理・3定義、原稿全体は27定理・40宣言。

## 検証結果

GitHub Actions [#41218537964](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41218537964) — `completed/success`、対象証明ソースコミット `33f5309dbf5f29e8a677dbb0064f160fdd46af95`。

- 固定Lean: `4.30.0-rc2`、mathlib: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`
- `python -B -X utf8 tools/verify.py --proof-only`: `passed=true`
- `lake env lean --trust=0 ../linear_input/lean_check/MainResult.lean`: 終了コード0
- **782定理・939宣言**の統合証明検査、全939宣言の公理監査成功。
- `joint_axiom_audit=true`、`baseline_axioms_match=true`。
- `warnings=[]`、`errors=[]`、`unexpected=[]`、`forbidden_tokens=[]`、`changed_during_verification=[]`。
- 許可公理は既存の `propext`, `Classical.choice`, `Quot.sound`。未許可公理・`sorryAx`なし。
- 検査された新ソース `linear_input/lean_check/VariablePairGaloisBridge.inc` のSHA-256: `fd91c2b515112174446a2226bbbbe61d6ff01485ca02af14164e3e366239d08d`。
- [検証ログ・公理監査アーティファクト](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41218537964/artifacts/13048274611)（artifact ID `13048274611`、88,595 bytes）。

本ログは固定版の依存キャッシュを利用した実機検査であり、完全クリーンビルドではない。

## 数学的な境界

この8軌道は**形式的な5符号パターン**を `(x,y) ↦ (±x,±y)` で同一視する場合の結果。固定パラメータや制約領域まで固定した「15組すべての変数対問題」が8種類になると主張していない。

係数が0なら、異なる符号パターンが実際には同じ関数になる追加の退化が生じ得る。軌道の8分類を、関数そのものの全同値類数だと解釈しない。

判別式の符号による全実根の個数分類および `Gal(T_{3^n}(X)-y)≃D_{3^n}` の体としての同型証明は、この追補のLean検証範囲外。先行PR #8での `F=F'=0 ⇒ Δ=0`、`Δ≠0 ⇒ F=0でF'≠0`、チェビシェフ特例の臨界値 `u=±1` は保持した。
