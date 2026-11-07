# primitive-lean

平面曲線の曲げエネルギー（エラスティカ）の変分から出発し、定義と証明を Lean 4 で積み上げる「原始の形式化」の公開リポジトリです。本文は [原始の形式化.md](原始の形式化.md)、本文と Lean 宣言の対応は [検証と再実行.md](検証と再実行.md) にあります。

- Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`（[lean/lean-toolchain](lean/lean-toolchain)・[lean/lakefile.toml](lean/lakefile.toml) で固定）
- すべての宣言を `--trust=0` でコンパイルし、公理監査を行います。許可する公理は Lean 標準の `propext`・`Quot.sound`・`Classical.choice` のみで、`sorry`・`native_decide`・独自の `axiom` は使いません。

## 主定理

以下の5つが、このリポジトリの中心となる結果です。Lean の文は要点を抜き出したもので、正確な仮定は各リンク先の宣言を参照してください。いずれも**必要条件・存在・個数**の主張であり、逆向きや最小曲線の存在は主張しません。

### 1. 一般密度エラスティカの局所最小の必要条件

[`Elastica.locallyMinimizing_necessary_conditions`](lean/Elastica/MinimumConditions.lean)

長さ ℓ>0 で、端点の角度・位置を固定した C¹ 比較の下で、一般の C³ 密度 ε による曲げエネルギー ∫ε(κ)ds の局所最小になっている C³ の接線角 θ を考える（直線は除く）。このとき、ある乗数 λ, μ, σ について、区間内部で次の3つが同時に成り立つ。

- 角度の方程式：(ε'(κ))' = −λ sin θ + μ cos θ
- 第一積分：κ ε'(κ) − ε(κ) − λ cos θ − μ sin θ = σ
- 曲率の方程式：(ε'(κ))'' + κ² ε'(κ) − κ ε(κ) − σ κ = 0

さらに、拘束を保つ変分について第二変分は非負になる。停留性や乗数の存在は仮定せず、エネルギーを摂動パラメータで実際に微分して導いている。

```lean
theorem locallyMinimizing_necessary_conditions
    (hℓ : 0 < ℓ) (hε : ContDiff ℝ 3 ε) (hθ : ContDiff ℝ 3 θ)
    (hne : ¬ ∀ s ∈ Icc 0 ℓ, θ s = θ 0) (hmin : LocallyMinimizing ε θ ℓ) :
    ∃ lam μ σ : ℝ, (∀ s ∈ Ioo 0 ℓ, 角度の方程式 ∧ 第一積分 ∧ 曲率の方程式) ∧
      (∀ η, 拘束の線形化 → 0 ≤ 第二変分)
```

### 2. 面積拘束付き最小から曲率方程式・位相平面の保存系へ（本文 5.5 節の主結果）

[`LinearInputMainResult.locallyMinimizing_pressure_curvature_phase`](linear_input/lean_check/MainResult.inc)

二次の曲げ密度（係数 k>0）で、長さ・端点・符号付き面積を固定した局所最小 θ を考える。このとき、**同じ定数** p（面積乗数）, σ, c について、次がすべて成り立つ。

- 面積項を加えた汎関数での停留性
- 曲率の方程式 k κ'' + (k/2) κ³ − σ κ = p
- 曲率から作った位相曲線 (x, y) = (κ, κ' + √2 κ) が、四次エネルギー E_u（λ=1/2, r=−σ/k, u=p/k）のハミルトン系を満たし、E_u = c で保存される

```lean
theorem locallyMinimizing_pressure_curvature_phase
    (hℓ : 0 < ℓ) (hk : 0 < k) (hθ : ContDiff ℝ 3 θ)
    (hmin : LinearInputAreaMinimum.LocallyMinimizing k θ ℓ) :
    ∃ p σ c : ℝ, Stationary k p θ ℓ ∧ ∀ s ∈ Ioo 0 ℓ,
      k * κ'' + k * κ ^ 3 / 2 - σ * κ = p ∧ E (1/2) (-σ/k) (p/k) x y = c ∧ (ハミルトン系) ∧ …
```

### 3. 同じ係数で指定した帰還則の大域解と収束

[`LinearInputMainResult.pressure_parameters_global_feedback`](linear_input/lean_check/MainResult.inc)

主定理2の係数のまま、帰還率 γ>0、C¹ 関数 b、目標値 e* > (max(σ/k, 0))²/6 を**別途指定**する。このとき、初期エネルギーが e* より大きい任意の初期点から、前方大域解が存在する。その解では、エネルギーは e* より大きいまま狭義に減少して e* に収束し、軌道は単射（同じ点を再び通らない）。曲線の最小性から時間発展が導かれるという主張ではない。

### 4. 四次模型の一意な大域最小の完全な判定

[`LinearInputQuarticClassification.unique_global_minimum_iff`](linear_input/lean_check/QuarticClassification.inc)

λ>0 の四次エネルギー E について、平面上の点 (a, √2 a) が**一意な大域最小点**になるための必要十分条件は、次の2つが成り立つこと。

- 入力が u = λa³ + ra（`input λ r a`）である
- λa² + r > 0、または a = r = 0

### 5. チェビシェフ型三倍角反復の実逆像の個数

[`LinearInputBranchFibers.real_inverse_card_regular`](linear_input/lean_check/BranchFibers.inc)（端点の場合は `real_inverse_card_one`, `real_inverse_card_neg_one`）

三倍角の式 T(x) = 4x³ − 3x を n 回反復した写像 Tₙ について、−1 < y < 1 なら方程式 Tₙ(x) = y の実数解はちょうど 3ⁿ 個。y = ±1 のときは (3ⁿ+1)/2 個。

```lean
theorem real_inverse_card_regular (n : ℕ) (hy0 : -1 < y) (hy1 : y < 1) :
    {x : ℝ | ternaryIterate n x = y}.ncard = 3 ^ n
```

これら以外の追補（有限ベイズ更新、F0/F16 の有限モデル、ガロア・クンマー拡大、演算子の自己拡張、Orbit-trace 多項式など）は、本文の第8章以降と [検証と再実行.md](検証と再実行.md) に、宣言名と仮定の対応表があります。

## 検証の実行

```bash
cd lean && lake exe cache get && cd ..             # mathlib のビルド済みキャッシュを取得
pip install pytest==9.2.0 numpy==2.5.4
python -B -X utf8 tools/verify.py --integration-only
```

`--integration-only` は、次をまとめて実行します（CI と同じ内容です）。

- ソースハッシュの照合
- リポジトリのテスト
- 有限検算
- ARC3 のオフライン検査
- Lean の joint 検査と追補の検査（`--trust=0`）
- 全宣言の公理監査

ほかに次のモードがあります。

| モード | 内容 |
|---|---|
| `--proof-only` | Lean 証明と公理監査のみ |
| `--arc3-only` | ARC 実験の検査のみ（Lean は実行しない） |
| 引数なし | 統合前の保存版との照合と、配布物・描画の検査を含む全体検査。`archive/before_unification_2026-10-20.zip` が必要で、このリポジトリには含まれていません |

実行結果は `verification/` に出力されます（Git では追跡しません）。過去の検証記録は [docs/verification/](docs/verification/) にあります。

## 入口

- **本文・証明**: [原始の形式化.md](原始の形式化.md) · [Elastica](lean/Elastica.lean) · [線形入力](linear_input/lean_check/README.md)
- **統合台帳・検証**: [ソースSHA-256台帳](docs/integration/manifest.json) · [2026-11-02統合説明](docs/integration/2026-11-02-review.md)
- **多項式・Orbit-trace**: [OrbitTrace入口](lean/OrbitTrace.lean) · [研究上の成立条件と未証明事項](docs/research/2026-11-04-orbit-trace-integrals.md)
- **演算器の観測・有限自己拡張**: `linear_input/lean_check/OperatorWordObservations.inc` 〜 `HigherOrderLiftSelfRewriting.inc` · [系列の統合境界](docs/integration/2026-11-05-operator-rulefold-consolidation.md)
- **デモ**: [Rulefold × デジタル曼荼羅](demos/rulefold_mandala.html) · [数学モデルとの区別](demos/RULEFOLD_MANDALA_README.md)
- **実験**: [ARC 公開デモのローカル統合検査](experiments/arc3/README.md) · [Kaggle handoff（歴史的記録）](docs/KAGGLE.md)
- **未統合の研究系列**: [PR #75](https://github.com/Sumuji-zkdwn/primitive-lean/pull/75) は履歴非保存・局所接合の証明群を統合提案中。#70 と #71 は同名の異なるLean原稿なので未選定です。
- **更新履歴**: [docs/HISTORY.md](docs/HISTORY.md)（2026-11-06 までの README の日付別記録）

## 運用方針

- 定義、追加の仮定、手書きの証明、Lean の証明、数値検算を区別して記録します（[AGENTS.md](AGENTS.md)）。
- ZIP、`.lake/`、ビルド生成物、認証情報は Git 履歴に入れません。
- スマートフォンからの追加手順は [docs/MOBILE_UPLOAD.md](docs/MOBILE_UPLOAD.md) を参照してください。
