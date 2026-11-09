# 回転する直線への逐次射影：忘却を細かく刻むと矢印が残る

2026-11-09。独立モジュール [lean/RotatingProjections.lean](../../lean/RotatingProjections.lean)（Mathlib のみを import）。既存の Elastica・線形入力の宣言は変更していない。

## 定義

平面ベクトル v を、角度 θ の直線へ直交射影する。

```text
coeff θ v = v₁ cos θ + v₂ sin θ
proj θ v  = (coeff θ v · cos θ, coeff θ v · sin θ)
```

刻み Δ 0, Δ 1, … を与え、k 番目の直線の角度を `line Δ θ₀ k = θ₀ + Σ_{i<k} Δ i` とおく。`run Δ θ₀ k` は直線 1, …, k へ順に射影する合成写像である。半回転を等分する場合は `halfStep n = (i ↦ π/n)` とする。

## Lean で証明した主張（28定理、`--trust=0`、許可公理のみ）

| 宣言 | 内容 |
|---|---|
| `proj_idempotent` | proj θ ∘ proj θ = proj θ。F0 の `Idempotent` と同じ形の冪等写像 |
| `run_scaled_dir`, `run_dir` | 直線上の長さ r の矢印は、k 回後に長さ r·∏_{i<k} cos Δ i で k 番目の直線上にある |
| `run_halfStep_final` | n ≠ 0 なら、(1,0) は n 回後に (−cos(π/n)ⁿ, 0) |
| `halfTurn_two`, `halfTurn_three`, `halfTurn_four` | n = 2, 3, 4 で (0,0), (−1/8,0), (−1/4,0) |
| `halfTurn_four_trace` | (1,0) → (½,½) → (0,½) → (−¼,¼) → (−¼,0) |
| `halfTurn_four_coordinate_reappears` | 第1座標は 1 → 0（2回後）→ −1/4（4回後） |
| `halfTurn_bounds` | n ≥ 3 で 1 − π²/(2n) ≤ cos(π/n)ⁿ ≤ 1 |
| `halfTurn_tendsto_one` | cos(π/n)ⁿ → 1 |
| `bending_lower_bound` | すべての i < k で \|Δ i\| ≤ 1 なら 1 − (Σ Δ i²)/2 ≤ ∏ cos Δ i |
| `equal_steps_optimal` | n 個の刻みが [−π/2, π/2] にあり総和が Θ なら ∏ cos Δ i ≤ cos(Θ/n)ⁿ（AM-GM と cos の凹性） |
| `run_absorbs_first` | k ≥ 1 なら run k ∘ proj(line 1) = run k |
| `identified_stay_identified` | 最初の射影で一致した2入力は、以後のすべての段で一致する |
| `proj_not_commute` | proj 0 ∘ proj(π/4) ≠ proj(π/4) ∘ proj 0（(1,0) で (½,0) と (½,½)） |
| `halfTurn_four_not_idempotent` | 4段の合成 T は冪等でない：T(T(1,0)) = (1/16,0) ≠ (−1/4,0) |

数値の 100 回で約 95.2%（cos(π/100)¹⁰⁰ ≈ 0.95184）は Lean の定理ではなく、`tests/test_rotating_projections.py` の浮動小数点検算である。Lean で保証するのは上の下界 1 − π²/200 ≈ 0.9507 と上界 1 まで。

## F0 との接続

各 `proj θ` は F0 の K（冪等写像）の線形版である。既存の F0 定理（`step_equal_on_fibers`, `A_B_collapse`）は、**一つの K** と条件 B を満たす S の下で、捨てた区別が戻らないことを述べる。この実験では K を毎回取り替えるので、隣り合う K は可換でない（`proj_not_commute`）。合成は冪等ですらない（`halfTurn_four_not_idempotent`）。

それでも、合成全体は最初の射影を吸収する（`run_absorbs_first`）。したがって、

- **座標の値は再出現する**（`halfTurn_four_coordinate_reappears`）
- **最初の射影で消えた入力の区別は戻らない**（`identified_stay_identified`）

の2つが両立する。値の再出現と区別の復活を分けることが、F16 の「忘却後の差の再出現」（`docs/verification/2026-11-01-f16-holonomy.md`）や第8.16節のベイズの反例と比べるときの要点になる。この独立モジュールは `LinearInputF0` を import しておらず、F0 の宣言への形式的な接続は未登録である。

## 曲げエネルギーとの接続（手計算、Lean 未形式化）

弧長 ℓ を n 等分して h = ℓ/n、Δ i = κ(s_i)·h とすると、Σ Δ i² = h·Σ κ(s_i)² h ≈ (ℓ/n)∫κ² ds となる。`bending_lower_bound` と合わせると、損失は概ね (ℓ/2n)∫κ² ds、すなわち二次密度の曲げエネルギーの h/2 倍で抑えられる。等曲率（円弧）では π²/(2n) となり、`halfTurn_bounds` と一致する。この連続極限は手計算であり、リーマン和の収束は形式化していない。

## 範囲の限定

- 拘束しているのは接線角に当たる直線角の**総回転だけ**で、端点位置は固定していない。`equal_steps_optimal` が等分割（円弧）を最適とするのはこのためであり、第3章の端点固定エラスティカ問題の局所最小とは別の問題である。
- 射影は直交射影に限る。量子ゼノン効果や偏光板との対応は解釈であり、ここで述べる長さは振幅である（強度は2乗：100 回で約 90.6%）。
- n = 1 では直線が元の x 軸に戻るので、何も変わらない（逆向きにはならない）。`run_halfStep_final` の右辺は cos(π)¹ = −1 で (1,0) を与える。

## 再実行

```bash
python -m unittest tests/test_rotating_projections.py -v
cd lean && lake exe cache get
lake env lean --trust=0 RotatingProjections.lean
```

公理監査はワークフロー `.github/workflows/rotating-projections.yml` が行う。2026-11-09 のローカル実行（Lean v4.30.0-rc2、mathlib `5450b53e`）では、コンパイルの警告・エラー 0、28定理すべてが `[propext, Classical.choice, Quot.sound]` のみに依存、Python 検算 6 件成功。
