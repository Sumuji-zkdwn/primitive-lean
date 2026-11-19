# Siphon有限測定定理 — PR #146への独立追加

基準: `Sumuji-zkdwn/primitive-lean`、PR #146、
`763d5d88d26d5fe8a8830c3b74f57461213ba4ed`。
2026年11月17日（日本時間）。PR #146に積み重ねる追加定理。既存の定義・証明・依存ピンは変更しない。

## 定理

`I(u,v)=v+u³`、`L(u,v)=(v,v-u)` とする。
`E` は既存の `Elastica.SiphonPolynomialE.E`。
初期点 `z≠(0,0)` に対し、`I(z)≠0` なら `a=z`、そうでなければ `a=L(z)` とおく。

任意の自然数 `d` と、総次数がそれぞれ `d` 以下の実二変数多項式 `P,Q` について、

```
P(E^m(L(E^n(a)))) = Q(E^m(L(E^n(a))))
       0 ≤ n ≤ d+1,  0 ≤ m ≤ 3d
```

がすべて成立すれば `P=Q`。したがって `(d+2)(3d+1)` 測定で十分である。
作用順は `a → E^n → L → E^m`。関数合成を右から作用させる記法では `E^m L E^n`。

さらに、最初の `d+2` 候補から異なる非零不変量を持つ `d+1` 本を選べるため、
`(d+1)(3d+1)` 測定で十分である。

未知多項式の値とは無関係に、既知の点座標から評価行列の独立行を選べば、
ちょうど `N(d)=(d+1)(d+2)/2` 測定に削減できる。
これは全ての次数 `d` 以下の多項式を決定するための最小測定数でもある。
この最適化は選択された添字が初期点に依存することを許す。
全初期点に共通する固定の `N(d)` 個の操作列を示した、という主張ではない。

| d | 元の長方形 | 曲線選択後 | 独立行選択後・最小値 |
|---:|---:|---:|---:|
| 0 | 2 | 1 | 1 |
| 1 | 12 | 8 | 3 |
| 2 | 28 | 21 | 6 |
| 3 | 50 | 40 | 10 |
| 5 | 112 | 96 | 21 |
| 10 | 372 | 341 | 66 |

ここでの測定とは、既知の到達点での未知多項式の**正確な実数値**を一回読むこと。
初期点の座標が既知であること、同じ初期点から各有限操作列を実行できることを前提とする。
移動回数・リセット回数・初期状態の推定費用はこの数に含めない。
各候補点は高々 `4d+3` 回の生成操作で到達できる（初期の `L` を含む）。
有理初期点では選択を厳密演算で実行できる。
任意の実初期点についての主張は正確な実数に関する数学的定理であり、
有限精度の測定や数値条件の良さまでは保証しない。

## 三段階の証明

### 1. 次数評価と曲線内補間

差 `H=P-Q` も総次数 `d` 以下である。`r=I(a)` とおく。
既存定理 `iterate_eq_closedOrbit` より、

`E^m(b)=(b₁+m I(b)², I(b)−(b₁+m I(b)²)³)`。

曲線 `C_s={(u,s−u³):u∈ℝ}` への単項式 `u^i v^j` の制限は
`u^i(s−u³)^j` となり、`u` についての次数は `i+3j≤3d`。
よって `H(u,s−u³)` の次数も `3d` 以下。
`s≠0` なら `b₁+m s²` は `m=0,…,3d` で互いに異なる。
この `3d+1` 点で零なら、根の個数の定理により曲線全体で零になる。

### 2. 異なる非零不変量を持つ曲線の選択

`t_n=a₁+n r²` は `r≠0` のもとで狭義増加。
`s_n=I(L(E^n(a)))=F_r(t_n)` と書くと

`F_r(x)=r−x³−x+(r−x³)³`。

立方関数の狭義増加性から `F_r` は狭義減少。
独立な微分検算でも `F'_r(x)=−1−3x²−9x²(r−x³)²<0`。
したがって `s_0,…,s_{d+1}` は相異なり、零は高々一つ。
非零のものから `d+1` 本を選べる。
曲線選択には `P` や `Q` の測定値を使わない。

初期 `I(z)=0` の処理を省くことはできない。
`z=(u,−u³)≠(0,0)` なら `u≠0` であり、

`I(Lz)=−u(u⁸+u²+1)≠0`。

よって最初の `L` 一回で上述の議論に入れる。
元の `E` はこの零不変量曲線を点ごとに固定する。
この前処理を省くと、全ての `E^m L E^n(z)` は同じ曲線に乗り、
次数3の非零多項式 `I−I(Lz)` を零多項式と区別できない。
初期の `E` 軌道も含めて高々一回の `L` を許しても、
次数6の `I(I−I(Lz))` が非零の消失多項式になる。
原点は両写像の共通不動点であり、次数1以上では決定不能。
次数0だけなら原点の一測定でも十分。

### 3. 曲線を横断する補間

任意の `u` を固定する。
`G_u(s)=H(u,s−u³)` の `s` に関する次数は高々 `d`。
段階1・2により、これは相異なる `d+1` 個の `s_n` で零である。
よって `G_u=0`。
任意の `(u,v)` に対し `s=v+u³` とすれば `H(u,v)=0`。
実数体上の多項式の外延性から、関数としてだけでなく多項式環で `H=0`。

## なぜ N(d) 点まで削減できるか

`V_d={P∈ℝ[u,v]:deg_total(P)≤d}` の単項式基底は
`{u^i v^j:i,j≥0,i+j≤d}`、次元は `N(d)`。
上述の有限候補点における評価行列を `A` とすると、三段階の証明は
`ker A={0}`、したがって `rank A=N(d)` を意味する。
行基底を選ぶと `N(d)` 行からなる非特異な正方行列が得られる。
その点だけで係数を一意に復元できる。

逆に `M<N(d)` 点での評価写像 `V_d→ℝ^M` は必ず非零核を持つ。
したがってこれより少ない正確な点評価で全多項式を決定することはできない。
適応的に測定点を選ぶ決定的手順も、零多項式への応答列を考えると、
そこで選ばれた `M` 点で消える非零多項式と区別できない。

この線形代数による最適値の証明は、今回の数学的証明として提示する。
最適値の次元計算と行選択まで全てをLeanで形式化したとの主張はしない。

## 証拠の区別

1. **既存Lean結果**: PR #146の全前進軌道での多項式決定・ザリスキー稠密性と、共通多項式保存量の定数性。
2. **既存Python結果**: 非零整数初期点 `(0,1),(1,−1),(−2,3)` の次数5、112候補点×21単項式の行列の階数21。原点は階数1。もとの検査は21回だけを測定する手順や任意次数の証明を提示するものではない。
3. **今回の一般次数結果**: 上記有限長方形と選択曲線による補間定理。Leanの実行結果・検査対象宣言は [検証記録](../verification/2026-11-17-siphon-finite-determination.md) に記載する。
4. **今回の最適化**: `N(d)` 点への削減と最小性は上記の線形代数による証明。
5. **今回の独立Python結果**: 次数0〜12、非零初期点9種、計117例。全例で `N(d)` 個の独立行を選び、非零小行列式を素数を法として再検算した。455件の単項式次数評価、原点の階数1、前処理省略の反例も検査した。有限例の成功を一般定理の代わりにはしない。

## 依存関係

| 今回の内容 | 上流の定義・宣言 | 利用方法 |
|---|---|---|
| 写像と不変量 | `Elastica.SiphonPolynomialE.I`, `E`, `iterate` | 固定ソースをimport |
| 閉形式の反復 | `iterate_eq_closedOrbit`, `closedOrbit` | 直接参照 |
| 線形写像 | `OrbitTrace.linearE` | 固定ソースをimport |
| 評価関数 | `SiphonCommonInvariant.readPoly` | 同一式を独立モジュールに定義、定義的に等しい |
| 出ていく不変量の単調性 | `outgoing_invariant_strictAnti` | 元はprivate。証明を公開補題 `outgoing_strictAnti` として再構成 |
| 零不変量からの脱出 | `zero_fibre_regular_after_turn` | 元はprivate。証明を `regular_after_turn` として再構成 |
| 曲線の多項式化 | `curvePolynomial` | 元はprivateかつ次数保証なし。明示的 `pathPoly` と次数上界を新規作成 |
| 有限点の根の剛性 | mathlib `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero` / 末尾 `'` 版 | 直接参照 |
| 平面での多項式一致 | mathlib `MvPolynomial.funext`, `totalDegree_sub` | 直接参照 |

新定理の証明は `polynomial_zero_of_regular_orbit` や既存のザリスキー稠密性定理を
ブラックボックスとして呼ばない。既存証明の二段階補間を有限個に置き換え、
次数・候補数・例外を明示している。

## 出典

- [PR #146](https://github.com/Sumuji-zkdwn/primitive-lean/pull/146)
- [固定ヘッドの既存証明](https://github.com/Sumuji-zkdwn/primitive-lean/blob/763d5d88d26d5fe8a8830c3b74f57461213ba4ed/lean/Research/SiphonCommonInvariant.lean)
- [研究記録](https://github.com/Sumuji-zkdwn/primitive-lean/blob/763d5d88d26d5fe8a8830c3b74f57461213ba4ed/docs/research/2026-11-17-siphon-operational-world.md)
- [既存Python検査](https://github.com/Sumuji-zkdwn/primitive-lean/blob/763d5d88d26d5fe8a8830c3b74f57461213ba4ed/tests/test_siphon_operational_world.py)
- [既存ヘッドの成功run 43982007551](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/43982007551)

この既存CI成功を、新規追加モジュールがGitHub Actionsで成功した証拠として扱わない。


## リポジトリ内の再現

```sh
python3 -m pip install sympy==1.14.0
python3 -B tools/check_siphon_finite_determination.py
python3 -B tools/verify_toolchain_modules.py --module Research.SiphonFiniteDetermination
```

Leanの環境は既存の `lean/lean-toolchain` と `lean/lake-manifest.json` を使用する。
必要なら最初に `cd lean && lake exe cache get` を実行する。
個別検証器は依存二モジュールを含むソース再コンパイルと全定理の公理監査を行う。
統合検証入口 `tools/verify.py --toolchain-modules-only` でも新モジュールは自動収集される。
Python証明書は `verification/siphon-finite-determination/python_certificates.json` に生成される。
専用CIは `.github/workflows/siphon-finite-determination.yml`。


## 2026-11-19 追記：最適値 \(N(d)\) と下界の Lean 証明

上の「この線形代数による最適値の証明は、今回の数学的証明として提示する。最適値の次元計算と行選択まで全てをLeanで形式化したとの主張はしない」を、独立モジュール `lean/Research/SiphonOptimalDetermination.lean`（11定理、`Research.SiphonFiniteDetermination` を import）で形式化した。

- `finrank_V`：総次数 \(d\) 以下の二変数実多項式の空間 \(V_d\)（mathlib の `restrictTotalDegree`）の次元は \(N(d)=(d+1)(d+2)/2\)（`card_expSet`：\(i+j\le d\) の指数を反対角線ごとに数える）。
- `exists_vanishing_of_card_lt`・`not_determining_of_card_lt`：\(N(d)\) 点未満の任意の集合に対し、そこで消える非零の次数 \(d\) 以下の多項式がある（評価写像の核）。したがって決定できない。
- `adaptive_not_determining`：次の測定点がそれまでの応答に依存する適応的手順でも、\(N(d)\) 回未満では零多項式と同じ応答列を返す非零多項式がある（本文の「零多項式への応答列」の議論）。
- `exists_optimal_determining_set`：任意の非零初期点から、既存定理の到達点 \(E^mLE^n\)（正則化した初期点）のうち**ちょうど** \(N(d)\) 点で次数 \(d\) 以下の全多項式が決まる。既存の決定集合での点評価は \(V_d\) の双対を張り（`Submodule.span_eq_top_of_ne_zero`）、その線形独立な部分族（`exists_linearIndependent'`）は双対の基底で大きさ \(N(d)\)。
- `minimum_is_N`：両方向をまとめた最小値の定理。`no_uniform_finite_cutoff`：次数を固定しなければ、どの有限点集合でも零多項式と区別できない非零多項式がある。点の選択は初期点に依存し、全初期点に共通の固定操作列は主張しない（本文と同じ）。

検証（2026-11-19、Lean `v4.36.0-rc2`）：`python3 -B tools/verify_toolchain_modules.py --module Research.SiphonOptimalDetermination` が依存3モジュールを含めて再コンパイルし、4モジュール88定理の公理監査に成功（使用公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内）。`lake env lean --trust=0` の単独コンパイルも警告なし。独立検算 `python -B tests/test_siphon_optimal_determination.py` は有理数の厳密計算で、5種の初期点・\(d\le3\) の到達点の評価行列の階数 \(N(d)\)、貪欲選択でちょうど \(N(d)\) 点、\(N(d)-1\) 点に対する非零消失多項式、適応的手順での応答列の一致を確認する。専用CI `.github/workflows/siphon-optimal-determination.yml`、統合検査の `siphon-optimal-determination` 段。

GitHub Actions：[run 44602956632](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/44602956632)（コミット `bc50534`）が成功（conclusion `success`）。
