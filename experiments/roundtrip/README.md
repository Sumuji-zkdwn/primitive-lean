# 初期465定理からの数学的往復操作（13往復）

初期の **465定理・509宣言** だけを出発点に、

> 形式的記述 → 自然言語による解釈 → 別の数学的表現への翻訳 → 元の体系への逆翻訳 → 再解釈

を13回行った記録です。各往復では直前の往復で得た構造を入力にし、使う初期定理と合成順序を毎回変えました。到達先は途中で現れた構造から選びました。得た命題はすべて Lean で検証済みです。追加した仮定と、Leanで検証していない解釈は §5 で区別します。

## 0. 初期465定理の原本の特定

| 項目 | 内容 |
|---|---|
| 範囲 | `lean/Elastica/` の24モジュール（**214定理**）と、`linear_input/lean_check/` の初期36原稿（`Design.lean` から `CoupledConsequences.inc` まで、**251定理**） |
| 宣言 | 465定理・42定義・2略記、合計 **509宣言** |
| 根拠 | `検証と再実行.md` 冒頭の「既存部分は465定理・509宣言」という記述。Kaggle記録 `evidence/kaggle/20261025T123036-471322/main-result.json` の `baseline_theorem_count = 465`・`baseline_declaration_count = 509`。同じ記録の全538宣言から追補29宣言を除くと、ちょうど509宣言（465 theorem）になる |
| 取り込みコミット | `eaa535b`（Elastica）、`acda8a1`・`486f3af`（線形入力）、いずれも2026-10-25 |
| 同一性 | Kaggle固定コミット `2e058f2` との差分はなし。記録されたSHA-256と60ファイルすべてが一致 |
| 区別した後続追加 | `MainResult.inc`・`GeneralMinimum.inc`・`SupportComposition.inc`・`QuarticClassification.inc`・`CurvatureRigidity.inc`（ここまでで494/538）、その後の `HistorySignature.inc` 以降の全追補（Chebyshev／F0／Bayes／F16／Galois／Kummer など）、`lean/OrbitTrace*.lean` |

`assemble.py` は毎回次の処理を行います。

1. 60ファイルを記録のSHA-256と照合する。
2. コメントを除いて宣言を数え直し、465/509 であることを確認する。
3. Elastica（ビルド済みライブラリとしてimport）と初期36原稿だけを結合する。
4. その後ろに往復原稿 `R01`〜`R13` を続ける。

後続の追補は一切読み込みません。したがって、ここで得た定理はすべて **初期509宣言＋Mathlib だけ** に依存します。

## 1. 検証

```
python3 -B experiments/roundtrip/assemble.py --compile
```

- Lean 4.30.0-rc2、Mathlib `5450b53e…`（リポジトリ固定の設定）。`--trust=0` で実行しました。
- 結果は [verification.json](verification.json) のとおりです。新規 **116宣言（107定理・9定義）**、エラー・警告0、`#print axioms` 116件はいずれも `propext`・`Classical.choice`・`Quot.sound` のみです。`sorry`・`axiom`・`native_decide` は使っていません。
- 実行環境はこのクラウドセッション（Linux）です。Mathlib は公式キャッシュを使い、`Elastica` はローカルでビルドしました。

## 2. 全体の経路

```
R1 観測束 ──補間──▶ R2 凹包絡 ──特殊化──▶ R3 カスプ破局 ──合成──▶ R4 一次相転移
                                                                  │
R13 変形しても消えない相転移 ◀── R12 Tsallisエネルギー ◀── R11 形式群則   │ 平滑化
      │（R4へ帰着）                                         ▲         ▼
      └──────────────────────────── R10 相似不変量 ◀── R9 曲線   R5 Gibbs自由エネルギー
                                                     ▲            │ 同じ四次関数
                                   R8 キンク角(停留) ◀── R7 ソリトン ◀── R6 力学（円弧）
```

## 3. 各往復の記録

各往復について、入力、解釈と翻訳先、Lean に戻した命題（逆翻訳）、再解釈、そして何が保存され・失われ・新たに現れたか（保存／喪失／新出）を記します。

### R1 観測束 → Lagrange補間 → 観測束（`R01_Interpolation.inc`）
- **入力**: `LinearInputObservation.energy A X u z = A z − u·X z`。初期定理の `recover_coordinate`、`recover_zero_input_energy`、`two_inputs_iff_pair`。
- **解釈と翻訳先**: 状態 `z` を固定すると、入力 `u` についての1次多項式になる。2入力での観測は2点評価であり、行列は Vandermonde 行列（線形代数・補間）になる。
- **逆翻訳**: `obsMatrix_eq_vandermonde`、`det_obsMatrix`（det = u − v）、`energy_interpolate`（任意の第3入力の観測は2観測のアフィン結合）、`recover_by_inverse`（復元は逆行列そのもの）。初期定理 `recover_zero_input_energy` は「w = 0 での補間」として再導出した。
- **再解釈**: 初期定理の「2入力で十分」は、次数1の補間の一意性と同じことである。
- **保存／喪失／新出**: 復元可能性は保存。状態空間 `S` の構造は失われる。新たに、入力についての多項式構造と、1入力では決して分離できないこと（`single_input_not_injective`）が現れた。

### R2 補間直線 → 下側包絡（凸解析） → 単調性定理（`R02_ValueFunction.inc`）
- **入力**: R1 の「各状態は u のアフィン直線」。
- **翻訳先**: 直線族の下側包絡である最小値関数。凹関数になり、`−X(z_u)` が超勾配になる。
- **逆翻訳**: `supergradient`、`observable_monotone`（任意の `S`・任意の観測量 `X` で成り立つ）、`value_concave`。初期定理 `minimizer_monotone` は、S = ℝ・X = id の場合として再証明した（`minimizer_monotone_from_envelope`）。
- **再解釈**: 最小点の単調性は、凹関数の超勾配が単調であることそのものである。
- **保存／喪失／新出**: 単調性は保存。最小点の存在は失われる（仮定として扱う）。新たに、凹性の証明に中間入力での最小性が不要であることが分かった。

### R3 凹包絡 × 設計エネルギー → カスプ破局 → 設計（`R03_Cusp.inc`）
- **入力**: R2 の枠組みに初期の `LinearInputDesign.E` を入れる。`design_is_pencil` により、これは観測量 `x` の観測束になる。
- **翻訳先**: `f = λx⁴/4 + r x²/2 − u x` はカスプの標準形である（破局理論）。
- **逆翻訳**:
  - `metastable_local_not_global`: `3λa² + r > 0 > λa² + r` の帯では、局所最小だが大域最小ではない。
  - `maxwell_input_zero`・`maxwell_two_global_minimizers`: 余裕0（Maxwell集合）では u = 0 となり、±a が同時に大域最小になる。
  - `fold_discriminant`・`discriminant_fold`: 折り目は判別式 4r³ + 27λu² = 0 と一致する。
  - `input_chebyshev`: (λ, r) = (4, −3) では input が Chebyshev 多項式 T₃ になる。
- **再解釈**: 初期の「大域最小の証明書」λa² + r ≥ 0 は、局所安定条件 3λa² + r ≥ 0 より厳しい。両者の差が準安定帯である。
- **保存／喪失／新出**: 大域最小の判定は保存。y 座標は失われる（y = √2x に従属する）。新たに準安定帯、Maxwell集合、判別式、T₃ が現れた。T₃ は後続追補（Chebyshev系）と独立に、初期定義だけから再び現れたことになる。

### R4 Maxwell集合 × 超勾配 → 一次相転移（Landau理論） → 設計（`R04_PhaseTransition.inc`）
- **入力**: R2 の超勾配と R3 の二重最小点を、この順で合成する。
- **翻訳先**: 秩序変数の跳びと、自由エネルギーの角。
- **逆翻訳**:
  - `not_differentiableAt_of_two_minimizers`: 一般の観測束で、観測値の異なる2最小点があれば値関数は微分不能になる。
  - 実際の下限 `value λ r u = ⨅ E` を、初期の `coercive_lower_bound` を使って定義した。
  - `value_not_differentiableAt_zero`: λ > 0 > r なら u = 0 で微分不能。
  - `order_parameter_jump`: u > 0 の最小点は x ≥ √(−r/λ)、u < 0 の最小点は x ≤ −√(−r/λ)。
- **保存／喪失／新出**: 最小点の順序は保存。滑らかさは失われる。新たに相転移と、2√(−r/λ) 以上の跳びが現れた。

### R5 角 → Gibbs自由エネルギー（統計力学） → 観測束（`R05_GibbsSmoothing.inc`）
- **入力**: R4 の角。順序反転は初期の `exp_neg_mul_le_exp_neg_mul_iff` を使う。
- **翻訳先**: −β⁻¹ log Σ e^{−βE}。
- **逆翻訳**:
  - `freeEnergy_le_min`・`min_sub_log_two_le_freeEnergy`: min − log2/β ≤ F ≤ min（Laplace型の評価）。
  - `freeEnergy_maxwell`: F = E₀ − β⁻¹ log(2 cosh βau)。
  - `hasDerivAt_freeEnergy_maxwell`: 傾きは −a·tanh(βau)。
  - `susceptibility_at_zero`: u = 0 での感受率は βa²。
  - `tendsto_freeEnergy_maxwell`: β → ∞ で角に収束する。
  - `limit_not_differentiableAt`: 極限は R4 の定理で微分不能になる。
- **保存／喪失／新出**: 最小値は β → ∞ の極限として保存。角は有限の β で失われる。新たに tanh 型の応答と、発散する感受率が現れた。

### R6 カスプのポテンシャル → 弧長を時間とする Newton 力学 → 弾性曲線の円弧（`R06_CircleMechanics.inc`）
- **入力**: R3〜R5 で使った同じ四次関数。初期の `CurvatureBridge.energy_shear` によれば、曲率方程式の位相エネルギーは `E(1/2, −σ/k, u, κ, κ′+√2κ)` である。
- **翻訳先**: 曲率 κ を粒子、弧長 s を時間とみる。
- **逆翻訳**:
  - `phase_energy_split`: 位相エネルギー = 運動エネルギー + `potential (1/2) (−σ/k) u`。
  - `circle_iff_input`: 一定曲率 a が解であることは、u = input(1/2, −σ/k, a) と同値。
  - `pressure_circle_iff`: 圧力方程式では p/k = input になる。
  - `expansion_around_circle`: 円弧のまわりの厳密展開（打ち切りなし）。線形係数は R3 の 3λa² + r に一致する。
  - `metastable_circle_example`（k = σ = a = 1）: 振動的には安定だが、位相ポテンシャルの大域最小ではない円弧の具体例。
- **保存／喪失／新出**: 四次関数そのものは保存。「全平面での最小化」は「保存則つきの運動」に変わる。新たに、圧力が入力 u の役割を果たすことが分かった。

### R7 二重井戸 → セパラトリクス（可積分系のソリトン） → 曲率（`R07_Soliton.inc`）
- **入力**: R6 で u = 0、σ/k = c² > 0 とした二重井戸（κ = 0 が山頂）。
- **翻訳先**: 山頂を通るホモクリニック軌道 κ = 2c·sech(cs)。
- **逆翻訳**:
  - `soliton_curvature_equation`: 初期の曲率方程式の厳密解（σ = kc²）。
  - `soliton_phase_energy`: 位相エネルギーは恒等的に0（山頂の値）。
  - `soliton_phase_flow`: 初期の `phase_hasDerivAt` がそのまま適用できる。
  - `soliton_tendsto_zero`: s → ∞ で 0 に減衰する。
- **保存／喪失／新出**: 方程式は保存。有限区間の境界条件は失われる（無限長）。新たに、閉じた形の非自明解と、エネルギー0の分離線が現れた。

### R8 ソリトン曲率 → 振り子のキンク（定常 sine-Gordon） → 停留する弾性曲線（`R08_KinkAngle.inc`）
- **入力**: R7 の κ を積分する。
- **翻訳先**: θ = 4 arctan e^{cs}。θ″ = c² sin θ のキンク解である。
- **逆翻訳**:
  - `curvature_kink`: 初期の `curvature` で見た θ の曲率が R7 のソリトンに一致する。
  - `cos_kink`・`sin_kink`: cos θ・sin θ の閉じた形。
  - `kink_angleEquation`: 初期の角度方程式で λ = −kc²、μ = 0。
  - **`kink_stationary`**: 初期の `stationary_of_angleEquation` と `stationary_iff_firstVariation` を通して、このキンクが二次密度の実際の弾性エネルギーについて、任意の区間 [0, ℓ] で `Elastica.Stationary` であることを示した。仮定として置いたのではなく、初期の変分論から導いている。
  - `kink_first_integral`: 初期の第一積分の値は kc² であり、R7 の曲率方程式に必要だった σ と一致する。初期理論の2系統（`Equations` と `CurvatureBridge`）の整合性検査にもなっている。
- **保存／喪失／新出**: 曲率は保存。角度の持ち上げは定数分だけ任意性がある。新たに、初期体系の中で初めての **直線・円以外の明示的な停留曲線** が得られた（リポジトリの Lean 全体にも cosh・arctan を含む例はない）。

### R9 キンク角 → 平面曲線（微分幾何・静力学） → モーメント則と自己交差（`R09_LoopCurve.inc`）
- **入力**: R8 の θ を、初期の `xCoord`・`yCoord` で再構成する。
- **逆翻訳**:
  - `moment_balance`（一般定理）: 初期の角度方程式を満たす任意の θ について、kκ + λy − μx は一定（曲げモーメント = 端の力のモーメント）。
  - `xCoord_kink`・`yCoord_kink`: x = s − (2/c) tanh(cs)、y = (2/c) sech(cs)。
  - `soliton_eq_height`: 曲率は高さに比例する（κ = c²y）。`moment_constant_kink` で、一般則からも同じ結果になることを確かめた。
  - **`kink_self_intersection`**: 1 < s* < 2 で γ(s*) = γ(−s*)。数値では s* ≈ 1.9150、交点の高さは y ≈ 0.5768。
- **保存／喪失／新出**: エネルギーと方程式は保存。曲線が単純曲線であることは失われる（埋め込みではなく、はめ込みにすぎない）。新たに、高さと曲率の比例関係（Bernoulli型の法則）と、トポロジー的な交差が現れた。

### R10 曲線族 → 相似群 → 計量的不変量と位相的不変量（`R10_ScalingInvariants.inc`）
- **入力**: R9 の曲線族 γ_c。初期の `curvature_angle_scaling`・`energy_scaling_quadratic` を使う。
- **逆翻訳**:
  - `kink_scaling`: θ_c(s) = θ₁(s/(1/c))。
  - `soliton_scaling_from_baseline`: 初期の曲率スケーリング則で読んだ曲率の変換。
  - `energy_kink`: 区間エネルギーは 2kc·tanh(cℓ)。
  - `energy_scaling_baseline`・`energy_routes_agree`: 明示積分と初期のスケーリング定理という2経路が一致する。
  - `energy_kink_lt`: エネルギーは 2kc 未満。
  - `kink_tendsto_atTop`・`kink_tendsto_atBot`: 接線の全回転角はどの c > 0 でも 2π。
- **保存／喪失／新出**: 形は保存。大きさは失われる。新たに、エネルギーは c に比例する（計量的）一方で、回転角 2π は c によらない（位相的）、という二層構造が現れた。

### R11 べき乗スケーリング → 乗法形式群則（代数） → powerLog（`R11_FormalGroup.inc`）
- **入力**: R10 の「拡大でエネルギーがべき倍になる」性質と、初期の `energy_scaling_of_homogeneous`（倍率 a^{1−m}）。
- **翻訳先**: 拡大の合成は乗法。相対変化 ρ(a) = a^p − 1（p = 1 − m）は ρ(ab) = ρ(a) ⊕₁ ρ(b) を満たす。
- **逆翻訳**:
  - `fgl` の結合律・可換律・単位元・逆元を示した。`one_add_mul_fgl` で、x ↦ 1 + px が ⊕ₚ を乗法に共役させることを示した。
  - `powerLog_hom`: 初期の `powerLog_mul` は (ℝ_{>0}, ·) → (ℝ, ⊕ₚ) の準同型である。
  - `energy_relative_change`・`energy_composed_scaling`: エネルギーの相対変化。
  - `quadratic_loss_fraction`・`loss_fraction_union`: 二次弾性では、エネルギーの損失率 1 − 1/a = powerLog(−1, a) が独立事象の和事象の確率 P(A∪B) = P(A) + P(B) − P(A)P(B) と同じ法則で合成される。
- **保存／喪失／新出**: 合成の構造は保存。幾何は失われる。新たに形式群と、確率の和事象との対応が現れた。

### R12 形式群 → Tsallis型の非加法エネルギー → Gibbs重み（`R12_TsallisEnergy.inc`）
- **入力**: R11 の ⊕ₚ と R5 の Gibbs 重み。
- **翻訳先**: E_p = −powerLog p (e^{−βE})/β = (1 − e^{−pβE})/(pβ)（非示量統計）。
- **逆翻訳**:
  - `deform_eq`: E_p の閉じた形。
  - `deform_add`: E_p(e₁ + e₂) = E_p(e₁) ⊕_{−pβ} E_p(e₂)。
  - `deform_energy_split`: 初期の `powerLog_exponentialWeight_split` は、この法則を区間分割について述べたものそのものである（初期定理に戻ってきた）。
  - `deform_subadditive`: pβ > 0 で劣加法的。
  - `deform_order`: 曲線の順序は保たれる（初期の `energy_le_iff_powerLog_exponentialWeight_le`）。
  - `deform_tendsto`: p → 0 で加法的エネルギーに戻る（初期の `tendsto_powerLog_exponentialWeight_zero`）。
- **保存／喪失／新出**: 順序は保存。加法性は失われる。新たに、非加法性の大きさが変形パラメータで決まる合成則（⊕_{−pβ}）が現れた。

### R13 変形エネルギー → 順序の不変量・滑らかな共役 → Maxwell の角（`R13_DeformedTransition.inc`）
- **入力**: R12 の「変形は順序を保ち、加法性を壊す」と、R4 の角を合成する。
- **逆翻訳**:
  - `deform_strictMono`: 変形は狭義単調増加。
  - `deform_left_inverse`: 滑らかな左逆写像がある。
  - `not_differentiableAt_deform`: どの変形でも角は消えない。
  - `deform_value_is_min`: 変形した値関数は、変形した問題の最小値になる。
  - **`deformed_maxwell_corner`**: すべての p と β ≠ 0 について、初期の設計エネルギーの変形値関数は u = 0 で微分不能。
- **再解釈**: 相転移は「順序」の構造に属し、「加法」の構造には属さない。この往復で R4 に戻り、輪が閉じた。
- **保存／喪失／新出**: 順序と角は保存。加法性は失われる。新たに、相転移が変形に対して不変であることが分かった。

## 4. 使った初期定理と合成順序の変化

| 往復 | 主に使った初期宣言 | 合成 |
|---|---|---|
| R1 | `LinearInputObservation.energy`（再導出：`recover_zero_input_energy`） | 単独 |
| R2 | `energy`、`minimizer_monotone`（再導出） | R1 → |
| R3 | `Design.E/f/input/GlobalMin`、`globalMin_iff_margin`、`scalar_gap` | R2 ∘ Design |
| R4 | `coercive_lower_bound`、`lowerBoundConstant`、`globalMin_iff_margin` | R2 ∘ R3（超勾配を先に） |
| R5 | `exp_neg_mul_le_exp_neg_mul_iff` | R4 を極限として |
| R6 | `energy_shear`、`Calculus.potential`、`Design.input`、`globalMin_iff_margin` | R3 ∘ CurvatureBridge |
| R7 | `energy_shear`、`phase_hasDerivAt`、`gx`、`gy` | R6 の特殊値 |
| R8 | `curvature`、`stationary_of_angleEquation`、`stationary_iff_firstVariation`、`quadratic_density_hasDerivAt` | R7 を積分してから変分論へ（曲率 → 角 → 停留） |
| R9 | `xCoord`、`yCoord`、`hasDerivAt_xCoord`、`hasDerivAt_yCoord` | R8 を積分（角 → 曲線） |
| R10 | `curvature_angle_scaling`、`energy_scaling_quadratic` | R9 にスケーリングを作用 |
| R11 | `energy_scaling_of_homogeneous`、`energy_scaling_quadratic`、`powerLog_mul` | R10 の倍率を代数化 |
| R12 | `powerLog_exponentialWeight_split`、`energy_le_iff_powerLog_exponentialWeight_le`、`tendsto_powerLog_exponentialWeight_zero` | R11 ∘ R5 |
| R13 | `strictAnti_powerLog_exp_neg_mul`、`exists_global_minimum`、`powerLog_zero` | R12 ∘ R4（R2・R3 を経由） |

R6〜R9 では、合成の向きを 曲率 → 角 → 停留性 → 座標 と、初期体系の通常の導出（変分 → 角度方程式 → 曲率方程式）とは逆向きに辿りました。

## 5. 検証済み・追加仮定・未検証解釈の区別

- **Lean 検証済み**: §3 で名前を挙げたすべての定理（116宣言）。初期509宣言と Mathlib のみに依存します。
- **追加した仮定（定理の仮定として明示）**:
  - R2: 最小点の存在（`IsMinimizer` を仮定。R4・R13 では初期の `exists_global_minimum` で補った）。
  - R5: 状態空間を Maxwell 点の2状態に制限した。連続な設計エネルギーの Gibbs 測度ではない。
  - R7〜R10: 二次密度 kq²/2、σ = kc² > 0（R10 の一部は c > 0、k > 0）。
  - R9: 自己交差は c = 1 の場合のみ。他の c はスケーリングで移るが、それは Lean では示していない。
  - R12: pβ > 0（劣加法性のみ）。
- **Lean で検証していない解釈**:
  - R3: f をカスプ破局の標準形とみること。
  - R4: Landau の一次相転移という読み。
  - R7: 2c·sech(cs) を mKdV ソリトンの形とみること。
  - R8: θ を sine-Gordon のキンクとみること。
  - R9: 曲線を「単一ループのソリトン型エラスティカ」と呼ぶこと、および Bernoulli 型の法則という名前。
  - R11: 確率の和事象との類比。
  - R12: Tsallis（q-対数）という名前付け。
  - 各段の「保存／喪失／新出」の判定は、定理の形から読み取った記述であり、それ自体は形式化していません。

## 6. 全体の結果と最も興味深い到達点

- 初期体系の **静的な「大域最小の設計証明書」**（`LinearInputDesign`）から出発し、凸解析・破局理論・統計力学を経て一次相転移に至りました（R1〜R5）。さらに同じ四次関数を曲率の位相ポテンシャルとして読み替えることで、弾性曲線へ戻りました（R6）。
- **最も興味深い到達点**は R7〜R9 です。設計証明書に現れた四次関数の分離線をたどると、初期体系の変分定理そのもので停留性が保証される明示解が得られました。
  - 曲率は 2c·sech(cs)、角は 4 arctan(e^{cs})。
  - 曲線は (s − (2/c)tanh(cs), (2/c)sech(cs)) で、自分自身と交差します。
  - 曲率は高さに比例します（κ = c²y）。
  - 初期体系に明示的な停留解は直線と円しかなく、これは初めての非自明な停留曲線です。
  - 第一積分の値 σ = kc² が、別系統の曲率方程式に必要な値と一致することも Lean で確かめました。
- 後半（R11〜R13）では、初期体系に既にある `powerLog` の積公式が乗法形式群則であることが分かりました。その結果、Tsallis 型の変形エネルギーが区間分割で非加法的に合成されること、それでも R4 の相転移はあらゆる変形で消えないことが示され、輪が閉じました。

## ファイル

- `assemble.py`: 原本照合・件数再計数・結合・コンパイル・記録
- `R01_*.inc` 〜 `R13_*.inc`: 各往復の Lean 原稿
- `verification.json`: 実行結果（再生成されます）
- `declarations.json`: 新規116宣言の一覧
- `Joint.lean`・`build.log`: 生成物（Git には入れません）
