import Mathlib

/-!
# Rotating line projections

A planar vector is projected, in order, onto lines whose angles advance by
prescribed steps `Δ 0, Δ 1, …`.  Each projection is idempotent (an F0-style
forgetting map `K ∘ K = K`), but consecutive projections onto different lines do
not commute.

Proved here, directly from the definitions:

* the exact state after `k` projections: amplitude `∏ cos (Δ i)` on the current
  line;
* the uniform half turn `Δ i = π / n`: final state `(-(cos (π / n)) ^ n, 0)`,
  with the exact values for `n = 2, 3, 4` and the full four-step trace;
* the explicit bound `1 - π² / (2n) ≤ cos (π / n) ^ n ≤ 1` (`n ≥ 3`) and the
  limit `cos (π / n) ^ n → 1`;
* a discrete bending bound `1 - (∑ Δ i ^ 2) / 2 ≤ ∏ cos (Δ i)` for `|Δ i| ≤ 1`;
* equal steps maximise the surviving amplitude for a fixed total turn
  (steps in `[-π/2, π/2]`);
* the whole composite absorbs its first projection, so inputs identified by the
  first projection stay identified: a coordinate can reappear, a forgotten
  distinction cannot;
* two explicit failures: non-commutation, and the composite is not idempotent.

Scope: only the total turn of the line angle is constrained.  Nothing here fixes
end positions, so this is not the fixed-boundary elastica problem, and the
continuum statement relating `∑ Δ i ^ 2` to `∫ κ² ds` is not formalised.
-/

noncomputable section
namespace RotatingProjections

open Real Finset Filter Topology

/-- Vectors of the plane, as pairs of reals. -/
abbrev Vec := ℝ × ℝ

/-- Component of `v` along the unit direction of angle `θ`. -/
def coeff (θ : ℝ) (v : Vec) : ℝ := v.1 * cos θ + v.2 * sin θ

/-- Orthogonal projection onto the line through the origin of angle `θ`. -/
def proj (θ : ℝ) (v : Vec) : Vec := (coeff θ v * cos θ, coeff θ v * sin θ)

/-- Angle of the `k`-th line: start angle plus the first `k` steps. -/
def line (Δ : ℕ → ℝ) (θ₀ : ℝ) (k : ℕ) : ℝ := θ₀ + ∑ i ∈ range k, Δ i

/-- Project successively onto lines `1, …, k`. -/
def run (Δ : ℕ → ℝ) (θ₀ : ℝ) : ℕ → Vec → Vec
  | 0, v => v
  | k + 1, v => proj (line Δ θ₀ (k + 1)) (run Δ θ₀ k v)

/-- The uniform step making `n` steps add up to a half turn. -/
def halfStep (n : ℕ) : ℕ → ℝ := fun _ => π / n

theorem coeff_proj (θ : ℝ) (v : Vec) : coeff θ (proj θ v) = coeff θ v := by
  have h := sin_sq_add_cos_sq θ
  show (coeff θ v * cos θ) * cos θ + (coeff θ v * sin θ) * sin θ = coeff θ v
  linear_combination (coeff θ v) * h

/-- Each projection is an idempotent forgetting map, in the same form as the
F0 condition `∀ x, K (K x) = K x`. -/
theorem proj_idempotent (θ : ℝ) (v : Vec) : proj θ (proj θ v) = proj θ v := by
  have h := coeff_proj θ v
  simp only [proj] at h ⊢
  rw [h]

theorem proj_scaled_dir (θ φ r : ℝ) :
    proj θ (r * cos φ, r * sin φ) =
      (r * cos (θ - φ) * cos θ, r * cos (θ - φ) * sin θ) := by
  have h : coeff θ (r * cos φ, r * sin φ) = r * cos (θ - φ) := by
    simp only [coeff, cos_sub]
    ring
  simp only [proj, h]

theorem line_succ (Δ : ℕ → ℝ) (θ₀ : ℝ) (k : ℕ) :
    line Δ θ₀ (k + 1) = line Δ θ₀ k + Δ k := by
  simp only [line, sum_range_succ]
  ring

theorem line_one (Δ : ℕ → ℝ) (θ₀ : ℝ) : line Δ θ₀ 1 = θ₀ + Δ 0 := by
  simp [line]

/-- Exact state after `k` projections, starting from length `r` on the
initial line: the amplitude is multiplied by `cos (Δ i)` at every step. -/
theorem run_scaled_dir (Δ : ℕ → ℝ) (θ₀ r : ℝ) (k : ℕ) :
    run Δ θ₀ k (r * cos θ₀, r * sin θ₀) =
      (r * (∏ i ∈ range k, cos (Δ i)) * cos (line Δ θ₀ k),
        r * (∏ i ∈ range k, cos (Δ i)) * sin (line Δ θ₀ k)) := by
  induction k with
  | zero => simp [run, line]
  | succ k ih =>
    have hstep : line Δ θ₀ (k + 1) - line Δ θ₀ k = Δ k := by
      rw [line_succ]; ring
    rw [run, ih]
    have h := proj_scaled_dir (line Δ θ₀ (k + 1)) (line Δ θ₀ k)
      (r * ∏ i ∈ range k, cos (Δ i))
    simp only [mul_assoc] at h ⊢
    rw [h, hstep, prod_range_succ]
    simp only [mul_assoc, mul_comm (cos (Δ k))]

/-- Unit-length version of `run_scaled_dir`. -/
theorem run_dir (Δ : ℕ → ℝ) (θ₀ : ℝ) (k : ℕ) :
    run Δ θ₀ k (cos θ₀, sin θ₀) =
      ((∏ i ∈ range k, cos (Δ i)) * cos (line Δ θ₀ k),
        (∏ i ∈ range k, cos (Δ i)) * sin (line Δ θ₀ k)) := by
  simpa using run_scaled_dir Δ θ₀ 1 k

theorem line_halfStep (n k : ℕ) : line (halfStep n) 0 k = k * (π / n) := by
  simp [line, halfStep]

theorem line_halfStep_self {n : ℕ} (hn : n ≠ 0) : line (halfStep n) 0 n = π := by
  rw [line_halfStep]
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

theorem prod_halfStep (n k : ℕ) :
    ∏ i ∈ range k, cos (halfStep n i) = cos (π / n) ^ k := by
  simp [halfStep]

/-- State after `k` steps of the uniform half turn, from `(r, 0)`. -/
theorem run_halfStep_scaled (n k : ℕ) (r : ℝ) :
    run (halfStep n) 0 k (r, 0) =
      (r * cos (π / n) ^ k * cos (k * (π / n)),
        r * cos (π / n) ^ k * sin (k * (π / n))) := by
  have h := run_scaled_dir (halfStep n) 0 r k
  simp only [cos_zero, sin_zero, mul_one, mul_zero] at h
  rw [h, prod_halfStep, line_halfStep]

/-- **Uniform half turn.**  After `n` projections onto lines advanced by
`π / n`, the unit vector `(1, 0)` becomes `(-(cos (π / n)) ^ n, 0)`. -/
theorem run_halfStep_final {n : ℕ} (hn : n ≠ 0) :
    run (halfStep n) 0 n (1, 0) = (-(cos (π / n) ^ n), 0) := by
  have h := run_dir (halfStep n) 0 n
  simp only [cos_zero, sin_zero] at h
  rw [h, prod_halfStep, line_halfStep_self hn, cos_pi, sin_pi]
  simp

/-- Two quarter-turn projections annihilate the vector. -/
theorem halfTurn_two : run (halfStep 2) 0 2 (1, 0) = (0, 0) := by
  rw [run_halfStep_final (by norm_num)]
  simp

/-- Three projections leave one eighth, reversed. -/
theorem halfTurn_three : run (halfStep 3) 0 3 (1, 0) = (-(1 / 8), 0) := by
  rw [run_halfStep_final (by norm_num)]
  norm_num [cos_pi_div_three]

theorem cos_pi_div_four_sq : cos (π / 4) ^ 2 = 1 / 2 := by
  rw [cos_pi_div_four, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Four projections leave one quarter, reversed. -/
theorem halfTurn_four : run (halfStep 4) 0 4 (1, 0) = (-(1 / 4), 0) := by
  rw [run_halfStep_final (by norm_num)]
  have h : cos (π / 4) ^ 4 = (cos (π / 4) ^ 2) ^ 2 := by ring
  have e : π / ((4 : ℕ) : ℝ) = π / 4 := by push_cast; ring
  rw [e, h, cos_pi_div_four_sq]
  norm_num

/-- The complete four-step trace
`(1,0) → (½,½) → (0,½) → (-¼,¼) → (-¼,0)`. -/
theorem halfTurn_four_trace :
    run (halfStep 4) 0 1 (1, 0) = (1 / 2, 1 / 2) ∧
    run (halfStep 4) 0 2 (1, 0) = (0, 1 / 2) ∧
    run (halfStep 4) 0 3 (1, 0) = (-(1 / 4), 1 / 4) ∧
    run (halfStep 4) 0 4 (1, 0) = (-(1 / 4), 0) := by
  have hc := cos_pi_div_four_sq
  have hs : sin (π / 4) = cos (π / 4) := by rw [sin_pi_div_four, cos_pi_div_four]
  have h2 : ((2 : ℕ) : ℝ) * (π / ((4 : ℕ) : ℝ)) = π / 2 := by push_cast; ring
  have h3 : ((3 : ℕ) : ℝ) * (π / ((4 : ℕ) : ℝ)) = π - π / 4 := by push_cast; ring
  have h1 : ((1 : ℕ) : ℝ) * (π / ((4 : ℕ) : ℝ)) = π / 4 := by push_cast; ring
  have h4 : π / ((4 : ℕ) : ℝ) = π / 4 := by push_cast; ring
  refine ⟨?_, ?_, ?_, halfTurn_four⟩
  · have h := run_halfStep_scaled 4 1 1
    rw [h1, h4] at h
    rw [h, hs]
    refine Prod.ext ?_ ?_ <;> simp only [one_mul, pow_one] <;> linear_combination hc
  · have h := run_halfStep_scaled 4 2 1
    rw [h2, h4] at h
    rw [h, cos_pi_div_two, sin_pi_div_two, hc]
    norm_num
  · have h := run_halfStep_scaled 4 3 1
    rw [h3, h4] at h
    rw [h, cos_pi_sub, sin_pi_sub, hs]
    have e : cos (π / 4) ^ 3 * cos (π / 4) = (cos (π / 4) ^ 2) ^ 2 := by ring
    refine Prod.ext ?_ ?_
    · simp only [one_mul, mul_neg, e, hc]; norm_num
    · simp only [one_mul, e, hc]; norm_num

/-- **Coordinate reappearance.**  In the four-step half turn the first
coordinate is `1`, vanishes after two projections, and is `-1/4` at the end. -/
theorem halfTurn_four_coordinate_reappears :
    (run (halfStep 4) 0 0 (1, 0)).1 = 1 ∧
    (run (halfStep 4) 0 2 (1, 0)).1 = 0 ∧
    (run (halfStep 4) 0 4 (1, 0)).1 = -(1 / 4) := by
  obtain ⟨-, h2, -, h4⟩ := halfTurn_four_trace
  refine ⟨rfl, ?_, ?_⟩
  · rw [h2]
  · rw [h4]

theorem cos_pi_div_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ cos (π / n) := by
  apply cos_nonneg_of_mem_Icc
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  constructor
  · have : 0 ≤ π / n := div_nonneg pi_pos.le hpos.le
    linarith [pi_pos]
  · rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [pi_pos]

/-- **Explicit bound** for the uniform half turn: the lost fraction of the
length is at most `π² / (2n)`. -/
theorem halfTurn_bounds {n : ℕ} (hn : 3 ≤ n) :
    1 - π ^ 2 / (2 * n) ≤ cos (π / n) ^ n ∧ cos (π / n) ^ n ≤ 1 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have hc0 := cos_pi_div_nonneg (by omega : 2 ≤ n)
  refine ⟨?_, pow_le_one₀ hc0 (cos_le_one _)⟩
  set x : ℝ := π / n with hx
  have hx0 : 0 ≤ x := div_nonneg pi_pos.le hpos.le
  have hx1 : x ≤ 4 / 3 := by
    rw [hx, div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 3)]
    nlinarith [pi_le_four]
  have hsq : x ^ 2 ≤ 16 / 9 := by nlinarith
  have hbase : 0 ≤ 1 + -(x ^ 2 / 2) := by linarith
  have hcos : 1 + -(x ^ 2 / 2) ≤ cos x := by
    have := one_sub_sq_div_two_le_cos (x := x); linarith
  have hbern := one_add_mul_le_pow (a := -(x ^ 2 / 2)) (by linarith) n
  have hpow := pow_le_pow_left₀ hbase hcos n
  have hlin : (n : ℝ) * -(x ^ 2 / 2) = -(π ^ 2 / (2 * n)) := by
    rw [hx]; field_simp
  linarith

/-- **Limit.**  Cutting the half turn ever finer keeps the whole length. -/
theorem halfTurn_tendsto_one :
    Tendsto (fun n : ℕ => cos (π / n) ^ n) atTop (𝓝 1) := by
  have hlow : Tendsto (fun n : ℕ => 1 - (π ^ 2 / 2) / n) atTop (𝓝 1) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (π ^ 2 / 2)).const_sub (1 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have h := (halfTurn_bounds hn).1
    have e : π ^ 2 / (2 * n) = (π ^ 2 / 2) / n := by ring
    rw [e] at h
    exact h
  · filter_upwards [eventually_ge_atTop 3] with n hn
    exact (halfTurn_bounds hn).2

/-- `∏ (1 - a i) ≥ 1 - ∑ a i` for weights in `[0, 1]`. -/
theorem one_sub_sum_le_prod (a : ℕ → ℝ) (k : ℕ)
    (ha : ∀ i ∈ range k, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∑ i ∈ range k, a i ≤ ∏ i ∈ range k, (1 - a i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ha' : ∀ i ∈ range k, 0 ≤ a i ∧ a i ≤ 1 := fun i hi =>
      ha i (mem_range.mpr (Nat.lt_succ_of_lt (mem_range.mp hi)))
    have hk := ha k (mem_range.mpr (Nat.lt_succ_self k))
    have hP0 : 0 ≤ ∏ i ∈ range k, (1 - a i) :=
      prod_nonneg fun i hi => by linarith [(ha' i hi).2]
    have hP1 : ∏ i ∈ range k, (1 - a i) ≤ 1 :=
      prod_le_one (fun i hi => by linarith [(ha' i hi).2])
        (fun i hi => by linarith [(ha' i hi).1])
    have := ih ha'
    rw [sum_range_succ, prod_range_succ]
    nlinarith [hk.1, hk.2]

/-- **Discrete bending bound.**  For steps with `|Δ i| ≤ 1`, the surviving
amplitude is at least `1 - (∑ Δ i ^ 2) / 2`. -/
theorem bending_lower_bound (Δ : ℕ → ℝ) (k : ℕ) (hΔ : ∀ i ∈ range k, |Δ i| ≤ 1) :
    1 - (∑ i ∈ range k, Δ i ^ 2) / 2 ≤ ∏ i ∈ range k, cos (Δ i) := by
  have hsq : ∀ i ∈ range k, Δ i ^ 2 ≤ 1 := fun i hi => by
    have := hΔ i hi
    nlinarith [abs_nonneg (Δ i), sq_abs (Δ i)]
  have hw : ∀ i ∈ range k, 0 ≤ Δ i ^ 2 / 2 ∧ Δ i ^ 2 / 2 ≤ 1 := fun i hi =>
    ⟨by positivity, by linarith [hsq i hi]⟩
  have h1 := one_sub_sum_le_prod (fun i => Δ i ^ 2 / 2) k hw
  have h2 : ∏ i ∈ range k, (1 - Δ i ^ 2 / 2) ≤ ∏ i ∈ range k, cos (Δ i) :=
    prod_le_prod (fun i hi => by linarith [hsq i hi])
      (fun i _ => one_sub_sq_div_two_le_cos)
  rw [← sum_div] at h1
  linarith

/-- **Equal steps are optimal.**  For `n` steps in `[-π/2, π/2]` with total
turn `Θ`, the surviving amplitude is at most that of `n` equal steps. -/
theorem equal_steps_optimal {n : ℕ} (hn : n ≠ 0) (Δ : ℕ → ℝ) (Θ : ℝ)
    (hΔ : ∀ i ∈ range n, Δ i ∈ Set.Icc (-(π / 2)) (π / 2))
    (hsum : ∑ i ∈ range n, Δ i = Θ) :
    ∏ i ∈ range n, cos (Δ i) ≤ cos (Θ / n) ^ n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hc : ∀ i ∈ range n, 0 ≤ cos (Δ i) := fun i hi => cos_nonneg_of_mem_Icc (hΔ i hi)
  have hw0 : ∀ i ∈ range n, (0 : ℝ) ≤ (fun _ => (n : ℝ)⁻¹) i := fun _ _ => by positivity
  have hw1 : ∑ i ∈ range n, (fun _ => (n : ℝ)⁻¹) i = 1 := by
    simp [card_range, hnr.ne']
  -- AM-GM: geometric mean ≤ arithmetic mean
  have amgm := geom_mean_le_arith_mean_weighted (range n) (fun _ => (n : ℝ)⁻¹)
    (fun i => cos (Δ i)) hw0 hw1 hc
  -- Jensen for the concave cosine
  have jensen := strictConcaveOn_cos_Icc.concaveOn.le_map_sum hw0 hw1 hΔ
  simp only [smul_eq_mul] at jensen
  have hmean : ∑ i ∈ range n, (n : ℝ)⁻¹ * Δ i = Θ / n := by
    rw [← mul_sum, hsum]; ring
  rw [hmean] at jensen
  have hgeo : ∏ i ∈ range n, cos (Δ i) ^ ((n : ℝ)⁻¹) =
      (∏ i ∈ range n, cos (Δ i)) ^ ((n : ℝ)⁻¹) :=
    finset_prod_rpow (range n) _ hc _
  rw [hgeo] at amgm
  have hP0 : 0 ≤ ∏ i ∈ range n, cos (Δ i) := prod_nonneg hc
  have hroot : 0 ≤ (∏ i ∈ range n, cos (Δ i)) ^ ((n : ℝ)⁻¹) := rpow_nonneg hP0 _
  have hle := pow_le_pow_left₀ hroot (amgm.trans jensen) n
  rwa [rpow_inv_natCast_pow hP0 hn] at hle

/-- **Absorption.**  The whole composite factors through the first projection:
for `k ≥ 1`, applying the first projection beforehand changes nothing. -/
theorem run_absorbs_first (Δ : ℕ → ℝ) (θ₀ : ℝ) (v : Vec) {k : ℕ} (hk : 1 ≤ k) :
    run Δ θ₀ k (proj (line Δ θ₀ 1) v) = run Δ θ₀ k v := by
  induction k, hk using Nat.le_induction with
  | base => simp only [run]; exact proj_idempotent _ _
  | succ k _ ih => simp only [run] at ih ⊢; rw [ih]

/-- **A forgotten distinction does not return.**  Inputs identified by the
first projection give the same state after every later step. -/
theorem identified_stay_identified (Δ : ℕ → ℝ) (θ₀ : ℝ) {x y : Vec}
    (h : proj (line Δ θ₀ 1) x = proj (line Δ θ₀ 1) y) {k : ℕ} (hk : 1 ≤ k) :
    run Δ θ₀ k x = run Δ θ₀ k y := by
  rw [← run_absorbs_first Δ θ₀ x hk, ← run_absorbs_first Δ θ₀ y hk, h]

/-- Projections onto different lines need not commute. -/
theorem proj_not_commute :
    proj 0 (proj (π / 4) (1, 0)) ≠ proj (π / 4) (proj 0 (1, 0)) := by
  have hc := cos_pi_div_four_sq
  have hs : sin (π / 4) = cos (π / 4) := by rw [sin_pi_div_four, cos_pi_div_four]
  have hne : cos (π / 4) ≠ 0 := by
    intro h0; rw [h0] at hc; norm_num at hc
  intro h
  have h2 := congrArg Prod.snd h
  simp only [proj, coeff, cos_zero, sin_zero, hs] at h2
  apply hne
  nlinarith [hc]

/-- The composite of the four non-commuting idempotents is not idempotent. -/
theorem halfTurn_four_not_idempotent :
    run (halfStep 4) 0 4 (run (halfStep 4) 0 4 (1, 0)) ≠ run (halfStep 4) 0 4 (1, 0) := by
  rw [halfTurn_four, run_halfStep_scaled]
  have h4 : ((4 : ℕ) : ℝ) * (π / ((4 : ℕ) : ℝ)) = π := by push_cast; ring
  rw [h4, cos_pi, sin_pi]
  intro h
  have h1 := congrArg Prod.fst h
  have e : cos (π / ((4 : ℕ) : ℝ)) ^ 4 = (cos (π / 4) ^ 2) ^ 2 := by push_cast; ring
  simp only [e, cos_pi_div_four_sq] at h1
  norm_num at h1

end RotatingProjections
