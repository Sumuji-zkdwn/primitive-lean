/-!
# Full original-variable cusp and fold count

The classification refers to the original \`LinearInputDesign.input\` and
D = 4*r^3 + 27*lam*u^2 (the NEGATIVE of the conventional cubic discriminant
up to a positive power of lam). We use FoldCount.inc for r < 0 and derive
r >= 0 from the original cubic by IVT and strict monotonicity.
The cusp tip D = r = u = 0 is separate, not a fold.
-/
noncomputable section
namespace LinearInputFoldCountOriginal
open LinearInputFoldCount

/-- A positive scale exists for any negative quadratic parameter. -/
theorem scale_exists {lam r : ℝ} (hlam : 0 < lam) (hr : r < 0) :
    ∃ a : ℝ, 0 < a ∧ r = -3 * lam * a ^ 2 := by
  have hden : (0 : ℝ) < 3 * lam := by positivity
  have hq : 0 < -r / (3 * lam) := div_pos (neg_pos.mpr hr) hden
  refine ⟨Real.sqrt (-r / (3 * lam)), Real.sqrt_pos.2 hq, ?_⟩
  rw [Real.sq_sqrt (le_of_lt hq)]
  field_simp [ne_of_gt hden]
  ring

/-- The original stationary equation and normalized cubic agree under scaling. -/
theorem input_iff_normal {lam a t z : ℝ} (hlam : 0 < lam) (ha : 0 < a) :
    LinearInputDesign.input lam (-3 * lam * a ^ 2) (a * z) =
        2 * lam * a ^ 3 * t ↔ normal t z = 0 := by
  have hnonzero : lam * a ^ 3 ≠ 0 := ne_of_gt (by positivity)
  have heq := input_normal_form lam a t z
  constructor
  · intro h
    rw [h, sub_self] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left hnonzero
  · intro h
    rw [h, mul_zero] at heq
    linarith

/-- Cardano's D in normalized coordinates. -/
theorem D_normal (lam a t : ℝ) :
    4 * (-3 * lam * a ^ 2) ^ 3 + 27 * lam * (2 * lam * a ^ 3 * t) ^ 2 =
      108 * lam ^ 3 * a ^ 6 * (t ^ 2 - 1) := by
  ring

private theorem scaled_data {lam r u : ℝ} (hlam : 0 < lam) (hr : r < 0) :
    ∃ a t : ℝ, 0 < a ∧ r = -3 * lam * a ^ 2 ∧
      u = 2 * lam * a ^ 3 * t := by
  obtain ⟨a, ha, hr'⟩ := scale_exists hlam hr
  refine ⟨a, u / (2 * lam * a ^ 3), ha, hr', ?_⟩
  have hden : 2 * lam * a ^ 3 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hden]
  ring

private theorem quot_eq_scaled_iff {a x z : ℝ} (ha : a ≠ 0) :
    x / a = z ↔ x = a * z := by
  constructor
  · intro h
    have heq := congrArg (fun v : ℝ => a * v) h
    have hx : a * (x / a) = x := by field_simp [ha]
    simpa only [hx] using heq
  · intro h
    rw [h]
    field_simp [ha]
    ring

private theorem input_scaled_iff {lam r u a t : ℝ}
    (hlam : 0 < lam) (ha : 0 < a)
    (hr : r = -3 * lam * a ^ 2) (hu : u = 2 * lam * a ^ 3 * t)
    (x : ℝ) :
    LinearInputDesign.input lam r x = u ↔ normal t (x / a) = 0 := by
  have hx : a * (x / a) = x := by field_simp [ne_of_gt ha]
  calc
    LinearInputDesign.input lam r x = u ↔
      LinearInputDesign.input lam (-3 * lam * a ^ 2) (a * (x / a)) =
        2 * lam * a ^ 3 * t := by simp only [hr, hu, hx]
    _ ↔ normal t (x / a) = 0 := input_iff_normal hlam ha

private theorem discriminant_scaled {lam r u a t : ℝ}
    (hr : r = -3 * lam * a ^ 2) (hu : u = 2 * lam * a ^ 3 * t) :
    4 * r ^ 3 + 27 * lam * u ^ 2 =
      108 * lam ^ 3 * a ^ 6 * (t ^ 2 - 1) := by
  rw [hr, hu]
  exact D_normal lam a t

private theorem hessian_scaled (lam r a z : ℝ)
    (hr : r = -3 * lam * a ^ 2) :
    3 * lam * (a * z) ^ 2 + r = lam * a ^ 2 * (3 * z ^ 2 - 3) := by
  rw [hr]
  ring

private theorem negative_r_of_D_neg {lam r u : ℝ}
    (hlam : 0 < lam) (hD : 4 * r ^ 3 + 27 * lam * u ^ 2 < 0) :
    r < 0 := by
  by_contra h
  have hr : 0 ≤ r := le_of_not_gt h
  have hp : 0 ≤ 4 * r ^ 3 := by positivity
  have hq : 0 ≤ 27 * lam * u ^ 2 := by positivity
  linarith

private theorem negative_r_of_fold {lam r u : ℝ}
    (hlam : 0 < lam) (hr : r ≠ 0)
    (hD : 4 * r ^ 3 + 27 * lam * u ^ 2 = 0) :
    r < 0 := by
  by_contra h
  have hr0 : 0 ≤ r := le_of_not_gt h
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
  have hp : 0 < 4 * r ^ 3 := by positivity
  have hq : 0 ≤ 27 * lam * u ^ 2 := by positivity
  linarith

private theorem normal_root_gt_one {t z : ℝ} (ht : 1 < t)
    (hz : normal t z = 0) : 1 < z := by
  by_contra h
  have hle : z ≤ 1 := le_of_not_gt h
  have hfactor : normal t z = (z - 2) * (z + 1) ^ 2 - 2 * (t - 1) := by
    unfold normal
    ring
  have hn : (z - 2) * (z + 1) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  rw [hfactor] at hz
  linarith

private theorem normal_root_lt_neg_one {t z : ℝ} (ht : t < -1)
    (hz : normal t z = 0) : z < -1 := by
  have hmirror : normal (-t) (-z) = 0 := by
    unfold normal at *
    nlinarith
  have h := normal_root_gt_one (by linarith : (1 : ℝ) < -t) hmirror
  linarith

/-- D < 0: exactly three stationary points, with min/saddle/min types. -/
theorem stationary_three {lam r u : ℝ} (hlam : 0 < lam)
    (hD : 4 * r ^ 3 + 27 * lam * u ^ 2 < 0) :
    ∃ x₁ x₂ x₃ : ℝ, x₁ < x₂ ∧ x₂ < x₃ ∧
      (∀ x : ℝ, LinearInputDesign.input lam r x = u ↔
        x = x₁ ∨ x = x₂ ∨ x = x₃) ∧
      0 < 3 * lam * x₁ ^ 2 + r ∧ 3 * lam * x₂ ^ 2 + r < 0 ∧
      0 < 3 * lam * x₃ ^ 2 + r := by
  obtain ⟨a, t, ha, hr, hu⟩ :=
    scaled_data hlam (negative_r_of_D_neg hlam hD)
  have heq := discriminant_scaled hr hu
  have hc : (0 : ℝ) < 108 * lam ^ 3 * a ^ 6 := by positivity
  have htsq : t ^ 2 - 1 < 0 := by
    by_contra hn
    have hn0 : 0 ≤ t ^ 2 - 1 := le_of_not_gt hn
    have hp := mul_nonneg (le_of_lt hc) hn0
    linarith
  have htl : -1 < t := by nlinarith
  have htr : t < 1 := by nlinarith
  obtain ⟨p, q, w, hp, hqL, hqR, hw, hall⟩ := three_roots t htl htr
  refine ⟨a * p, a * q, a * w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_lt_mul_of_pos_left (lt_trans hp hqL) ha
  · exact mul_lt_mul_of_pos_left (lt_trans hqR hw) ha
  · intro x
    calc
      LinearInputDesign.input lam r x = u ↔ normal t (x / a) = 0 :=
        input_scaled_iff hlam ha hr hu x
      _ ↔ x / a = p ∨ x / a = q ∨ x / a = w := hall _
      _ ↔ x = a * p ∨ x = a * q ∨ x = a * w := by
        simp only [quot_eq_scaled_iff (ne_of_gt ha)]
  · rw [hessian_scaled lam r a p hr]
    exact mul_pos (by positivity) ((root_type_by_interval p).1 hp)
  · rw [hessian_scaled lam r a q hr]
    exact mul_neg_of_pos_of_neg (by positivity) ((root_type_by_interval q).2.1 hqL hqR)
  · rw [hessian_scaled lam r a w hr]
    exact mul_pos (by positivity) ((root_type_by_interval w).2.2 hw)

/-- D = 0 and r != 0: the fold and the nondegenerate minimum. -/
theorem stationary_fold {lam r u : ℝ} (hlam : 0 < lam) (hr : r ≠ 0)
    (hD : 4 * r ^ 3 + 27 * lam * u ^ 2 = 0) :
    ∃ xf xm : ℝ, xf ≠ xm ∧
      (∀ x : ℝ, LinearInputDesign.input lam r x = u ↔ x = xf ∨ x = xm) ∧
      3 * lam * xf ^ 2 + r = 0 ∧ 0 < 3 * lam * xm ^ 2 + r := by
  obtain ⟨a, t, ha, hr', hu⟩ :=
    scaled_data hlam (negative_r_of_fold hlam hr hD)
  have heq := discriminant_scaled hr' hu
  have hc : (0 : ℝ) < 108 * lam ^ 3 * a ^ 6 := by positivity
  have hmul : (108 * lam ^ 3 * a ^ 6) * (t ^ 2 - 1) = 0 := by linarith
  have ht0 : t ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hc)
  have hf : (t - 1) * (t + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with hpos | hneg
  · have ht : t = 1 := by linarith
    subst t
    refine ⟨a * (-1), a * 2, ?_, ?_, ?_, ?_⟩
    · intro h
      nlinarith [ha]
    · intro x
      calc
        LinearInputDesign.input lam r x = u ↔ normal 1 (x / a) = 0 :=
          input_scaled_iff hlam ha hr' hu x
        _ ↔ x / a = -1 ∨ x / a = 2 := positive_fold_roots _
        _ ↔ x = a * (-1) ∨ x = a * 2 := by
          simp only [quot_eq_scaled_iff (ne_of_gt ha)]
    · rw [hessian_scaled lam r a (-1) hr']
      norm_num
    · rw [hessian_scaled lam r a 2 hr']
      norm_num <;> positivity
  · have ht : t = -1 := by linarith
    subst t
    refine ⟨a * 1, a * (-2), ?_, ?_, ?_, ?_⟩
    · intro h
      nlinarith [ha]
    · intro x
      calc
        LinearInputDesign.input lam r x = u ↔ normal (-1) (x / a) = 0 :=
          input_scaled_iff hlam ha hr' hu x
        _ ↔ x / a = 1 ∨ x / a = -2 := negative_fold_roots _
        _ ↔ x = a * 1 ∨ x = a * (-2) := by
          simp only [quot_eq_scaled_iff (ne_of_gt ha)]
    · rw [hessian_scaled lam r a 1 hr']
      norm_num
    · rw [hessian_scaled lam r a (-2) hr']
      norm_num <;> positivity

private theorem input_difference (lam r x y : ℝ) :
    LinearInputDesign.input lam r y - LinearInputDesign.input lam r x =
      (y - x) * (lam * (x ^ 2 + x * y + y ^ 2) + r) := by
  unfold LinearInputDesign.input
  ring

private theorem input_strictMono {lam r : ℝ} (hlam : 0 < lam)
    (hr : 0 ≤ r) : StrictMono (LinearInputDesign.input lam r) := by
  intro x y hxy
  have hsq : 0 < (x - y) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hxy))
  have hsum := sq_nonneg (x + y)
  have hquad : 0 < x ^ 2 + x * y + y ^ 2 := by nlinarith
  have hpos : 0 < lam * (x ^ 2 + x * y + y ^ 2) + r :=
    add_pos_of_pos_of_nonneg (mul_pos hlam hquad) hr
  have hm := mul_pos (sub_pos.mpr hxy) hpos
  have heq := input_difference lam r x y
  linarith

private theorem nonnegative_unique {lam r u : ℝ} (hlam : 0 < lam)
    (hr : 0 ≤ r) :
    ∃ x : ℝ, ∀ y : ℝ, LinearInputDesign.input lam r y = u ↔ y = x := by
  let M : ℝ := |u| / lam + 1
  have hM : 1 ≤ M := by
    dsimp [M]
    have hp : 0 ≤ |u| / lam := div_nonneg (abs_nonneg u) (le_of_lt hlam)
    linarith
  have hMpos : 0 < M := by linarith
  have hlinear : lam * M = |u| + lam := by
    dsimp [M]
    field_simp [ne_of_gt hlam]
    ring
  have hprod : 0 ≤ M * ((M - 1) * (M + 1)) :=
    mul_nonneg (le_of_lt hMpos)
      (mul_nonneg (by linarith) (by linarith))
  have hcube : M ≤ M ^ 3 := by nlinarith [hprod]
  have hbound : lam * M ≤ lam * M ^ 3 :=
    mul_le_mul_of_nonneg_left hcube (le_of_lt hlam)
  have hrM : 0 ≤ r * M := mul_nonneg hr (le_of_lt hMpos)
  have hright0 : |u| < LinearInputDesign.input lam r M := by
    unfold LinearInputDesign.input
    linarith
  have hleft : LinearInputDesign.input lam r (-M) < u := by
    have hodd : LinearInputDesign.input lam r (-M) =
        -LinearInputDesign.input lam r M := by
      unfold LinearInputDesign.input
      ring
    linarith [neg_abs_le u]
  have hright : u < LinearInputDesign.input lam r M :=
    lt_of_le_of_lt (le_abs_self u) hright0
  have hcont : Continuous (fun v : ℝ => LinearInputDesign.input lam r v) := by
    unfold LinearInputDesign.input
    fun_prop
  obtain ⟨x, hx, hxroot⟩ :=
    intermediate_value_Icc (show -M ≤ M by linarith) hcont.continuousOn
      (show u ∈ Set.Icc
        (LinearInputDesign.input lam r (-M))
        (LinearInputDesign.input lam r M) from
        ⟨le_of_lt hleft, le_of_lt hright⟩)
  have hinj := (input_strictMono hlam hr).injective
  refine ⟨x, ?_⟩
  intro y
  constructor
  · intro hy
    exact hinj (hy.trans hxroot.symm)
  · rintro rfl
    exact hxroot

/-- D > 0: one stationary point with strictly positive Hessian determinant. -/
theorem stationary_one {lam r u : ℝ} (hlam : 0 < lam)
    (hD : 0 < 4 * r ^ 3 + 27 * lam * u ^ 2) :
    ∃ x : ℝ, (∀ y : ℝ, LinearInputDesign.input lam r y = u ↔ y = x) ∧
      0 < 3 * lam * x ^ 2 + r := by
  by_cases hrneg : r < 0
  · obtain ⟨a, t, ha, hr, hu⟩ := scaled_data hlam hrneg
    have heq := discriminant_scaled hr hu
    have hc : (0 : ℝ) < 108 * lam ^ 3 * a ^ 6 := by positivity
    have ht2 : 0 < t ^ 2 - 1 := by
      by_contra hn
      have hle : t ^ 2 - 1 ≤ 0 := le_of_not_gt hn
      have hm := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) hle
      linarith
    by_cases ht : 1 < t
    · obtain ⟨z, hz, hunique⟩ := unique_root_above t ht
      have hz1 : 1 < z := normal_root_gt_one ht hz
      refine ⟨a * z, ?_, ?_⟩
      · intro y
        calc
          LinearInputDesign.input lam r y = u ↔ normal t (y / a) = 0 :=
            input_scaled_iff hlam ha hr hu y
          _ ↔ y / a = z := by
            constructor
            · exact fun hy => hunique _ hy
            · rintro rfl
              exact hz
          _ ↔ y = a * z := quot_eq_scaled_iff (ne_of_gt ha)
      · rw [hessian_scaled lam r a z hr]
        exact mul_pos (by positivity) ((root_type_by_interval z).2.2 hz1)
    · have ht' : t < -1 := by nlinarith [ht2]
      obtain ⟨z, hz, hunique⟩ := unique_root_below t ht'
      have hz1 : z < -1 := normal_root_lt_neg_one ht' hz
      refine ⟨a * z, ?_, ?_⟩
      · intro y
        calc
          LinearInputDesign.input lam r y = u ↔ normal t (y / a) = 0 :=
            input_scaled_iff hlam ha hr hu y
          _ ↔ y / a = z := by
            constructor
            · exact fun hy => hunique _ hy
            · rintro rfl
              exact hz
          _ ↔ y = a * z := quot_eq_scaled_iff (ne_of_gt ha)
      · rw [hessian_scaled lam r a z hr]
        exact mul_pos (by positivity) ((root_type_by_interval z).1 hz1)
  · have hr0 : 0 ≤ r := le_of_not_gt hrneg
    obtain ⟨x, hunique⟩ := nonnegative_unique hlam hr0
    refine ⟨x, hunique, ?_⟩
    by_cases hzero : r = 0
    · subst r
      have hx : x ≠ 0 := by
        intro h
        have hu0 : LinearInputDesign.input lam 0 (0 : ℝ) = u := by
          exact (hunique 0).2 h.symm
        have hu : u = 0 := by simpa [LinearInputDesign.input] using hu0.symm
        subst u
        norm_num at hD
      have hp : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      have hm : 0 < lam * x ^ 2 := mul_pos hlam hp
      nlinarith
    · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hzero)
      have hp : 0 ≤ 3 * lam * x ^ 2 := by positivity
      linarith

/-- D = 0 and r = 0 forces u = 0, the separate triple-root cusp tip. -/
theorem tip_of_D_zero {lam r u : ℝ} (hlam : 0 < lam) (hr : r = 0)
    (hD : 4 * r ^ 3 + 27 * lam * u ^ 2 = 0) : u = 0 := by
  rw [hr] at hD
  norm_num at hD
  have h27 : (27 : ℝ) * lam ≠ 0 := ne_of_gt (by positivity)
  have hu2 : u ^ 2 = 0 :=
    (mul_eq_zero.mp (show (27 * lam) * u ^ 2 = 0 by nlinarith [hD])).resolve_left h27
  nlinarith

end LinearInputFoldCountOriginal
