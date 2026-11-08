/-!
Cusp/fold classification in the original linear-input notation.

The real number `t` parametrizes the normalized depressed cubic
`z^3 - 3*z - 2*t`. This covers the r < 0 regime after choosing the
positive scale a with r = -3*lam*a^2 and u = 2*lam*a^3*t.
The tip r = u = 0 is treated separately, since the two-root fold
classification does not apply at that triple root.
-/
noncomputable section
namespace LinearInputFoldCount

/-- A normalized stationary equation for the quartic energy. -/
def normal (t z : ℝ) : ℝ := z ^ 3 - 3 * z - 2 * t

/-- The normalized cubic is exactly the existing design input. -/
theorem input_normal_form (lam a t z : ℝ) :
    LinearInputDesign.input lam (-3 * lam * a ^ 2) (a * z) -
      2 * lam * a ^ 3 * t = lam * a ^ 3 * normal t z := by
  unfold LinearInputDesign.input normal
  ring

/-- This discriminant is positive in the three-root sector. -/
theorem ordinary_discriminant_normal (t : ℝ) :
    LinearInputVariablePairGalois.cubicDiscriminant 1 (-3) (2 * t) =
      108 * (1 - t ^ 2) := by
  unfold LinearInputVariablePairGalois.cubicDiscriminant
  ring

/-- The positive-input fold has a double root at -1 and a simple root at 2. -/
theorem positive_fold_roots (z : ℝ) :
    normal 1 z = 0 ↔ z = -1 ∨ z = 2 := by
  have hfactor : normal 1 z = (z + 1) ^ 2 * (z - 2) := by
    unfold normal
    ring
  rw [hfactor]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · left
      nlinarith
    · right
      linarith
  · rintro (rfl | rfl) <;> norm_num

/-- The negative-input fold has a double root at 1 and a simple root at -2. -/
theorem negative_fold_roots (z : ℝ) :
    normal (-1) z = 0 ↔ z = 1 ∨ z = -2 := by
  have hfactor : normal (-1) z = (z - 1) ^ 2 * (z + 2) := by
    unfold normal
    ring
  rw [hfactor]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · left
      nlinarith
    · right
      linarith
  · rintro (rfl | rfl) <;> norm_num

/-- At the cusp tip there is one distinct stationary point, not two. -/
theorem cusp_tip_unique (lam : ℝ) (hlam : 0 < lam) (x : ℝ) :
    LinearInputDesign.input lam 0 x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hx : lam * x ^ 3 = 0 := by simpa [LinearInputDesign.input] using h
    have hx3 : x ^ 3 = 0 := (mul_eq_zero.mp hx).resolve_left (ne_of_gt hlam)
    have hprod : x * (x * x) = 0 := by
      calc
        x * (x * x) = x ^ 3 := by ring
        _ = 0 := hx3
    rcases mul_eq_zero.mp hprod with hx0 | hxx
    · exact hx0
    · rcases mul_eq_zero.mp hxx with hx0 | hx0 <;> exact hx0
  · rintro rfl
    simp [LinearInputDesign.input]

private theorem normal_diff (t x y : ℝ) :
    normal t y - normal t x = (y - x) * (x ^ 2 + x * y + y ^ 2 - 3) := by
  unfold normal
  ring

private theorem quad_pos_right {x y : ℝ} (hx : 1 ≤ x) (hxy : x < y) :
    0 < x ^ 2 + x * y + y ^ 2 - 3 := by
  have h1 : 0 ≤ x - 1 := by linarith
  have h2 : 0 ≤ y - 1 := by linarith
  have h3 := mul_nonneg h1 h2
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]

private theorem quad_pos_left {x y : ℝ} (hxy : x < y) (hy : y ≤ -1) :
    0 < x ^ 2 + x * y + y ^ 2 - 3 := by
  have h1 : 0 ≤ -x - 1 := by linarith
  have h2 : 0 ≤ -y - 1 := by linarith
  have h3 := mul_nonneg h1 h2
  nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1)]

private theorem quad_neg_middle {x y : ℝ}
    (hx : -1 ≤ x) (hxy : x < y) (hy : y ≤ 1) :
    x ^ 2 + x * y + y ^ 2 - 3 < 0 := by
  have h1 := mul_nonneg (show 0 ≤ 1 - x by linarith)
    (show 0 ≤ 1 + x by linarith)
  have h2 := mul_nonneg (show 0 ≤ 1 - y by linarith)
    (show 0 ≤ 1 + y by linarith)
  have h3 : 0 < (x - y) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hxy))
  nlinarith

private theorem mono_right (t : ℝ) {x y : ℝ}
    (hx : 1 ≤ x) (hxy : x < y) : normal t x < normal t y := by
  have hq := quad_pos_right hx hxy
  have hm := mul_pos (sub_pos.mpr hxy) hq
  nlinarith [normal_diff t x y]

private theorem mono_left (t : ℝ) {x y : ℝ}
    (hxy : x < y) (hy : y ≤ -1) : normal t x < normal t y := by
  have hq := quad_pos_left hxy hy
  have hm := mul_pos (sub_pos.mpr hxy) hq
  nlinarith [normal_diff t x y]

private theorem anti_middle (t : ℝ) {x y : ℝ}
    (hx : -1 ≤ x) (hxy : x < y) (hy : y ≤ 1) :
    normal t y < normal t x := by
  have hq := quad_neg_middle hx hxy hy
  have hm := mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hq
  nlinarith [normal_diff t x y]

private theorem normal_continuous (t : ℝ) : Continuous (normal t) := by
  unfold normal
  fun_prop

private theorem root_between {t a b : ℝ} (hab : a ≤ b)
    (ha : normal t a ≤ 0) (hb : 0 ≤ normal t b) :
    ∃ x : ℝ, a ≤ x ∧ x ≤ b ∧ normal t x = 0 := by
  obtain ⟨x, hx, hz⟩ := intermediate_value_Icc hab (normal_continuous t).continuousOn
    (show (0 : ℝ) ∈ Set.Icc (normal t a) (normal t b) from ⟨ha, hb⟩)
  exact ⟨x, hx.1, hx.2, hz⟩

private theorem root_between_reverse {t a b : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ normal t a) (hb : normal t b ≤ 0) :
    ∃ x : ℝ, a ≤ x ∧ x ≤ b ∧ normal t x = 0 := by
  obtain ⟨x, hx, hz⟩ := intermediate_value_Icc' hab (normal_continuous t).continuousOn
    (show (0 : ℝ) ∈ Set.Icc (normal t b) (normal t a) from ⟨hb, ha⟩)
  exact ⟨x, hx.1, hx.2, hz⟩

/-- Three and only three distinct roots inside the cusp (strictly between the folds). -/
theorem three_roots (t : ℝ) (htl : -1 < t) (htr : t < 1) :
    ∃ a b c : ℝ, a < -1 ∧ -1 < b ∧ b < 1 ∧ 1 < c ∧
      ∀ x : ℝ, normal t x = 0 ↔ x = a ∨ x = b ∨ x = c := by
  have hleft0 : normal t (-3) < 0 := by unfold normal; norm_num; linarith
  have hleft1 : 0 < normal t (-1) := by unfold normal; norm_num; linarith
  have hright1 : normal t 1 < 0 := by unfold normal; norm_num; linarith
  have hright3 : 0 < normal t 3 := by unfold normal; norm_num; linarith
  obtain ⟨a, ha3, ha1, ha0⟩ :=
    root_between (t := t) (a := -3) (b := -1) (by norm_num)
      (le_of_lt hleft0) (le_of_lt hleft1)
  obtain ⟨b, hb1, hb2, hb0⟩ :=
    root_between_reverse (t := t) (a := -1) (b := 1) (by norm_num)
      (le_of_lt hleft1) (le_of_lt hright1)
  obtain ⟨c, hc1, hc3, hc0⟩ :=
    root_between (t := t) (a := 1) (b := 3) (by norm_num)
      (le_of_lt hright1) (le_of_lt hright3)
  have ha : a < -1 := by
    by_contra hn
    have heq : a = -1 := le_antisymm ha1 (le_of_not_gt hn)
    rw [heq] at ha0
    linarith
  have hbL : -1 < b := by
    by_contra hn
    have heq : b = -1 := le_antisymm (le_of_not_gt hn) hb1
    rw [heq] at hb0
    linarith
  have hbR : b < 1 := by
    by_contra hn
    have heq : b = 1 := le_antisymm hb2 (le_of_not_gt hn)
    rw [heq] at hb0
    linarith
  have hc : 1 < c := by
    by_contra hn
    have heq : c = 1 := le_antisymm (le_of_not_gt hn) hc1
    rw [heq] at hc0
    linarith
  refine ⟨a, b, c, ha, hbL, hbR, hc, ?_⟩
  intro x
  constructor
  · intro hx
    rcases lt_trichotomy x (-1) with hxm | hxe | hxp
    · left
      rcases lt_trichotomy x a with hlt | heq | hgt
      · have hs := mono_left t hlt (le_of_lt ha)
        linarith
      · exact heq
      · have hs := mono_left t hgt (le_of_lt hxm)
        linarith
    · rw [hxe] at hx
      linarith
    · rcases lt_trichotomy x 1 with hxm | hxe | hxp2
      · right; left
        rcases lt_trichotomy x b with hlt | heq | hgt
        · have hs := anti_middle t (le_of_lt hxp) hlt (le_of_lt hbR)
          linarith
        · exact heq
        · have hs := anti_middle t (le_of_lt hbL) hgt (le_of_lt hxm)
          linarith
      · rw [hxe] at hx
        linarith
      · right; right
        rcases lt_trichotomy x c with hlt | heq | hgt
        · have hs := mono_right t (le_of_lt hxp2) hlt
          linarith
        · exact heq
        · have hs := mono_right t (le_of_lt hc) hgt
          linarith
  · rintro (rfl | rfl | rfl)
    · exact ha0
    · exact hb0
    · exact hc0

/-- Past the positive fold, exactly one stationary root survives. -/
theorem unique_root_above (t : ℝ) (ht : 1 < t) :
    ∃! z : ℝ, normal t z = 0 := by
  have htpos : 0 < t := by linarith
  have hmul : 0 < t * (t ^ 2 - 1) := by
    apply mul_pos htpos
    nlinarith
  have h2 : normal t 2 < 0 := by unfold normal; norm_num; linarith
  have h3 : 0 < normal t (3 * t) := by
    unfold normal
    nlinarith
  obtain ⟨a, ha2, ha3, ha0⟩ :=
    root_between (t := t) (a := 2) (b := 3 * t) (by linarith)
      (le_of_lt h2) (le_of_lt h3)
  refine ⟨a, ha0, ?_⟩
  intro z hz
  have hz1 : 1 < z := by
    by_contra hn
    have hle : z ≤ 1 := le_of_not_gt hn
    have hfactor : normal t z = (z - 2) * (z + 1) ^ 2 - 2 * (t - 1) := by
      unfold normal
      ring
    have hnon : (z - 2) * (z + 1) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    rw [hfactor] at hz
    linarith
  rcases lt_trichotomy z a with hlt | heq | hgt
  · have hs := mono_right t (le_of_lt hz1) hlt
    linarith
  · exact heq
  · have hs := mono_right t (by linarith : (1 : ℝ) ≤ a) hgt
    linarith

/-- Past the negative fold, exactly one stationary root survives. -/
theorem unique_root_below (t : ℝ) (ht : t < -1) :
    ∃! z : ℝ, normal t z = 0 := by
  obtain ⟨a, ha, haUnique⟩ := unique_root_above (-t) (by linarith)
  refine ⟨-a, ?_, ?_⟩
  · unfold normal at *
    nlinarith
  · intro z hz
    have hz' : normal (-t) (-z) = 0 := by
      unfold normal at *
      nlinarith
    have h := haUnique (-z) hz'
    linarith

/-- For the normal form, the two outer roots have positive reduced Hessian
and the middle root has negative reduced Hessian. -/
theorem root_type_by_interval (z : ℝ) :
    (z < -1 → 0 < 3 * z ^ 2 - 3) ∧
    (-1 < z → z < 1 → 3 * z ^ 2 - 3 < 0) ∧
    (1 < z → 0 < 3 * z ^ 2 - 3) := by
  constructor
  · intro hz
    nlinarith [sq_nonneg (z + 1)]
  constructor
  · intro hl hr
    nlinarith [mul_pos (by linarith : 0 < 1 - z) (by linarith : 0 < 1 + z)]
  · intro hz
    nlinarith [sq_nonneg (z - 1)]

end LinearInputFoldCount
