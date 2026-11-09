/-!
Quartic support classification extended from lam > 0 to lam ≥ 0.
The removed-quartic case lam = 0 is included. The tie-breaking exception of
the lam > 0 classification survives only with an explicit 0 < lam.
Scalar statements only; no dynamics and no lam → 0 asymptotics are asserted.
-/
noncomputable section
namespace LinearInputQuarticNonneg
open LinearInputDesign

/-- The support gap at the forced input factors through the margin. -/
theorem gap_factor (lam r a x : ℝ) :
    (lam * x ^ 4 / 4 + r * x ^ 2 / 2) - (lam * a ^ 4 / 4 + r * a ^ 2 / 2) -
      input lam r a * (x - a) =
    (x - a) ^ 2 * (lam * (x + a) ^ 2 / 4 + (lam * a ^ 2 + r) / 2) := by
  unfold input
  ring

/-- Any supporting input is the stationary input; no sign of lam is used. -/
theorem support_forces_input {lam r u a : ℝ}
    (h : ∀ x : ℝ, u * (x - a) ≤
      (lam * x ^ 4 / 4 + r * x ^ 2 / 2) - (lam * a ^ 4 / 4 + r * a ^ 2 / 2)) :
    u = input lam r a := by
  have hmin : ∀ t : ℝ, LinearInputCalculus.potential lam r u a ≤
      LinearInputCalculus.potential lam r u t := by
    intro t
    have := h t
    unfold LinearInputCalculus.potential
    linarith
  simpa [input] using LinearInputCalculus.global_minimum_forces_input hmin

/-- A negative margin is witnessed by an explicit point different from a. -/
theorem exists_negative_gap {lam r a : ℝ} (hlam : 0 ≤ lam)
    (hm : lam * a ^ 2 + r < 0) :
    ∃ x : ℝ, x ≠ a ∧ lam * (x + a) ^ 2 / 4 + (lam * a ^ 2 + r) / 2 < 0 := by
  set m := lam * a ^ 2 + r with hmdef
  have hden : 0 < lam + 1 - m := by linarith
  set d := -m / (lam + 1 - m) with hd
  have hdpos : 0 < d := div_pos (by linarith) hden
  have hdmul : d * (lam + 1 - m) = -m := by
    rw [hd]; field_simp
  have hdlt : d < 1 := by nlinarith
  have hld : lam * d < -m := by nlinarith
  have hsq : lam * d ^ 2 < -2 * m := by nlinarith [mul_nonneg hlam hdpos.le]
  by_cases hx : -a + d = a
  · refine ⟨-a - d, ?_, ?_⟩
    · intro h; linarith
    · have : (-a - d + a) ^ 2 = d ^ 2 := by ring
      rw [this]; linarith
  · refine ⟨-a + d, hx, ?_⟩
    have : (-a + d + a) ^ 2 = d ^ 2 := by ring
    rw [this]; linarith

/-- Support classification for every lam ≥ 0, including the removed quartic. -/
theorem support_iff_input_and_margin {lam r u a : ℝ} (hlam : 0 ≤ lam) :
    (∀ x : ℝ, u * (x - a) ≤
      (lam * x ^ 4 / 4 + r * x ^ 2 / 2) - (lam * a ^ 4 / 4 + r * a ^ 2 / 2)) ↔
    u = input lam r a ∧ 0 ≤ lam * a ^ 2 + r := by
  constructor
  · intro h
    have hu := support_forces_input h
    refine ⟨hu, ?_⟩
    by_contra hneg
    obtain ⟨x, hxa, hx⟩ := exists_negative_gap hlam (lt_of_not_ge hneg)
    have hg := gap_factor lam r a x
    have hpos : 0 < (x - a) ^ 2 := by
      have : x - a ≠ 0 := sub_ne_zero.mpr hxa
      positivity
    have hneg' : (x - a) ^ 2 * (lam * (x + a) ^ 2 / 4 + (lam * a ^ 2 + r) / 2) < 0 :=
      mul_neg_of_pos_of_neg hpos hx
    have := h x
    rw [hu] at this
    linarith
  · rintro ⟨hu, hm⟩ x
    have hg := gap_factor lam r a x
    have hb : 0 ≤ lam * (x + a) ^ 2 / 4 + (lam * a ^ 2 + r) / 2 := by positivity
    have : 0 ≤ (x - a) ^ 2 * (lam * (x + a) ^ 2 / 4 + (lam * a ^ 2 + r) / 2) :=
      mul_nonneg (sq_nonneg _) hb
    rw [hu]
    linarith

/-- Strict support for every lam ≥ 0. The tie-breaking clause needs 0 < lam. -/
theorem strict_support_iff {lam r u a : ℝ} (hlam : 0 ≤ lam) :
    (∀ x : ℝ, x ≠ a → u * (x - a) <
      (lam * x ^ 4 / 4 + r * x ^ 2 / 2) - (lam * a ^ 4 / 4 + r * a ^ 2 / 2)) ↔
    u = input lam r a ∧
      (0 < lam * a ^ 2 + r ∨ (0 < lam ∧ a = 0 ∧ r = 0)) := by
  constructor
  · intro hs
    have hsupp : ∀ x : ℝ, u * (x - a) ≤
        (lam * x ^ 4 / 4 + r * x ^ 2 / 2) - (lam * a ^ 4 / 4 + r * a ^ 2 / 2) := by
      intro x
      by_cases hx : x = a
      · subst hx; simp
      · exact le_of_lt (hs x hx)
    obtain ⟨hu, hm⟩ := (support_iff_input_and_margin hlam).mp hsupp
    refine ⟨hu, ?_⟩
    rcases eq_or_lt_of_le hm with hz | hp
    · right
      have hz' : lam * a ^ 2 + r = 0 := hz.symm
      -- at zero margin the gap is (x-a)^2 * lam (x+a)^2 / 4
      have key : ∀ x : ℝ, x ≠ a → 0 < (x - a) ^ 2 * (lam * (x + a) ^ 2 / 4) := by
        intro x hx
        have h1 := hs x hx
        have hg := gap_factor lam r a x
        rw [hz', hu] at *
        have : (x - a) ^ 2 * (lam * (x + a) ^ 2 / 4 + 0 / 2) =
            (x - a) ^ 2 * (lam * (x + a) ^ 2 / 4) := by ring
        linarith
      have hlampos : 0 < lam := by
        rcases eq_or_lt_of_le hlam with h0 | h0
        · exfalso
          have := key (a + 1) (by linarith)
          rw [← h0] at this
          simp at this
        · exact h0
      have ha : a = 0 := by
        by_contra ha
        have hne : -a ≠ a := by
          intro h; apply ha; linarith
        have h2 := key (-a) hne
        have h3 : (-a - a) ^ 2 * (lam * (-a + a) ^ 2 / 4) = 0 := by ring
        linarith
      refine ⟨hlampos, ha, ?_⟩
      rw [ha] at hz'
      simpa using hz'
    · exact Or.inl hp
  · rintro ⟨hu, hcase⟩ x hx
    have hg := gap_factor lam r a x
    have hpos : 0 < (x - a) ^ 2 := by
      have : x - a ≠ 0 := sub_ne_zero.mpr hx
      positivity
    have hb : 0 < lam * (x + a) ^ 2 / 4 + (lam * a ^ 2 + r) / 2 := by
      rcases hcase with hp | ⟨hl, ha, hr⟩
      · have : 0 ≤ lam * (x + a) ^ 2 / 4 := by positivity
        linarith
      · subst ha; subst hr
        have hx0 : x ≠ 0 := hx
        have hx2 : 0 < x ^ 2 := by positivity
        have hlx : 0 < lam * x ^ 2 := mul_pos hl hx2
        have he : lam * (x + 0) ^ 2 / 4 + (lam * 0 ^ 2 + 0) / 2 = lam * x ^ 2 / 4 := by ring
        rw [he]
        linarith
    have := mul_pos hpos hb
    rw [hu]
    linarith

/-- For lam > 0 the extended criterion is exactly the existing one. -/
theorem strict_criterion_agrees_of_pos {lam r a : ℝ} (hlam : 0 < lam) :
    (0 < lam * a ^ 2 + r ∨ (0 < lam ∧ a = 0 ∧ r = 0)) ↔
    (0 < lam * a ^ 2 + r ∨ (a = 0 ∧ r = 0)) := by
  constructor
  · rintro (h | ⟨_, ha, hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ha, hr⟩
  · rintro (h | ⟨ha, hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hlam, ha, hr⟩

/-- A supporting input exists uniquely exactly at nonnegative margin, lam ≥ 0. -/
theorem existsUnique_support_input_iff {lam r a : ℝ} (hlam : 0 ≤ lam) :
    (∃! u : ℝ, ∀ x : ℝ, u * (x - a) ≤
      (lam * x ^ 4 / 4 + r * x ^ 2 / 2) - (lam * a ^ 4 / 4 + r * a ^ 2 / 2)) ↔
    0 ≤ lam * a ^ 2 + r := by
  constructor
  · rintro ⟨u, hu, _⟩
    exact ((support_iff_input_and_margin hlam).mp hu).2
  · intro hm
    refine ⟨input lam r a, (support_iff_input_and_margin hlam).mpr ⟨rfl, hm⟩, ?_⟩
    intro u hu
    exact ((support_iff_input_and_margin hlam).mp hu).1

/-- A strict supporting input exists uniquely exactly on the extended criterion. -/
theorem existsUnique_strict_support_input_iff {lam r a : ℝ} (hlam : 0 ≤ lam) :
    (∃! u : ℝ, ∀ x : ℝ, x ≠ a → u * (x - a) <
      (lam * x ^ 4 / 4 + r * x ^ 2 / 2) - (lam * a ^ 4 / 4 + r * a ^ 2 / 2)) ↔
    0 < lam * a ^ 2 + r ∨ (0 < lam ∧ a = 0 ∧ r = 0) := by
  constructor
  · rintro ⟨u, hu, _⟩
    exact ((strict_support_iff hlam).mp hu).2
  · intro hm
    refine ⟨input lam r a, (strict_support_iff hlam).mpr ⟨rfl, hm⟩, ?_⟩
    intro u hu
    exact ((strict_support_iff hlam).mp hu).1

/-! ## The removed quartic, lam = 0 -/

/-- With the quartic removed, a point is the unique minimizer iff r > 0. -/
theorem zero_quartic_strict_support_iff {r u a : ℝ} :
    (∀ x : ℝ, x ≠ a → u * (x - a) <
      (0 * x ^ 4 / 4 + r * x ^ 2 / 2) - (0 * a ^ 4 / 4 + r * a ^ 2 / 2)) ↔
    u = r * a ∧ 0 < r := by
  rw [strict_support_iff le_rfl]
  simp [input]

/-- With the quartic removed and r = u = 0, every point is a global minimizer. -/
theorem zero_quartic_flat_all_minimal (a x : ℝ) :
    f 0 0 0 a ≤ f 0 0 0 x := by
  simp [f]

/-- With the quartic removed, no global minimizer exists when r < 0. -/
theorem zero_quartic_no_minimum_of_neg {r u : ℝ} (hr : r < 0) :
    ¬ ∃ a : ℝ, ∀ x : ℝ, f 0 r u a ≤ f 0 r u x := by
  rintro ⟨a, ha⟩
  have hs : ∀ x : ℝ, u * (x - a) ≤
      (0 * x ^ 4 / 4 + r * x ^ 2 / 2) - (0 * a ^ 4 / 4 + r * a ^ 2 / 2) := by
    intro x; have := ha x; simp only [f] at this; linarith
  have := ((support_iff_input_and_margin le_rfl).mp hs).2
  linarith

/-- With the quartic removed, no global minimizer exists when r = 0 and u ≠ 0. -/
theorem zero_quartic_no_minimum_of_flat_input {u : ℝ} (hu : u ≠ 0) :
    ¬ ∃ a : ℝ, ∀ x : ℝ, f 0 0 u a ≤ f 0 0 u x := by
  rintro ⟨a, ha⟩
  have hs : ∀ x : ℝ, u * (x - a) ≤
      (0 * x ^ 4 / 4 + 0 * x ^ 2 / 2) - (0 * a ^ 4 / 4 + 0 * a ^ 2 / 2) := by
    intro x; have := ha x; simp only [f] at this; linarith
  have := ((support_iff_input_and_margin le_rfl).mp hs).1
  simp [input] at this
  exact hu this

/-- For lam > 0 the coefficient is inessential: rescaling by s = √lam. -/
theorem quartic_scaling {s r u x : ℝ} (hs : s ≠ 0) :
    f (s ^ 2) r u x = f 1 r (s * u) (s * x) / s ^ 2 := by
  unfold f
  field_simp

end LinearInputQuarticNonneg
