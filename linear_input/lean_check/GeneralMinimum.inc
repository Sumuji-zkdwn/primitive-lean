/-!
General fixed-input minimum criteria, using the existing observation energy.
Source: the user's general V(x) - u*x claim and the accepted three-item plan.
No convexity, continuity or differentiability is assumed in the two general
equivalences. Uniqueness concerns the minimizing point, not the input.
The quartic bridges reuse the existing full-plane minimum certificates.
-/
noncomputable section
namespace LinearInputMinimum
open LinearInputObservation LinearInputDesign

/-- Global minimality at the specified point is exactly the support inequality. -/
theorem minimum_iff_support (V : ℝ → ℝ) (a u : ℝ) :
    (∀ x : ℝ, energy V id u a ≤ energy V id u x) ↔
      ∀ x : ℝ, u * (x - a) ≤ V x - V a := by
  simp only [energy, id_eq]
  constructor <;> intro h x <;> nlinarith [h x]

/-- The target is the unique global minimizer iff support is strict off the target. -/
theorem unique_minimum_iff_strict_support (V : ℝ → ℝ) (a u : ℝ) :
    ((∀ x : ℝ, energy V id u a ≤ energy V id u x) ∧
      ∀ b : ℝ, (∀ x : ℝ, energy V id u b ≤ energy V id u x) → b = a) ↔
      ∀ x : ℝ, x ≠ a → u * (x - a) < V x - V a := by
  constructor
  · rintro ⟨hmin, huniq⟩ x hx
    have hne : energy V id u a ≠ energy V id u x := by
      intro he
      apply hx
      apply huniq x
      intro y
      rw [← he]
      exact hmin y
    have hlt := lt_of_le_of_ne (hmin x) hne
    simp only [energy, id_eq] at hlt
    nlinarith
  · intro h
    have hmin : ∀ x : ℝ, energy V id u a ≤ energy V id u x := by
      apply (minimum_iff_support V a u).mpr
      intro x
      by_cases hx : x = a
      · subst x
        simp
      · exact le_of_lt (h x hx)
    refine ⟨hmin, ?_⟩
    intro x hxm
    by_contra hx
    have hs := h x hx
    have hm := hxm a
    simp only [energy, id_eq] at hm
    nlinarith

/-- The scalar quartic comparison is equivalent to the existing full-plane one.
The transverse square is nonnegative and vanishes on y = sqrt(2)*x. -/
theorem quartic_minimum_iff_full (lam r u a : ℝ) :
    (∀ x : ℝ,
      energy (fun t : ℝ => lam * t ^ 4 / 4 + r * t ^ 2 / 2) id u a ≤
      energy (fun t : ℝ => lam * t ^ 4 / 4 + r * t ^ 2 / 2) id u x) ↔
    ∀ x y : ℝ, E lam r u a (Real.sqrt 2 * a) ≤ E lam r u x y := by
  change (∀ x : ℝ, f lam r u a ≤ f lam r u x) ↔ _
  constructor
  · intro h x y
    simp only [E, sub_self, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
    exact (h x).trans (le_add_of_nonneg_right (by positivity))
  · intro h x
    simpa [E] using h x (Real.sqrt 2 * x)

/-- General support specialized to the quartic, with the existing arbitrary-input criterion. -/
theorem quartic_support_iff_input_and_margin {lam r u a : ℝ} (hlam : 0 < lam) :
    (∀ x : ℝ, u * (x - a) ≤
      (lam * x ^ 4 / 4 + r * x ^ 2 / 2) -
      (lam * a ^ 4 / 4 + r * a ^ 2 / 2)) ↔
    u = input lam r a ∧ 0 ≤ lam * a ^ 2 + r := by
  exact (minimum_iff_support
    (fun t : ℝ => lam * t ^ 4 / 4 + r * t ^ 2 / 2) a u).symm.trans
    ((quartic_minimum_iff_full lam r u a).trans
      (LinearInputConsequences.global_minimum_iff_input_and_margin hlam))

/-- Existence of a supporting input is the already proved quartic realizability test. -/
theorem exists_quartic_support_iff {lam r a : ℝ} (hlam : 0 < lam) :
    (∃ u : ℝ, ∀ x : ℝ, u * (x - a) ≤
      (lam * x ^ 4 / 4 + r * x ^ 2 / 2) -
      (lam * a ^ 4 / 4 + r * a ^ 2 / 2)) ↔
    0 ≤ lam * a ^ 2 + r := by
  constructor
  · rintro ⟨u, hu⟩
    exact ((quartic_support_iff_input_and_margin hlam).mp hu).2
  · intro hm
    exact ⟨input lam r a,
      (quartic_support_iff_input_and_margin hlam).mpr ⟨rfl, hm⟩⟩

/-- Positive margin is sufficient for strict support. It is not claimed necessary:
at lam > 0, r = a = 0 the quartic still has a unique minimum. -/
theorem strict_quartic_support_of_margin_pos {lam r a : ℝ} (hlam : 0 ≤ lam)
    (hmargin : 0 < lam * a ^ 2 + r) :
    ∀ x : ℝ, x ≠ a → input lam r a * (x - a) <
      (lam * x ^ 4 / 4 + r * x ^ 2 / 2) -
      (lam * a ^ 4 / 4 + r * a ^ 2 / 2) := by
  apply (unique_minimum_iff_strict_support
    (fun t : ℝ => lam * t ^ 4 / 4 + r * t ^ 2 / 2) a (input lam r a)).mp
  have hfull := globalMin_of_margin hlam (le_of_lt hmargin)
  have hmin := (quartic_minimum_iff_full lam r (input lam r a) a).mpr hfull
  refine ⟨hmin, ?_⟩
  intro x hx
  have he : E lam r (input lam r a) x (Real.sqrt 2 * x) =
      E lam r (input lam r a) a (Real.sqrt 2 * a) := by
    simpa [E, f, energy] using le_antisymm (hx a) (hmin x)
  exact (unique_of_margin_pos hlam hmargin he).1

end LinearInputMinimum
