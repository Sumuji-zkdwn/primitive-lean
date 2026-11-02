/- This Lean fragment is appended after the three independently checked modules
by verify_lean.py. All.lean is the standalone compilation entry point. -/

namespace LinearInputConsequences
open LinearInputDesign

/-- An arbitrary input making the target a global minimum must be the design input.
This uses the actual derivative and Fermat's theorem, not a stationarity hypothesis. -/
theorem global_minimum_forces_design {lam r u a : ℝ}
    (hmin : ∀ x y : ℝ, E lam r u a (Real.sqrt 2 * a) ≤ E lam r u x y) :
    u = input lam r a := by
  apply LinearInputCalculus.global_minimum_forces_input
    (lam := lam) (r := r) (a := a)
  intro t
  have ht := hmin t (Real.sqrt 2 * t)
  simpa [E, f, LinearInputCalculus.potential] using ht

/-- Full characterization for an arbitrary input, not only a preselected input. -/
theorem global_minimum_iff_input_and_margin {lam r u a : ℝ} (hlam : 0 < lam) :
    (∀ x y : ℝ, E lam r u a (Real.sqrt 2 * a) ≤ E lam r u x y) ↔
      u = input lam r a ∧ 0 ≤ lam * a ^ 2 + r := by
  constructor
  · intro h
    have hu := global_minimum_forces_design h
    refine ⟨hu, ?_⟩
    rw [hu] at h
    exact margin_of_globalMin hlam h
  · rintro ⟨hu, hm⟩
    rw [hu]
    exact globalMin_of_margin (le_of_lt hlam) hm

/-- Realizability of a prescribed location by some linear input is exactly the margin test. -/
theorem exists_input_global_minimum_iff {lam r a : ℝ} (hlam : 0 < lam) :
    (∃ u : ℝ, ∀ x y : ℝ,
      E lam r u a (Real.sqrt 2 * a) ≤ E lam r u x y) ↔
      0 ≤ lam * a ^ 2 + r := by
  constructor
  · rintro ⟨u, hu⟩
    exact ((global_minimum_iff_input_and_margin hlam).mp hu).2
  · intro hm
    exact ⟨input lam r a, globalMin_of_margin (le_of_lt hlam) hm⟩

end LinearInputConsequences
