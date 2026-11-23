import Mathlib.Tactic

/-!
# Finite sweep inequalities for the Laakso gate quotient

This module proves pure real inequalities common to every admissible gate
interval. It does NOT formalize the existence of a gate path, a continuum
quotient metric, or doubling of the density.
-/

namespace LaaksoSweepBounds

/-- Starting at x, ending at y and visiting both endpoints l,u costs
two traversals minus the direct separation. -/
def sweep (l u x y : ℝ) : ℝ :=
  2 * (u - l) - |x - y|

theorem sweep_bounds (l u x y : ℝ)
    (hlx : l ≤ x) (hxu : x ≤ u)
    (hly : l ≤ y) (hyu : y ≤ u) :
    u - l ≤ sweep l u x y ∧ sweep l u x y ≤ 2 * (u - l) := by
  have hxy : |x - y| ≤ u - l := abs_le.mpr ⟨by linarith, by linarith⟩
  constructor
  · dsimp [sweep]
    linarith
  · dsimp [sweep]
    linarith [abs_nonneg (x - y)]

theorem calibrated_sweep_lower (F : ℝ → ℝ) (hF : Monotone F)
    (l u x y : ℝ) (hlx : l ≤ x) (hxu : x ≤ u)
    (hly : l ≤ y) (hyu : y ≤ u) :
    F u - F l ≤ sweep (F l) (F u) (F x) (F y) := by
  exact (sweep_bounds (F l) (F u) (F x) (F y)
    (hF hlx) (hF hxu) (hF hly) (hF hyu)).1

/-- Any admissible interval whose raw sweep cost dominates R is at
least R/2 wide. Hence an R-window at a point x in it lies in the
fivefold concentric dilation of that interval. -/
theorem window_in_fivefold_interval (l u x y R z : ℝ)
    (hlx : l ≤ x) (hxu : x ≤ u)
    (hly : l ≤ y) (hyu : y ≤ u)
    (hcost : R ≤ sweep l u x y)
    (hz : |z - x| ≤ R) :
    |z - (l + u) / 2| ≤ (5 / 2 : ℝ) * (u - l) := by
  have hbound := (sweep_bounds l u x y hlx hxu hly hyu).2
  have hR : R ≤ 2 * (u - l) := le_trans hcost hbound
  obtain ⟨hzlo, hzhi⟩ := abs_le.mp hz
  apply abs_le.mpr
  constructor <;> dsimp <;> linarith

#print axioms sweep_bounds
#print axioms calibrated_sweep_lower
#print axioms window_in_fivefold_interval

end LaaksoSweepBounds
