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


/-- A closed interval ball on the real line. -/
def lineBall (c r : ℝ) : Set ℝ := {z | |z - c| ≤ r}

/-- The quantitative D^3 lower radial comparison at the level of ONE
admissible sweep interval. Unlike an abstract transfer axiom, the proof
explicitly uses the fivefold inclusion and exactly three doubling steps.

The hypotheses on M and F are supplied here: applying the result to the
actual Stieltjes measure on the infinite Laakso quotient remains separate.
-/
theorem radial_mass_le_calibrated_sweep
    (M : Set ℝ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hmono : ∀ A B : Set ℝ, A ⊆ B → M A ≤ M B)
    (hdouble : ∀ c r : ℝ, 0 < r →
      M (lineBall c (2 * r)) ≤ D * M (lineBall c r))
    (F : ℝ → ℝ) (hF : Monotone F)
    (l u x y R : ℝ)
    (hl : l < u)
    (hlx : l ≤ x) (hxu : x ≤ u)
    (hly : l ≤ y) (hyu : y ≤ u)
    (hcost : R ≤ sweep l u x y)
    (hinterval : M (lineBall ((l + u) / 2) ((u - l) / 2)) = F u - F l) :
    M (lineBall x R) ≤ D ^ 3 * sweep (F l) (F u) (F x) (F y) := by
  let c : ℝ := (l + u) / 2
  let r : ℝ := (u - l) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hsubset : lineBall x R ⊆ lineBall c (8 * r) := by
    intro z hz
    change |z - x| ≤ R at hz
    change |z - c| ≤ 8 * r
    have hw := window_in_fivefold_interval l u x y R z
      hlx hxu hly hyu hcost hz
    dsimp [c, r]
    linarith
  have hiter : M (lineBall c (8 * r)) ≤ D ^ 3 * M (lineBall c r) := by
    calc
      M (lineBall c (8 * r)) =
          M (lineBall c (2 * (4 * r))) := by
            congr 1
            ring
      _ ≤ D * M (lineBall c (4 * r)) :=
        hdouble c (4 * r) (by positivity)
      _ = D * M (lineBall c (2 * (2 * r))) := by
        congr 1
        ring
      _ ≤ D * (D * M (lineBall c (2 * r))) :=
        mul_le_mul_of_nonneg_left
          (hdouble c (2 * r) (by positivity)) hD
      _ ≤ D * (D * (D * M (lineBall c r))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hdouble c r hr) hD) hD
      _ = D ^ 3 * M (lineBall c r) := by ring
  have hm : M (lineBall c r) = F u - F l := by
    simpa only [c, r] using hinterval
  calc
    M (lineBall x R) ≤ M (lineBall c (8 * r)) :=
      hmono _ _ hsubset
    _ ≤ D ^ 3 * M (lineBall c r) := hiter
    _ = D ^ 3 * (F u - F l) := by rw [hm]
    _ ≤ D ^ 3 * sweep (F l) (F u) (F x) (F y) :=
      mul_le_mul_of_nonneg_left
        (calibrated_sweep_lower F hF l u x y hlx hxu hly hyu)
        (pow_nonneg hD _)

#print axioms radial_mass_le_calibrated_sweep

#print axioms sweep_bounds
#print axioms calibrated_sweep_lower
#print axioms window_in_fivefold_interval

end LaaksoSweepBounds
