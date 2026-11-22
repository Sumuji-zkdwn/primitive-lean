import Mathlib.Tactic

/-!
# Algebraic certificates for a finite SU(2) cube unwinding counterexample

These are exact elementary identities used by the independent finite-cube
oracle. They do NOT formalize S³ path-connectedness, all six faces, a smooth
Skyrme energy, a topological degree, or any Einstein/particle field equation.
-/

namespace FiniteSkyrmeUnwinding

/-- A rational semicircle parameterization has unit-length numerator. -/
theorem rational_unit_numerator (s : ℝ) :
    (2 * s - 1) ^ 2 + (2 * s * (1 - s)) ^ 2 =
      (s ^ 2 + (1 - s) ^ 2) ^ 2 := by
  ring

/-- The denominator of this rational parameterization is never zero. -/
theorem rational_denominator_pos (s : ℝ) :
    0 < s ^ 2 + (1 - s) ^ 2 := by
  nlinarith [sq_nonneg (s - (1 / 2 : ℝ))]

/-- A rank-one face has zero Gram determinant and zero Skyrme-like area. -/
theorem rank_one_face_area_zero (r : ℝ) :
    r * r * (r * r) - (r * r) ^ 2 = 0 := by
  ring

/-- Energy of one perturbed site on the cube, where three edges meet it
    and the face quartic vanishes identically. -/
def oneSiteEnergy (a overlap : ℝ) : ℝ :=
  3 * a * (1 - overlap)

theorem antipode_energy (a : ℝ) :
    oneSiteEnergy a (-1) = 6 * a := by
  unfold oneSiteEnergy
  ring

theorem quarter_turn_energy (a : ℝ) :
    oneSiteEnergy a 0 = 3 * a := by
  unfold oneSiteEnergy
  ring

theorem vacuum_energy (a : ℝ) :
    oneSiteEnergy a 1 = 0 := by
  simp [oneSiteEnergy]

/-- Explicit admissible finite deformation lowers energy for a>0. -/
theorem antipode_not_minimal (a : ℝ) (ha : 0 < a) :
    oneSiteEnergy a 0 < oneSiteEnergy a (-1) := by
  rw [quarter_turn_energy, antipode_energy]
  linarith

/-- Norm square of a difference of two unit vectors if their dot
    product is c; the universal range c∈[-1,1] bounds it by four. -/
theorem unit_edge_diff_bound (c : ℝ) (hlo : -1 ≤ c) (hhi : c ≤ 1) :
    0 ≤ 2 * (1 - c) ∧ 2 * (1 - c) ≤ 4 := by
  constructor <;> linarith

end FiniteSkyrmeUnwinding
