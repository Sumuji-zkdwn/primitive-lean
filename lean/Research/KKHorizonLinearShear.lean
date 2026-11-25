import Mathlib.Tactic

/-!
Algebraic certificates for the Fourier indicial polynomial and the leading
tidal shear coefficient of the compact-circle horizon test. The tensor,
gauge, and ODE regular-singular calculations are separate SymPy/hand checks;
no Lean assertion of a GR instability theorem.
-/

namespace KKHorizonLinearShear

theorem indicial_factor (a q : ℂ) :
    a * (a - 1) + (1 + Complex.I * q) * a =
      a * (a + Complex.I * q) := by ring

theorem indicial_roots (a q : ℂ) :
    a * (a - 1) + (1 + Complex.I * q) * a = 0 ↔
      a = 0 ∨ a = -(Complex.I * q) := by
  rw [indicial_factor, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      linear_combination h
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h]
      ring

theorem tidal_norm_square (q : ℝ) :
    (-q ^ 2) ^ 2 + q ^ 2 = q ^ 2 * (1 + q ^ 2) := by ring

theorem tidal_coefficient_nonzero (q : ℝ) (hq : q ≠ 0) :
    0 < q ^ 2 * (1 + q ^ 2) := by
  exact mul_pos (sq_pos_of_ne_zero hq) (by positivity)

theorem exact_shear_without_backreaction_frozen
    (pr pv : ℝ) (hr : -2 * pr ^ 2 = 0) (hv : -2 * pv ^ 2 = 0) :
    pr = 0 ∧ pv = 0 := by
  have hpr : pr * pr = 0 := by nlinarith
  have hpv : pv * pv = 0 := by nlinarith
  exact ⟨(mul_eq_zero.mp hpr).elim id id, (mul_eq_zero.mp hpv).elim id id⟩

end KKHorizonLinearShear
