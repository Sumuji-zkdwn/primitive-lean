import Mathlib.Tactic

/-! Algebraic certificates for the 2D EF block of the 5D vacuum
extension. This does not formalize manifolds, geodesics or causality. -/
namespace KKCircleHorizon

theorem ef_determinant (f : ℝ) :
    0 * f - (-1 : ℝ) * (-1) = -1 := by ring

theorem orbit_norm_sign_inside (r B : ℝ)
    (hr : 0 < r) (h : r ^ 2 < B) :
    (r ^ 2 - B) / r ^ 2 < 0 := by
  exact div_neg_of_neg_of_pos (sub_neg.mpr h) (by positivity)

theorem orbit_norm_sign_outside (r B : ℝ)
    (hr : 0 < r) (h : B < r ^ 2) :
    0 < (r ^ 2 - B) / r ^ 2 := by
  exact div_pos (sub_pos.mpr h) (by positivity)

theorem orbit_norm_at_horizon (r B : ℝ) (h : r ^ 2 = B) :
    (r ^ 2 - B) / r ^ 2 = 0 := by rw [h, sub_self, zero_div]

theorem ef_has_both_signs (f : ℝ) :
    (-2 * ((f + 1) / 2) + f < 0) ∧
    (0 < -2 * ((f - 1) / 2) + f) := by constructor <;> linarith

end KKCircleHorizon
