import Mathlib.Tactic

/-! Algebraic subclaims of the exact 5D Bianchi V vacuum family.
The differential geometry and asymptotic limit are separate hand/SymPy work.
-/
namespace KKHorizonNonlinearBianchiV

theorem kasner_sum_numerator (B D P : ℝ) :
    B + ((D - B) / 2 + P) + ((D - B) / 2 - P) + (D - B) / 2 =
      (3 * D - B) / 2 := by ring

theorem kasner_square_residual (B D P : ℝ) :
    B^2 + ((D - B) / 2 + P)^2 + ((D - B) / 2 - P)^2 +
      ((D - B) / 2)^2 - ((3 * D - B) / 2)^2 =
      (-3 * D^2 + 3 * B^2 + 4 * P^2) / 2 := by ring

theorem shear_forces_D_gt_B (B D P : ℝ) (hB : 0 < B) (hD : 0 < D)
    (hP : P ≠ 0) (h : D^2 = B^2 + 4 * P^2 / 3) : B < D := by
  by_contra! hn
  have hprod : 0 ≤ (B - D) * (B + D) :=
    mul_nonneg (sub_nonneg.mpr hn) (by linarith)
  have hp : 0 < P^2 := sq_pos_of_ne_zero hP
  nlinarith [hprod, hp]

theorem z_exponent_between (B D : ℝ) (hB : 0 < B) (hD : B < D) :
    0 < (D - B) / (3 * D - B) ∧ (D - B) / (3 * D - B) < 1 := by
  have hden : 0 < 3 * D - B := by linarith
  exact ⟨div_pos (sub_pos.mpr hD) hden, (div_lt_one hden).2 (by linarith)⟩

theorem z_tidal_coefficient_positive (B D : ℝ) (hB : 0 < B) (hD : B < D) :
    0 < (D - B) / (3 * D - B) * (1 - (D - B) / (3 * D - B)) := by
  obtain ⟨hpos, hlt⟩ := z_exponent_between B D hB hD
  exact mul_pos hpos (sub_pos.mpr hlt)

end KKHorizonNonlinearBianchiV
