
/-! An explicit mixed-wave input belongs to the common analytic class. -/

namespace KerrKoopman.ExplicitAnalyticInput

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AnalyticLift AnalyticReality
open scoped ENNReal

def c : ℝ := 1 / Real.sqrt 2

/-- The k=1 coefficients of h plus or minus c*d for d=cos(x)/25,
h=3*sin(x)/100. The negative coefficient is its complex conjugate. -/
def positive : ℂ × ℂ :=
  ((c : ℂ) / 50 - (3 / 200 : ℂ) * Complex.I,
   -(c : ℂ) / 50 - (3 / 200 : ℂ) * Complex.I)

def weightedPositive : ℂ × ℂ := (Real.exp (1 / 2) : ℝ) • positive

def initial : Initial :=
  lp.single 1 (1 : ℤ) weightedPositive + lp.single 1 (-1 : ℤ) (star weightedPositive)

theorem c_nonneg : 0 ≤ c := by unfold c; positivity

theorem c_le_one : c ≤ 1 := by
  have h := inverse_sqrt_two_le
  change 1 / Real.sqrt 2 ≤ 1
  linarith

theorem positive_norm_le : ‖positive‖ ≤ 7 / 200 := by
  have hc : ‖(c : ℂ) / 50‖ ≤ 1 / 50 := by
    have he : ‖(c : ℂ) / 50‖ = c / 50 := by
      norm_num [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg c_nonneg]
    rw [he]
    exact div_le_div_of_nonneg_right c_le_one (by norm_num : (0 : ℝ) ≤ 50)
  have hi : ‖(3 / 200 : ℂ) * Complex.I‖ = 3 / 200 := by norm_num
  change max ‖(c : ℂ) / 50 - (3 / 200 : ℂ) * Complex.I‖
    ‖-(c : ℂ) / 50 - (3 / 200 : ℂ) * Complex.I‖ ≤ 7 / 200
  apply max_le
  · exact (norm_sub_le _ _).trans (by linarith)
  · have hn : ‖-(c : ℂ) / 50‖ ≤ 1 / 50 := by simpa only [neg_div, norm_neg] using hc
    exact (norm_sub_le _ _).trans (by linarith)

theorem weightedPositive_norm_le : ‖weightedPositive‖ ≤ 21 / 200 := by
  have he : Real.exp (1 / 2) ≤ 3 :=
    (Real.exp_le_exp.mpr (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans Real.exp_one_lt_three.le
  rw [weightedPositive, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ 3 * (7 / 200 : ℝ) := mul_le_mul he positive_norm_le (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem paired_single_norm_le (a : ℂ × ℂ) :
    ‖(lp.single 1 (1 : ℤ) a + lp.single 1 (-1 : ℤ) (star a) : Initial)‖ ≤ 2 * ‖a‖ := by
  have hp : ‖(lp.single 1 (1 : ℤ) a : Initial)‖ = ‖a‖ :=
    lp.norm_single (E := fun _ : ℤ => ℂ × ℂ) (by norm_num) 1 a
  have hm : ‖(lp.single 1 (-1 : ℤ) (star a) : Initial)‖ = ‖a‖ := by
    exact (lp.norm_single (E := fun _ : ℤ => ℂ × ℂ) (by norm_num) (-1) (star a)).trans
      (norm_star a)
  calc
    _ ≤ ‖(lp.single 1 (1 : ℤ) a : Initial)‖ + ‖(lp.single 1 (-1 : ℤ) (star a) : Initial)‖ :=
      norm_add_le _ _
    _ = 2 * ‖a‖ := by rw [hp, hm]; ring

theorem initial_norm_le : ‖initial‖ ≤ 57 / 250 := by
  apply (paired_single_norm_le weightedPositive).trans
  linarith [weightedPositive_norm_le]

theorem initial_hermitian : HermitianInitial initial := by
  intro k
  by_cases hp : k = 1
  · subst k
    simp [initial, Pi.add_apply, lp.single_apply]
  by_cases hn : k = -1
  · subst k
    simp [initial, Pi.add_apply, lp.single_apply]
  have hnp : -k ≠ 1 := by omega
  have hnn : -k ≠ -1 := by omega
  simp [initial, Pi.add_apply, lp.single_apply, hp, hn, hnp, hnn]

end
end KerrKoopman.ExplicitAnalyticInput
