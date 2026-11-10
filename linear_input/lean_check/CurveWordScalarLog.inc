/-! The standard alternating logarithm and exponential power series are
compositional inverses. All statements concern actual Mathlib PowerSeries. -/

noncomputable section

namespace LinearInputCurveWordScalarLog

open PowerSeries

theorem derivative_log_mul_one_add_X :
    derivative ℝ (log ℝ) * (1 + PowerSeries.X) = (1 : PowerSeries ℝ) := by
  ext n
  rw [mul_add, mul_one, map_add]
  cases n with
  | zero => simp [PowerSeries.deriv_log]
  | succ n =>
    have hx : coeff (n + 1) (derivative ℝ (log ℝ) * PowerSeries.X) = coeff n (derivative ℝ (log ℝ)) := by
      simpa only [pow_one] using coeff_mul_X_pow (derivative ℝ (log ℝ)) 1 n
    rw [hx]
    simp [PowerSeries.deriv_log, pow_succ]

theorem logOf_exp : PowerSeries.logOf (exp ℝ) = (PowerSeries.X : PowerSeries ℝ) := by
  apply PowerSeries.derivative.ext
  · rw [logOf_eq, derivative_subst ℝ HasSubst.exp_sub_one, PowerSeries.derivative_X]
    have hh := congrArg (substAlgHom (HasSubst.exp_sub_one (A := ℝ))) derivative_log_mul_one_add_X
    simp only [map_mul, map_add, map_one, substAlgHom_X] at hh
    simp only [map_sub, derivative_exp, Derivation.map_one_eq_zero, sub_zero]
    convert hh using 1
    simp [coe_substAlgHom]
  · simp [constantCoeff_logOf]

theorem exp_subst_log : (exp ℝ).subst (log ℝ) = (1 + PowerSeries.X : PowerSeries ℝ) := by
  let P : PowerSeries ℝ := exp ℝ - 1
  have hP : P.constantCoeff = 0 := by simp [P]
  have hP1 : P.coeff 1 = 1 := by simp [P, coeff_exp]
  letI : Invertible (P.coeff 1) := hP1.symm ▸ invertibleOne
  have hPinv : P.subst P.substInv = PowerSeries.X := subst_substInv_right P hP
  have hlog : (log ℝ).subst P = PowerSeries.X := logOf_exp
  have he : log ℝ = P.substInv := by
    have hh := congrArg (fun f : PowerSeries ℝ => f.subst P.substInv) hlog
    dsimp only at hh
    rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hP) (hasSubst_substInv P),
      hPinv, X_subst, subst_X (hasSubst_substInv P)] at hh
    exact hh
  have h := hPinv
  rw [← he] at h
  dsimp only [P] at h
  rw [subst_sub HasSubst.log] at h
  have hone : (1 : PowerSeries ℝ).subst (log ℝ) = 1 := by
    rw [← coe_substAlgHom HasSubst.log, map_one]
  rw [hone] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

theorem coeff_log_real (n : ℕ) :
    coeff n (log ℝ) = (-1 : ℝ) ^ (n + 1) / (n : ℝ) := by
  by_cases hn : n = 0 <;> simp [coeff_log, hn]

theorem coeff_exp_real (n : ℕ) :
    coeff n (exp ℝ) = 1 / (n.factorial : ℝ) := by
  simp [coeff_exp]

end LinearInputCurveWordScalarLog
