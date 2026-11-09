import KerrKoopman.AnalyticDuhamel
import KerrKoopman.AnalyticLpMap

/-! Actual two-branch, all-mode physical-time Duhamel map. -/

namespace KerrKoopman.AnalyticFourierDuhamel

noncomputable section
open AnalyticDuhamel
open scoped ENNReal

def multiplier (k : ℤ) : ℂ := if k < 0 then Complex.I else -Complex.I

theorem multiplier_norm (k : ℤ) : ‖multiplier k‖ = 1 := by
  unfold multiplier
  split_ifs <;> simp

/-- The damping-integral frequency |k| is converted to the actual -ik. -/
theorem multiplier_frequency (k : ℤ) :
    multiplier k * (|(k : ℝ)| : ℝ) = -Complex.I * (k : ℂ) := by
  unfold multiplier
  split_ifs with hk
  · have hkr : (k : ℝ) < 0 := by exact_mod_cast hk
    rw [abs_of_neg hkr]
    push_cast
    ring
  · have hkr : 0 ≤ (k : ℝ) := by exact_mod_cast (le_of_not_gt hk)
    rw [abs_of_nonneg hkr]
    push_cast
    ring

def mode (T : ℝ) (hT : 0 ≤ T) (β c : ℝ) (hβ : 0 < β) (k : ℤ) :
    C(Time T, ℂ) →L[ℝ] C(Time T, ℂ) :=
  multiplier k • oscillatoryCLM T hT β |(k : ℝ)| (c * k) hβ (abs_nonneg _)

theorem mode_norm_le (T : ℝ) (hT : 0 ≤ T) (β c : ℝ) (hβ : 0 < β) (k : ℤ)
    (f : C(Time T, ℂ)) : ‖mode T hT β c hβ k f‖ ≤ β⁻¹ * ‖f‖ := by
  change ‖multiplier k • (oscillatoryCLM T hT β |(k : ℝ)| (c * k) hβ (abs_nonneg _) f)‖ ≤ _
  rw [norm_smul, multiplier_norm, one_mul]
  exact oscillatoryCLM_norm_le T hT β |(k : ℝ)| (c * k) hβ (abs_nonneg _) f

def pairTrace {T : ℝ} (f g : C(Time T, ℂ)) : C(Time T, ℂ × ℂ) where
  toFun t := (f t, g t)
  continuous_toFun := f.continuous.prodMk g.continuous

def pairModeLinear (T : ℝ) (hT : 0 ≤ T) (β c : ℝ) (hβ : 0 < β) (k : ℤ) :
    C(Time T, ℂ) →ₗ[ℝ] C(Time T, ℂ × ℂ) where
  toFun f := pairTrace (mode T hT β c hβ k f) (mode T hT β (-c) hβ k f)
  map_add' f g := by ext t <;> simp [pairTrace]
  map_smul' a f := by ext t <;> simp [pairTrace] <;> rfl

theorem pairModeLinear_norm_le (T : ℝ) (hT : 0 ≤ T) (β c : ℝ) (hβ : 0 < β) (k : ℤ)
    (f : C(Time T, ℂ)) : ‖pairModeLinear T hT β c hβ k f‖ ≤ β⁻¹ * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (inv_nonneg.mpr hβ.le) (norm_nonneg _))).mpr
  intro t
  change ‖(mode T hT β c hβ k f t, mode T hT β (-c) hβ k f t)‖ ≤ _
  rw [Prod.norm_def]
  exact max_le
    (((mode T hT β c hβ k f).norm_coe_le_norm t).trans (mode_norm_le T hT β c hβ k f))
    (((mode T hT β (-c) hβ k f).norm_coe_le_norm t).trans (mode_norm_le T hT β (-c) hβ k f))

def pairMode (T : ℝ) (hT : 0 ≤ T) (β c : ℝ) (hβ : 0 < β) (k : ℤ) :
    C(Time T, ℂ) →L[ℝ] C(Time T, ℂ × ℂ) :=
  (pairModeLinear T hT β c hβ k).mkContinuous β⁻¹
    (pairModeLinear_norm_le T hT β c hβ k)

theorem pairMode_opNorm_le (T : ℝ) (hT : 0 ≤ T) (β c : ℝ) (hβ : 0 < β) (k : ℤ) :
    ‖pairMode T hT β c hβ k‖ ≤ β⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hβ.le)
    (pairModeLinear_norm_le T hT β c hβ k)

/-- Both characteristic branches and all integer modes, with no mode cutoff. -/
def duhamel (T : ℝ) (hT : 0 ≤ T) (β c : ℝ) (hβ : 0 < β) :
    AnalyticLpMap.L1 ℤ C(Time T, ℂ) →L[ℝ] AnalyticLpMap.L1 ℤ C(Time T, ℂ × ℂ) :=
  AnalyticLpMap.diagonal (pairMode T hT β c hβ) β⁻¹ (pairMode_opNorm_le T hT β c hβ)

theorem duhamel_opNorm_le (T : ℝ) (hT : 0 ≤ T) (β c : ℝ) (hβ : 0 < β) :
    ‖duhamel T hT β c hβ‖ ≤ β⁻¹ :=
  AnalyticLpMap.diagonal_opNorm_le _ _ (inv_nonneg.mpr hβ.le) (pairMode_opNorm_le T hT β c hβ)

theorem duhamel_apply (T : ℝ) (hT : 0 ≤ T) (β c : ℝ) (hβ : 0 < β)
    (f : AnalyticLpMap.L1 ℤ C(Time T, ℂ)) (k : ℤ) (t : Time T) :
    duhamel T hT β c hβ f k t =
      (mode T hT β c hβ k (f k) t, mode T hT β (-c) hβ k (f k) t) := rfl

end
end KerrKoopman.AnalyticFourierDuhamel
