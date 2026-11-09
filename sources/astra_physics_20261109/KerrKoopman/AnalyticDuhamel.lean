import KerrKoopman.AnalyticKernel
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Complex.Trigonometric

/-! Actual bounded damped integration on continuous time traces. -/

namespace KerrKoopman.AnalyticDuhamel

noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev Time (T : ℝ) := Set.Icc (0 : ℝ) T

def extend (T : ℝ) (hT : 0 ≤ T) (f : C(Time T, E)) (t : ℝ) : E :=
  f (Set.projIcc 0 T hT t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuous_extend (T : ℝ) (hT : 0 ≤ T) (f : C(Time T, E)) :
    Continuous (extend T hT f) := f.continuous.comp continuous_projIcc

def primitive (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ) (f : C(Time T, E)) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, Real.exp (β * s * ν) • extend T hT f s

theorem continuous_primitive (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ) (f : C(Time T, E)) :
    Continuous (primitive T hT β ν f) := by
  have hc : Continuous (fun s => Real.exp (β * s * ν) • extend T hT f s) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (β * s * ν))).smul
      (continuous_extend T hT f)
  exact continuous_iff_continuousAt.mpr (fun t =>
    (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt)

def oneMode (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ) (f : C(Time T, E)) : C(Time T, E) where
  toFun t := (ν * Real.exp (-β * (t : ℝ) * ν)) • primitive T hT β ν f t
  continuous_toFun := by
    apply Continuous.smul
    · fun_prop
    · exact (continuous_primitive T hT β ν f).comp continuous_subtype_val

theorem oneMode_eq_integral (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ)
    (f : C(Time T, E)) (t : Time T) :
    oneMode T hT β ν f t =
      ∫ s in (0 : ℝ)..(t : ℝ),
        (ν * Real.exp (-β * ((t : ℝ) - s) * ν)) • extend T hT f s := by
  change (ν * Real.exp (-β * (t : ℝ) * ν)) •
    (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (β * s * ν) • extend T hT f s) = _
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [smul_smul]
  congr 1
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem oneMode_norm_le (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ)
    (hβ : 0 < β) (hν : 0 ≤ ν) (f : C(Time T, E)) :
    ‖oneMode T hT β ν f‖ ≤ β⁻¹ * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (inv_nonneg.mpr hβ.le) (norm_nonneg _))).mpr
  intro t
  rw [oneMode_eq_integral]
  have hi := Phase3AnalyticKernel.damped_integral_norm_le β ν t ‖f‖ hβ hν
    t.property.1 (norm_nonneg _) (extend T hT f)
    (fun s _ => f.norm_coe_le_norm (Set.projIcc 0 T hT s))
  exact hi.trans_eq (by ring)

theorem oneMode_add (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ) (f g : C(Time T, E)) :
    oneMode T hT β ν (f + g) = oneMode T hT β ν f + oneMode T hT β ν g := by
  ext t
  have cf : Continuous (fun s => Real.exp (β * s * ν) • extend T hT f s) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (β * s * ν))).smul
      (continuous_extend T hT f)
  have cg : Continuous (fun s => Real.exp (β * s * ν) • extend T hT g s) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (β * s * ν))).smul
      (continuous_extend T hT g)
  change Continuous (fun s => Real.exp (β * s * ν) • f (Set.projIcc 0 T hT s)) at cf
  change Continuous (fun s => Real.exp (β * s * ν) • g (Set.projIcc 0 T hT s)) at cg
  simp only [oneMode, ContinuousMap.coe_mk, ContinuousMap.add_apply, primitive, extend,
    smul_add]
  rw [intervalIntegral.integral_add (cf.intervalIntegrable _ _) (cg.intervalIntegrable _ _),
    smul_add]

theorem oneMode_smul (T : ℝ) (hT : 0 ≤ T) (β ν a : ℝ) (f : C(Time T, E)) :
    oneMode T hT β ν (a • f) = a • oneMode T hT β ν f := by
  ext t
  simp only [oneMode, ContinuousMap.coe_mk, ContinuousMap.smul_apply, primitive, extend]
  simp_rw [smul_comm (Real.exp _) a]
  rw [intervalIntegral.integral_smul, smul_comm]

/-- Actual continuous linear one-mode Duhamel operator; its norm is independent
of the mode frequency. A Fourier phase can be composed as an isometry. -/
def oneModeCLM (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ) (hβ : 0 < β) (hν : 0 ≤ ν) :
    C(Time T, E) →L[ℝ] C(Time T, E) :=
  LinearMap.mkContinuous
    { toFun := oneMode T hT β ν
      map_add' := oneMode_add T hT β ν
      map_smul' := fun a f => oneMode_smul T hT β ν a f }
    β⁻¹ (oneMode_norm_le T hT β ν hβ hν)

theorem oneModeCLM_norm_le (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ) (hβ : 0 < β) (hν : 0 ≤ ν) :
    ‖oneModeCLM (E := E) T hT β ν hβ hν‖ ≤ β⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hβ.le)
    (oneMode_norm_le T hT β ν hβ hν)

def phase (T ω : ℝ) : C(Time T, ℂ) where
  toFun t := Complex.exp (Complex.I * (ω * (t : ℝ) : ℝ))
  continuous_toFun := by fun_prop

theorem phase_norm_apply (T ω : ℝ) (t : Time T) : ‖phase T ω t‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_norm_le (T ω : ℝ) : ‖phase T ω‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro t
  exact le_of_eq (phase_norm_apply T ω t)

def phaseCLM (T ω : ℝ) : C(Time T, ℂ) →L[ℝ] C(Time T, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun f => phase T ω * f
      map_add' := fun f g => mul_add _ f g
      map_smul' := fun a f => by ext t; simp [mul_smul_comm] }
    1 (fun f => (norm_mul_le _ _).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (phase_norm_le T ω) (norm_nonneg f)))

theorem phaseCLM_norm_le (T ω : ℝ) (f : C(Time T, ℂ)) :
    ‖phaseCLM T ω f‖ ≤ ‖f‖ := by
  exact (norm_mul_le _ _).trans (by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (phase_norm_le T ω) (norm_nonneg f))

/-- Add the actual linear Fourier transport phase without changing the
shrinking-strip integration bound. -/
def oscillatoryCLM (T : ℝ) (hT : 0 ≤ T) (β ν ω : ℝ) (hβ : 0 < β) (hν : 0 ≤ ν) :
    C(Time T, ℂ) →L[ℝ] C(Time T, ℂ) :=
  (phaseCLM T (-ω)).comp ((oneModeCLM T hT β ν hβ hν).comp (phaseCLM T ω))

theorem oscillatoryCLM_norm_le (T : ℝ) (hT : 0 ≤ T) (β ν ω : ℝ)
    (hβ : 0 < β) (hν : 0 ≤ ν) (f : C(Time T, ℂ)) :
    ‖oscillatoryCLM T hT β ν ω hβ hν f‖ ≤ β⁻¹ * ‖f‖ := by
  apply (phaseCLM_norm_le T (-ω) _).trans
  apply (oneMode_norm_le T hT β ν hβ hν (phaseCLM T ω f)).trans
  exact mul_le_mul_of_nonneg_left (phaseCLM_norm_le T ω f) (inv_nonneg.mpr hβ.le)

theorem oscillatoryCLM_opNorm_le (T : ℝ) (hT : 0 ≤ T) (β ν ω : ℝ)
    (hβ : 0 < β) (hν : 0 ≤ ν) :
    ‖oscillatoryCLM T hT β ν ω hβ hν‖ ≤ β⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hβ.le)
    (oscillatoryCLM_norm_le T hT β ν ω hβ hν)

end
end KerrKoopman.AnalyticDuhamel
