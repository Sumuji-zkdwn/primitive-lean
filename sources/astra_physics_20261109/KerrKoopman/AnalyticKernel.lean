import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
Analytic construction: exact one-mode shrinking-strip Duhamel estimates.
This component proves kernel estimates; the PDE theorem is in AnalyticPDE.
-/

namespace KerrKoopman.Phase3AnalyticKernel

open Set MeasureTheory
open scoped Topology

noncomputable section

/-- Exact mass of the damping kernel; no division by the mode frequency. -/
theorem kernel_integral (β ν t : ℝ) (hβ : 0 < β) :
    (∫ s in (0 : ℝ)..t, ν * Real.exp (-β * (t - s) * ν)) =
      (1 - Real.exp (-β * t * ν)) / β := by
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hd (s : ℝ) : HasDerivAt
      (fun r : ℝ => β⁻¹ * Real.exp (-β * (t - r) * ν))
      (ν * Real.exp (-β * (t - s) * ν)) s := by
    have h := ((((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-β)).mul_const ν).exp
    convert h.const_mul β⁻¹ using 1
    dsimp only [Pi.sub_apply, id_eq]
    field_simp
    ring
  have hc : Continuous (fun s : ℝ => ν * Real.exp (-β * (t - s) * ν)) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) (hc.intervalIntegrable 0 t)
  rw [hi]
  simp only [sub_self, mul_zero, zero_mul, Real.exp_zero, mul_one, sub_zero]
  ring

theorem kernel_integral_le (β ν t : ℝ) (hβ : 0 < β) :
    (∫ s in (0 : ℝ)..t, ν * Real.exp (-β * (t - s) * ν)) ≤ β⁻¹ := by
  rw [kernel_integral β ν t hβ]
  rw [← one_div]
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-β * t * ν)]) hβ.le

/-- The norm estimate used by each Fourier Duhamel mode. A transport phase
can be included in f because its complex norm is one. -/
theorem damped_integral_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (β ν t M : ℝ) (hβ : 0 < β) (hν : 0 ≤ ν)
    (ht : 0 ≤ t) (hM : 0 ≤ M) (f : ℝ → E)
    (hf : ∀ s ∈ Icc 0 t, ‖f s‖ ≤ M) :
    ‖∫ s in (0 : ℝ)..t, (ν * Real.exp (-β * (t - s) * ν)) • f s‖ ≤ M / β := by
  have hc : Continuous (fun s : ℝ => (ν * Real.exp (-β * (t - s) * ν)) * M) := by fun_prop
  have hn := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht
    (Filter.Eventually.of_forall (fun s hs => show
      ‖(ν * Real.exp (-β * (t - s) * ν)) • f s‖ ≤
        (ν * Real.exp (-β * (t - s) * ν)) * M from by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hν (Real.exp_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hf s ⟨hs.1.le, hs.2⟩)
        (mul_nonneg hν (Real.exp_nonneg _)))) (hc.intervalIntegrable 0 t)
  have hi : (∫ s in (0 : ℝ)..t, (ν * Real.exp (-β * (t - s) * ν)) * M) =
      (∫ s in (0 : ℝ)..t, ν * Real.exp (-β * (t - s) * ν)) * M :=
    intervalIntegral.integral_mul_const M _
  rw [hi] at hn
  calc
    _ ≤ (∫ s in (0 : ℝ)..t, ν * Real.exp (-β * (t - s) * ν)) * M := hn
    _ ≤ β⁻¹ * M := mul_le_mul_of_nonneg_right (kernel_integral_le β ν t hβ) hM
    _ = M / β := by ring

/-- A shrinking strip still gives a contractive convolution weight while its
width is nonnegative. This is the exact multiplier in weighted coordinates. -/
theorem convolution_weight_le (ρ : ℝ) (hρ : 0 ≤ ρ) (k l : ℤ) :
    Real.exp (ρ * (|((k + l : ℤ) : ℝ)| - |(k : ℝ)| - |(l : ℝ)|)) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply mul_nonpos_of_nonneg_of_nonpos hρ
  have h := abs_add_le (k : ℝ) (l : ℝ)
  push_cast
  linarith

end

end KerrKoopman.Phase3AnalyticKernel
