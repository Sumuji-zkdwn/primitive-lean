import KerrKoopman.AnalyticModeODE
import KerrKoopman.AnalyticFourierDuhamel
import KerrKoopman.AnalyticLift

/-! Physical Fourier coefficients, with the artificial analytic-width damping
cancelled in the actual time derivative. -/

namespace KerrKoopman.AnalyticPhysicalMode

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AnalyticDuhamel AnalyticModeODE AnalyticFourierDuhamel

def freeWave (β ν ω : ℝ) (a : ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-β * t * ν) : ℂ) * phaseAt (-ω) t * a

theorem freeWave_hasDerivAt (β ν ω : ℝ) (a : ℂ) (t : ℝ) :
    HasDerivAt (freeWave β ν ω a)
      ((-(β * ν : ℝ) - Complex.I * (ω : ℂ)) * freeWave β ν ω a t) t := by
  have he := ((((hasDerivAt_id t).const_mul (-β)).mul_const ν).exp).ofReal_comp
  have hd := (he.mul (phaseAt_hasDerivAt (-ω) t)).mul_const a
  convert hd using 1
  simp only [freeWave, id_eq]
  push_cast
  ring

def damping (ρ₀ β ν t : ℝ) : ℂ := (Real.exp (-(ρ₀ - β * t) * ν) : ℂ)

theorem damping_hasDerivAt (ρ₀ β ν t : ℝ) :
    HasDerivAt (damping ρ₀ β ν) ((β * ν : ℝ) * damping ρ₀ β ν t) t := by
  have h := (((hasDerivAt_const t ρ₀).sub ((hasDerivAt_id t).const_mul β)).neg.mul_const ν).exp.ofReal_comp
  convert h using 1
  simp only [damping, id_eq, Pi.neg_apply, Pi.sub_apply]
  push_cast
  ring

def weightedTrace (T : ℝ) (hT : 0 ≤ T) (β ω : ℝ) (k : ℤ) (a : ℂ)
    (f : C(Time T, ℂ)) (t : ℝ) : ℂ :=
  freeWave β |(k : ℝ)| ω a t + multiplier k * rawOsc T hT β |(k : ℝ)| ω f t

theorem weightedTrace_hasDerivAt (T : ℝ) (hT : 0 ≤ T) (β ω : ℝ) (k : ℤ) (a : ℂ)
    (f : C(Time T, ℂ)) (t : Time T) :
    HasDerivAt (weightedTrace T hT β ω k a f)
      ((-(β * |(k : ℝ)| : ℝ) - Complex.I * (ω : ℂ)) * weightedTrace T hT β ω k a f t
        - Complex.I * (k : ℂ) * f t) (t : ℝ) := by
  have hd := (freeWave_hasDerivAt β |(k : ℝ)| ω a t).add
    ((rawOsc_hasDerivAt T hT β |(k : ℝ)| ω f t).const_mul (multiplier k))
  have hm := multiplier_frequency k
  convert hd using 1
  simp only [weightedTrace]
  push_cast at hm ⊢
  linear_combination -f t * hm

def physicalTrace (ρ₀ : ℝ) (T : ℝ) (hT : 0 ≤ T) (β ω : ℝ) (k : ℤ) (a : ℂ)
    (f : C(Time T, ℂ)) (t : ℝ) : ℂ :=
  damping ρ₀ β |(k : ℝ)| t * weightedTrace T hT β ω k a f t

/-- The shrinking analytic scale cancels; the derivative is in physical time. -/
theorem physicalTrace_hasDerivAt (ρ₀ : ℝ) (T : ℝ) (hT : 0 ≤ T) (β ω : ℝ)
    (k : ℤ) (a : ℂ) (f : C(Time T, ℂ)) (t : Time T) :
    HasDerivAt (physicalTrace ρ₀ T hT β ω k a f)
      (-Complex.I * (ω : ℂ) * physicalTrace ρ₀ T hT β ω k a f t -
        Complex.I * (k : ℂ) * (damping ρ₀ β |(k : ℝ)| t * f t)) (t : ℝ) := by
  have hd := (damping_hasDerivAt ρ₀ β |(k : ℝ)| t).mul
    (weightedTrace_hasDerivAt T hT β ω k a f t)
  convert hd using 1
  simp only [physicalTrace]
  push_cast
  ring

theorem freeWave_eq_waveFactor (T β c σ : ℝ) (k : ℤ) (a : ℂ) (t : Time T) :
    freeWave β |(k : ℝ)| (σ * c * k) a t = AnalyticLift.waveFactor T β c k σ t * a := by
  unfold freeWave phaseAt AnalyticLift.waveFactor
  simp only [ContinuousMap.coe_mk]
  congr 2
  congr 1
  push_cast
  ring

theorem weightedTrace_eq (T : ℝ) (hT : 0 ≤ T) (β c σ : ℝ) (hβ : 0 < β)
    (k : ℤ) (a : ℂ) (f : C(Time T, ℂ)) (t : Time T) :
    weightedTrace T hT β (σ * c * k) k a f t =
      AnalyticLift.waveFactor T β c k σ t * a + mode T hT β (σ * c) hβ k f t := by
  unfold weightedTrace
  rw [freeWave_eq_waveFactor T β c σ k a t]
  congr 1

end
end KerrKoopman.AnalyticPhysicalMode
