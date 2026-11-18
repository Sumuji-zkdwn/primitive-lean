
/-! Actual time derivative of the damped integral trace. -/

namespace KerrKoopman.AnalyticModeODE

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory AnalyticDuhamel
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def rawMode (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ) (f : C(Time T, E)) (t : ℝ) : E :=
  (ν * Real.exp (-β * t * ν)) • primitive T hT β ν f t

theorem rawMode_eq (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ) (f : C(Time T, E)) (t : Time T) :
    rawMode T hT β ν f t = oneMode T hT β ν f t := rfl

omit [CompleteSpace E] in
theorem rawMode_zero (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ) (f : C(Time T, E)) :
    rawMode T hT β ν f 0 = 0 := by simp [rawMode, primitive]

theorem primitive_hasDerivAt (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ) (f : C(Time T, E)) (t : ℝ) :
    HasDerivAt (primitive T hT β ν f) (Real.exp (β * t * ν) • extend T hT f t) t := by
  have hc : Continuous (fun s => Real.exp (β * s * ν) • extend T hT f s) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (β * s * ν))).smul
      (continuous_extend T hT f)
  exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem rawMode_hasDerivAt (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ) (f : C(Time T, E)) (t : ℝ) :
    HasDerivAt (rawMode T hT β ν f)
      (ν • extend T hT f t - (β * ν) • rawMode T hT β ν f t) t := by
  have hs : HasDerivAt (fun s : ℝ => ν * Real.exp (-β * s * ν))
      (-(β * ν) * (ν * Real.exp (-β * t * ν))) t := by
    convert (((hasDerivAt_id t).const_mul (-β) |>.mul_const ν).exp.const_mul ν) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hp := primitive_hasDerivAt T hT β ν f t
  have hd := hs.smul hp
  have hc : (ν * Real.exp (-β * t * ν)) * Real.exp (β * t * ν) = ν := by
    rw [mul_assoc, ← Real.exp_add]
    simp
  convert hd using 1
  · rfl
  · simp only [rawMode, smul_smul]
    rw [hc]
    simp only [neg_mul, neg_smul, sub_eq_add_neg]

def phaseAt (ω t : ℝ) : ℂ := Complex.exp (Complex.I * (ω * t : ℝ))

theorem phaseAt_hasDerivAt (ω t : ℝ) :
    HasDerivAt (phaseAt ω) (Complex.I * (ω : ℂ) * phaseAt ω t) t := by
  have h := (((hasDerivAt_id t).const_mul ω).ofReal_comp.const_mul Complex.I).cexp
  convert h using 1
  · rfl
  · simp only [id_eq, phaseAt, mul_one]
    ring

theorem phaseAt_neg_mul (ω t : ℝ) : phaseAt (-ω) t * phaseAt ω t = 1 := by
  unfold phaseAt
  rw [← Complex.exp_add]
  push_cast
  ring_nf
  exact Complex.exp_zero

def rawOsc (T : ℝ) (hT : 0 ≤ T) (β ν ω : ℝ) (f : C(Time T, ℂ)) (t : ℝ) : ℂ :=
  phaseAt (-ω) t * rawMode T hT β ν (phaseCLM T ω f) t

theorem rawOsc_eq (T : ℝ) (hT : 0 ≤ T) (β ν ω : ℝ)
    (hβ : 0 < β) (hν : 0 ≤ ν) (f : C(Time T, ℂ)) (t : Time T) :
    rawOsc T hT β ν ω f t = oscillatoryCLM T hT β ν ω hβ hν f t := rfl

theorem extend_phase_at (T : ℝ) (hT : 0 ≤ T) (ω : ℝ)
    (f : C(Time T, ℂ)) (t : Time T) :
    extend T hT (phaseCLM T ω f) t = phaseAt ω t * f t := by
  simp [AnalyticDuhamel.extend, phaseCLM, phase, phaseAt, Set.projIcc_val]

theorem rawOsc_hasDerivAt (T : ℝ) (hT : 0 ≤ T) (β ν ω : ℝ)
    (f : C(Time T, ℂ)) (t : Time T) :
    HasDerivAt (rawOsc T hT β ν ω f)
      ((-Complex.I * (ω : ℂ) - (β * ν : ℝ)) * rawOsc T hT β ν ω f t + (ν : ℂ) * f t)
      (t : ℝ) := by
  have hd := (phaseAt_hasDerivAt (-ω) t).mul
    (rawMode_hasDerivAt T hT β ν (phaseCLM T ω f) t)
  have hi := phaseAt_neg_mul ω t
  convert hd using 1
  · rfl
  · simp only [rawOsc, extend_phase_at, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_mul]
    linear_combination -(ν : ℂ) * f t * hi

end
end KerrKoopman.AnalyticModeODE
