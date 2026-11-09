
/-! Analytic construction: the actual all-mode mild solution preserves the conjugate
symmetry needed for real physical fields. -/

namespace KerrKoopman.AnalyticReality

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory AnalyticLift AnalyticFixedPoint AnalyticAssembly
  Phase3PolynomialInverse Phase3WeightedConvolution Phase3WeightedReality
open scoped Topology

variable {I : Type*} [TopologicalSpace I] [CompactSpace I]

theorem correction_hermitian (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    {u : L1 C(I, ℂ)} (hu : Hermitian u) :
    Hermitian (correction (twistedProductReal ρ hρ) u) :=
  ((hu.product ρ hρ hu).smul (1 / 2)).add
    ((hu.product ρ hρ (hu.product ρ hρ hu)).smul (1 / 6))

theorem inverseStep_hermitian (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    {d u : L1 C(I, ℂ)} (hd : Hermitian d) (hu : Hermitian u) :
    Hermitian (inverseStep (twistedProductReal ρ hρ) d u) := by
  have h := (hd.smul (1 / 2)).add ((correction_hermitian ρ hρ hu).smul (-1))
  simpa only [inverseStep, neg_one_smul, sub_eq_add_neg] using h

theorem inverse_hermitian (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (d : L1 C(I, ℂ)) (hd : ‖d‖ ≤ 134 / 375) (hdH : Hermitian d) :
    Hermitian (inverse (twistedProductReal ρ hρ) (twistedProductReal_norm_le ρ hρ) d hd) := by
  have hit (n : ℕ) : Hermitian ((inverseStep (twistedProductReal ρ hρ) d)^[n] 0) := by
    induction n with
    | zero => exact hermitian_zero
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact inverseStep_hermitian ρ hρ hdH ih
  exact isClosed_hermitian.mem_of_tendsto
    (iterates_tendsto_inverse (twistedProductReal ρ hρ) (twistedProductReal_norm_le ρ hρ) d hd)
    (Filter.Eventually.of_forall hit)

theorem nonlinear_hermitian (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (d : L1 C(I, ℂ)) (hd : ‖d‖ ≤ 134 / 375) (hdH : Hermitian d) :
    Hermitian (nonlinear (twistedProductReal ρ hρ) (twistedProductReal_norm_le ρ hρ) d hd) := by
  simpa only [nonlinear, neg_one_smul] using
    (correction_hermitian ρ hρ (inverse_hermitian ρ hρ d hd hdH)).smul (-1)

def HermitianPair (T : ℝ) (u : Branches T) : Prop := ∀ k t, u (-k) t = star (u k t)

def HermitianInitial (a : Initial) : Prop := ∀ k, a (-k) = star (a k)

theorem hermitianPair_zero (T : ℝ) : HermitianPair T 0 := by
  intro k t
  simp

theorem HermitianPair.add {T : ℝ} {u v : Branches T}
    (hu : HermitianPair T u) (hv : HermitianPair T v) : HermitianPair T (u + v) := by
  intro k t
  simpa using congrArg₂ (· + ·) (hu k t) (hv k t)

theorem isClosed_hermitianPair (T : ℝ) : IsClosed {u : Branches T | HermitianPair T u} := by
  simp only [HermitianPair, Set.setOf_forall]
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro t
  let ev (j : ℤ) : Branches T →L[ℝ] (ℂ × ℂ) :=
    (ContinuousMap.evalCLM ℝ t).comp (lp.evalCLM ℝ (fun _ : ℤ => C(Time T, ℂ × ℂ)) 1 j)
  exact isClosed_eq (ev (-k)).continuous ((ev k).continuous.star)

theorem waveFactor_neg (T β c : ℝ) (k : ℤ) (σ : ℝ) (t : Time T) :
    waveFactor T β c (-k) σ t = star (waveFactor T β c k σ t) := by
  simp only [waveFactor, ContinuousMap.coe_mk, Int.cast_neg, abs_neg,
    star_mul, Complex.star_def, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  rw [mul_comm]
  congr 1
  simp

theorem freeLift_hermitian (T β c : ℝ) (hβ : 0 ≤ β) (a : Initial)
    (ha : HermitianInitial a) : HermitianPair T (freeLift T β c hβ a) := by
  intro k t
  rw [freeLift_apply, freeLift_apply, ha k, waveFactor_neg, waveFactor_neg]
  ext <;> simp [star_mul, mul_comm]

theorem displacement_hermitian (T : ℝ) (z : Branches T) (hz : HermitianPair T z) :
    Hermitian (displacement T z) := by
  intro k t
  rw [displacement_apply, displacement_apply, hz k t]
  simp

theorem integral_star (a b : ℝ) (f : ℝ → ℂ) :
    (∫ s in a..b, star (f s)) = star (∫ s in a..b, f s) := by
  change (∫ s in Ioc a b, star (f s)) - (∫ s in Ioc b a, star (f s)) =
    star ((∫ s in Ioc a b, f s) - (∫ s in Ioc b a, f s))
  rw [star_sub]
  exact congrArg₂ (· - ·) integral_conj integral_conj

theorem oneMode_star (T : ℝ) (hT : 0 ≤ T) (β ν : ℝ) (f : C(Time T, ℂ)) :
    AnalyticDuhamel.oneMode T hT β ν (star f) = star (AnalyticDuhamel.oneMode T hT β ν f) := by
  ext t
  change (ν * Real.exp (-β * (t : ℝ) * ν)) •
      (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (β * s * ν) • star (AnalyticDuhamel.extend T hT f s)) =
    star ((ν * Real.exp (-β * (t : ℝ) * ν)) •
      (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (β * s * ν) • AnalyticDuhamel.extend T hT f s))
  rw [star_smul, star_trivial]
  congr 1
  rw [← integral_star]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [star_smul, star_trivial]

theorem phase_star (T ω : ℝ) : star (AnalyticDuhamel.phase T ω) = AnalyticDuhamel.phase T (-ω) := by
  ext t
  simp only [AnalyticDuhamel.phase, ContinuousMap.star_apply, ContinuousMap.coe_mk,
    Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp

theorem oscillatory_star (T : ℝ) (hT : 0 ≤ T) (β ν ω : ℝ)
    (hβ : 0 < β) (hν : 0 ≤ ν) (f : C(Time T, ℂ)) :
    AnalyticDuhamel.oscillatoryCLM T hT β ν (-ω) hβ hν (star f) =
      star (AnalyticDuhamel.oscillatoryCLM T hT β ν ω hβ hν f) := by
  change AnalyticDuhamel.phase T (-(-ω)) *
      AnalyticDuhamel.oneMode T hT β ν (AnalyticDuhamel.phase T (-ω) * star f) =
    star (AnalyticDuhamel.phase T (-ω) *
      AnalyticDuhamel.oneMode T hT β ν (AnalyticDuhamel.phase T ω * f))
  rw [star_mul, ← oneMode_star, star_mul, phase_star, phase_star, neg_neg]
  simp only [mul_comm]

theorem multiplier_neg (k : ℤ) (hk : k ≠ 0) :
    AnalyticFourierDuhamel.multiplier (-k) = star (AnalyticFourierDuhamel.multiplier k) := by
  unfold AnalyticFourierDuhamel.multiplier
  by_cases h : k < 0
  · have hn : ¬ -k < 0 := by omega
    rw [if_neg hn, if_pos h]
    simp
  · have hn : -k < 0 := by omega
    rw [if_pos hn, if_neg h]
    simp

theorem mode_zero (T : ℝ) (hT : 0 ≤ T) (β c : ℝ) (hβ : 0 < β) (f : C(Time T, ℂ)) :
    AnalyticFourierDuhamel.mode T hT β c hβ 0 f = 0 := by
  ext t
  simp [AnalyticFourierDuhamel.mode, AnalyticDuhamel.oscillatoryCLM,
    AnalyticDuhamel.oneModeCLM, AnalyticDuhamel.oneMode, AnalyticDuhamel.phaseCLM]

theorem mode_neg_star (T : ℝ) (hT : 0 ≤ T) (β c : ℝ) (hβ : 0 < β)
    (k : ℤ) (f : C(Time T, ℂ)) :
    AnalyticFourierDuhamel.mode T hT β c hβ (-k) (star f) =
      star (AnalyticFourierDuhamel.mode T hT β c hβ k f) := by
  by_cases hk : k = 0
  · subst k
    simp only [neg_zero, mode_zero, star_zero]
  · change AnalyticFourierDuhamel.multiplier (-k) •
        AnalyticDuhamel.oscillatoryCLM T hT β |((-k : ℤ) : ℝ)| (c * (-k : ℤ)) hβ _ (star f) =
      star (AnalyticFourierDuhamel.multiplier k •
        AnalyticDuhamel.oscillatoryCLM T hT β |(k : ℝ)| (c * k) hβ _ f)
    simp only [Int.cast_neg, abs_neg, mul_neg]
    rw [multiplier_neg k hk, oscillatory_star, star_smul]

theorem kernel_hermitian (T : ℝ) (hT : 0 ≤ T) (f : Scalar T) (hf : Hermitian f) :
    HermitianPair T (kernel T hT f) := by
  intro k t
  have heq : f (-k) = star (f k) := by ext s; exact hf k s
  change (AnalyticFourierDuhamel.mode T hT 1 (1 / Real.sqrt 2) _ (-k) (f (-k)) t,
      AnalyticFourierDuhamel.mode T hT 1 (-(1 / Real.sqrt 2)) _ (-k) (f (-k)) t) = _
  rw [heq, mode_neg_star, mode_neg_star]
  rfl

theorem iterateMap_hermitian (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5)
    (a : Initial) (ha : ‖a‖ ≤ 57 / 250) (haH : HermitianInitial a)
    (z : Ball (Branches T)) (hz : HermitianPair T z.val) :
    HermitianPair T (iterateMap T hT0 hT1 a ha z).val := by
  apply (freeLift_hermitian T 1 (1 / Real.sqrt 2) (by norm_num) a haH).add
  apply kernel_hermitian
  exact nonlinear_hermitian (width T) (width_nonneg T hT1)
    (displacement T z.val) _ (displacement_hermitian T z.val hz)

/-- The actually constructed fixed point is a real Fourier state. -/
theorem mildSolution_hermitian (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5)
    (a : Initial) (ha : ‖a‖ ≤ 57 / 250) (haH : HermitianInitial a) :
    HermitianPair T (mildSolution T hT0 hT1 a ha).val := by
  let z₀ : Ball (Branches T) := ⟨0, mem_closedBall_self (by norm_num)⟩
  have hit (n : ℕ) : HermitianPair T ((iterateMap T hT0 hT1 a ha)^[n] z₀).val := by
    induction n with
    | zero => exact hermitianPair_zero T
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact iterateMap_hermitian T hT0 hT1 a ha haH _ ih
  exact (isClosed_hermitianPair T).mem_of_tendsto
    (iterates_tendsto_mildSolution T hT0 hT1 a ha) (Filter.Eventually.of_forall hit)

end

end KerrKoopman.AnalyticReality
