
/-! Actual real-field reconstruction from Hermitian analytic Fourier traces. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal

namespace KerrKoopman.Phase3WeightedRealDecode
open Phase3WeightedConvolution Phase3WeightedDecoder Phase3WeightedDerivative Phase3WeightedReality

variable {I : Type*} [TopologicalSpace I] [CompactSpace I]

def rawEvalCLM (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t) (t : I) (x : ℝ) :
    L1 C(I, ℂ) →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ (t, PUnit.unit.{1})).comp
    (fourierDecode ρ hρ (ContinuousMap.const PUnit.{1} x))

theorem rawEvalCLM_apply (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (t : I) (x : ℝ) (u : L1 C(I, ℂ)) : rawEvalCLM ρ hρ t x u = rawDecode ρ u t x :=
  fourierDecode_apply ρ hρ (ContinuousMap.const PUnit.{1} x) u (t, PUnit.unit)

theorem rawDecode_product (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (u v : L1 C(I, ℂ)) (t : I) (x : ℝ) :
    rawDecode ρ (twistedProductReal ρ hρ u v) t x = rawDecode ρ u t x * rawDecode ρ v t x := by
  have h := congrArg (fun f : C(I × PUnit.{1}, ℂ) => f (t, PUnit.unit))
    (fourierDecode_product ρ hρ (ContinuousMap.const PUnit.{1} x) u v)
  simpa only [fourierDecode_apply, ContinuousMap.mul_apply, ContinuousMap.const_apply] using h

theorem modeValue_neg_star (r : ℝ) (k : ℤ) (a : ℂ) (x : ℝ) :
    modeValue r (-k) (star a) x = star (modeValue r k a x) := by
  unfold modeValue
  change _ = (starRingEnd ℂ) (_ * a)
  rw [map_mul, ← Complex.exp_conj]
  congr 1
  congr 1
  simp

theorem rawDecode_star (ρ : C(I, ℝ)) {u : L1 C(I, ℂ)} (hu : Hermitian u) (t : I) (x : ℝ) :
    star (rawDecode ρ u t x) = rawDecode ρ u t x := by
  calc
    _ = ∑' k, star (modeValue (ρ t) k (u k t) x) := tsum_star
    _ = ∑' k, modeValue (ρ t) (-k) (u (-k) t) x := by
      apply tsum_congr
      intro k
      rw [hu k t]
      exact (modeValue_neg_star (ρ t) k (u k t) x).symm
    _ = rawDecode ρ u t x := tsum_comp_neg (fun k => modeValue (ρ t) k (u k t) x)

theorem rawDecode_im_zero (ρ : C(I, ℝ)) {u : L1 C(I, ℂ)} (hu : Hermitian u) (t : I) (x : ℝ) :
    (rawDecode ρ u t x).im = 0 :=
  Complex.conj_eq_iff_im.mp (rawDecode_star ρ hu t x)

def realDecode (ρ : C(I, ℝ)) (u : L1 C(I, ℂ)) (t : I) (x : ℝ) : ℝ :=
  (rawDecode ρ u t x).re

def realDerivative (ρ : C(I, ℝ)) (u : L1 C(I, ℂ)) (t : I) (x : ℝ) : ℝ :=
  (rawDerivative ρ u t x).re

def realEvalCLM (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t) (t : I) (x : ℝ) :
    L1 C(I, ℂ) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((rawEvalCLM ρ hρ t x).restrictScalars ℝ)

theorem realEvalCLM_apply (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (t : I) (x : ℝ) (u : L1 C(I, ℂ)) : realEvalCLM ρ hρ t x u = realDecode ρ u t x := by
  change (rawEvalCLM ρ hρ t x u).re = _
  rw [rawEvalCLM_apply]
  rfl

theorem ofReal_realDecode (ρ : C(I, ℝ)) {u : L1 C(I, ℂ)} (hu : Hermitian u) (t : I) (x : ℝ) :
    (realDecode ρ u t x : ℂ) = rawDecode ρ u t x :=
  Complex.conj_eq_iff_re.mp (rawDecode_star ρ hu t x)

theorem realDecode_product (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    {u v : L1 C(I, ℂ)} (hu : Hermitian u) (hv : Hermitian v) (t : I) (x : ℝ) :
    realDecode ρ (twistedProductReal ρ hρ u v) t x = realDecode ρ u t x * realDecode ρ v t x := by
  unfold realDecode
  rw [rawDecode_product, Complex.mul_re, rawDecode_im_zero ρ hu, rawDecode_im_zero ρ hv]
  ring

theorem hasDerivAt_realDecode (ρ : C(I, ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ t, δ ≤ ρ t) (u : L1 C(I, ℂ)) (t : I) (x : ℝ) :
    HasDerivAt (realDecode ρ u t) (realDerivative ρ u t x) x := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_rawDecode ρ δ hδ hρ u t x)

theorem continuous_realDecode (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t) (u : L1 C(I, ℂ)) :
    Continuous (fun p : I × ℝ => realDecode ρ u p.1 p.2) :=
  Complex.continuous_re.comp (continuous_rawDecode ρ hρ u)

theorem continuous_realDerivative (ρ : C(I, ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ t, δ ≤ ρ t) (u : L1 C(I, ℂ)) :
    Continuous (fun p : I × ℝ => realDerivative ρ u p.1 p.2) :=
  Complex.continuous_re.comp (continuous_rawDerivative ρ δ hδ hρ u)

theorem realDecode_periodic (ρ : C(I, ℝ)) (u : L1 C(I, ℂ)) (t : I) :
    Function.Periodic (realDecode ρ u t) (2 * Real.pi) := by
  intro x
  exact congrArg Complex.re (rawDecode_periodic ρ u t x)

theorem realDerivative_periodic (ρ : C(I, ℝ)) (u : L1 C(I, ℂ)) (t : I) :
    Function.Periodic (realDerivative ρ u t) (2 * Real.pi) := by
  intro x
  exact congrArg Complex.re (rawDerivative_periodic ρ u t x)

theorem realDecode_norm_le (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (u : L1 C(I, ℂ)) (t : I) (x : ℝ) : ‖realDecode ρ u t x‖ ≤ ‖u‖ := by
  exact (Complex.abs_re_le_norm _).trans (rawDecode_norm_le ρ hρ u t x)

theorem realDerivative_norm_le (ρ : C(I, ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ t, δ ≤ ρ t) (u : L1 C(I, ℂ)) (t : I) (x : ℝ) :
    ‖realDerivative ρ u t x‖ ≤ (Real.exp (-1) / δ) * ‖u‖ := by
  exact (Complex.abs_re_le_norm _).trans (rawDerivative_norm_le ρ δ hδ hρ u t x)

end KerrKoopman.Phase3WeightedRealDecode
