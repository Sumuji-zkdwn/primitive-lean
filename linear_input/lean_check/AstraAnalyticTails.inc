
/-! Actual circle Fourier reconstruction, trigonometric approximants and
orthogonal-projection residual bounds from analytic coefficient tails. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal
open MeasureTheory

namespace KerrKoopman.AnalyticTails
open Phase3WeightedConvolution Phase3WeightedDerivative Phase3WeightedRealDecode
open FourierProjection RealFourierDerivative

abbrev Circle := RealGalerkin.Circle

def circleMode (b : ℤ → ℂ) (k : ℤ) : C(Circle, ℂ) := b k • fourier k
def circleSum (b : ℤ → ℂ) : C(Circle, ℂ) := ∑' k, circleMode b k
def circleCutoff (N : ℕ) (b : ℤ → ℂ) : C(Circle, ℂ) := ∑ k ∈ frequencies N, circleMode b k
def circleL2 (b : ℤ → ℂ) : MaterialL2.RealCircleL2 :=
  realPart (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (circleSum b))
def realCircleSum (b : ℤ → ℂ) : C(Circle, ℝ) :=
  ⟨fun x => (circleSum b x).re, Complex.continuous_re.comp (circleSum b).continuous⟩

theorem realCircleSum_toLp (b : ℤ → ℂ) :
    ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ (realCircleSum b) = circleL2 b := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) AddCircle.haarAddCircle (realCircleSum b),
    realPart_ae (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (circleSum b)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSum b)] with x hx hy hz
  change _ = realPart (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (circleSum b)) x
  rw [hx, hy, hz]
  rfl

theorem fourier_norm_le (k : ℤ) : ‖(fourier k : C(Circle, ℂ))‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro x
  simp [fourier_apply]

theorem circleMode_norm_le (b : ℤ → ℂ) (k : ℤ) : ‖circleMode b k‖ ≤ ‖b k‖ := by
  rw [circleMode, norm_smul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (fourier_norm_le k) (norm_nonneg (b k))

theorem summable_circleMode_norm (b : ℤ → ℂ) (hb : Summable (fun k => ‖b k‖)) :
    Summable (fun k => ‖circleMode b k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (circleMode_norm_le b) hb

theorem circleSum_apply (b : ℤ → ℂ) (hb : Summable (fun k => ‖b k‖)) (x : Circle) :
    circleSum b x = ∑' k, b k * fourier k x := by
  change ContinuousMap.evalCLM ℂ x (∑' k, circleMode b k) = _
  rw [(ContinuousMap.evalCLM ℂ x).map_tsum (summable_circleMode_norm b hb).of_norm]
  rfl

theorem circle_tail_bound (N : ℕ) (b : ℤ → ℂ) (hb : Summable (fun k => ‖b k‖))
    (v : ℤ → ℝ) (hv : Summable v) (hv0 : ∀ k, 0 ≤ v k) (ε : ℝ) (hε : 0 ≤ ε)
    (htail : ∀ k, k ∉ frequencies N → ‖b k‖ ≤ ε * v k) :
    ‖circleSum b - circleCutoff N b‖ ≤ ε * ∑' k, v k := by
  classical
  have hs := summable_circleMode_norm b hb
  change ‖(∑' k, circleMode b k) - ∑ k ∈ frequencies N, circleMode b k‖ ≤ _
  rw [← hs.of_norm.sum_add_tsum_subtype_compl (frequencies N), add_sub_cancel_left]
  calc
    _ ≤ ∑' k : {k // k ∉ frequencies N}, ‖circleMode b k‖ := norm_tsum_le_tsum_norm (hs.subtype _)
    _ ≤ ∑' k : {k // k ∉ frequencies N}, ε * v k :=
      Summable.tsum_le_tsum (fun k => (circleMode_norm_le b k).trans (htail k k.property))
        (hs.subtype _) ((hv.subtype _).mul_left ε)
    _ = ε * ∑' k : {k // k ∉ frequencies N}, v k := tsum_mul_left
    _ ≤ ε * ∑' k, v k := by
      apply mul_le_mul_of_nonneg_left _ hε
      have he := hv.sum_add_tsum_subtype_compl (frequencies N)
      have hn : 0 ≤ ∑ k ∈ frequencies N, v k := Finset.sum_nonneg (fun k _ => hv0 k)
      linarith

theorem toLp_fourier (k : ℤ) :
    ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (fourier k : C(Circle, ℂ)) = basis k := by
  rw [basis, coe_fourierBasis]

theorem cutoff_real_mem (N : ℕ) (b : ℤ → ℂ) :
    realPart (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (circleCutoff N b)) ∈
      RealGalerkin.space N := by
  apply (RealFourierProjection.parts_mem N ?_).1
  simp only [circleCutoff, map_sum, circleMode, map_smul, toLp_fourier]
  apply Submodule.sum_mem
  intro k hk
  exact (bandlimited N).smul_mem (b k) (Submodule.subset_span ⟨k, hk, rfl⟩)

theorem toLp_norm_le (g : C(Circle, ℂ)) :
    ‖ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ g‖ ≤ ‖g‖ := by
  have hb : ‖(ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ :
      C(Circle, ℂ) →L[ℂ] FourierProjection.CircleL2)‖ ≤ 1 := by
    simpa [measureUnivNNReal] using (ContinuousMap.toLp_norm_le (α := Circle) (E := ℂ) (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle)
  exact (ContinuousLinearMap.le_opNorm _ g).trans (by simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg g))

theorem projection_best_approx (N : ℕ) (f g : MaterialL2.RealCircleL2) (hg : g ∈ RealGalerkin.space N) :
    ‖f - RealGalerkin.projection N f‖ ≤ ‖f - g‖ := by
  change ‖f - (RealGalerkin.space N).starProjection f‖ ≤ _
  rw [Submodule.starProjection_minimal (U := RealGalerkin.space N) f]
  have hb : BddBelow (Set.range (fun v : RealGalerkin.space N => ‖f - (v : MaterialL2.RealCircleL2)‖)) :=
    ⟨0, by rintro _ ⟨v, rfl⟩; exact norm_nonneg _⟩
  exact ciInf_le hb (⟨g, hg⟩ : RealGalerkin.space N)

theorem projection_tail_bound (N : ℕ) (b : ℤ → ℂ) (hb : Summable (fun k => ‖b k‖))
    (v : ℤ → ℝ) (hv : Summable v) (hv0 : ∀ k, 0 ≤ v k) (ε : ℝ) (hε : 0 ≤ ε)
    (htail : ∀ k, k ∉ frequencies N → ‖b k‖ ≤ ε * v k) :
    ‖circleL2 b - RealGalerkin.projection N (circleL2 b)‖ ≤ ε * ∑' k, v k := by
  apply (projection_best_approx N (circleL2 b)
    (realPart (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (circleCutoff N b)))
    (cutoff_real_mem N b)).trans
  change ‖realPart (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (circleSum b)) -
    realPart (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (circleCutoff N b))‖ ≤ _
  rw [← map_sub, ← map_sub]
  exact (realPart_norm_le _).trans ((toLp_norm_le _).trans (circle_tail_bound N b hb v hv hv0 ε hε htail))

theorem constant_toLp_mem (N : ℕ) (a : ℝ) :
    ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ (ContinuousMap.const Circle a) ∈
      RealGalerkin.space N := by
  have hm := RealFourierDerivative.cosine_mem N 0 (Nat.zero_le N)
  have he : ContinuousMap.const Circle a = a • RealGalerkin.cosine 0 := by
    ext x
    simp [RealGalerkin.cosine]
  rw [he, map_smul]
  exact (RealGalerkin.space N).smul_mem a hm

theorem projection_error_add_mem (N : ℕ) (f g : MaterialL2.RealCircleL2)
    (hg : g ∈ RealGalerkin.space N) :
    ‖(g + f) - RealGalerkin.projection N (g + f)‖ = ‖f - RealGalerkin.projection N f‖ := by
  rw [map_add, RealGalerkin.projection_eq_self N hg]
  congr 1
  abel

theorem projection_tail_bound_offset (N : ℕ) (a : ℝ) (b : ℤ → ℂ)
    (hb : Summable (fun k => ‖b k‖)) (v : ℤ → ℝ) (hv : Summable v) (hv0 : ∀ k, 0 ≤ v k)
    (ε : ℝ) (hε : 0 ≤ ε) (htail : ∀ k, k ∉ frequencies N → ‖b k‖ ≤ ε * v k) :
    ‖ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ
        (ContinuousMap.const Circle a + realCircleSum b) -
      RealGalerkin.projection N (ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ
        (ContinuousMap.const Circle a + realCircleSum b))‖ ≤ ε * ∑' k, v k := by
  rw [map_add, realCircleSum_toLp, projection_error_add_mem N _ _ (constant_toLp_mem N a)]
  exact projection_tail_bound N b hb v hv hv0 ε hε htail

end KerrKoopman.AnalyticTails
