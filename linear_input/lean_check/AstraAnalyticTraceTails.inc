
/-! Instantiation of actual projection tails by weighted analytic traces. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal
open MeasureTheory

namespace KerrKoopman.AnalyticTraceTails
open Phase3WeightedConvolution Phase3WeightedDerivative Phase3WeightedRealDecode AnalyticTails
open FourierProjection

abbrev Circle := AnalyticTails.Circle

variable {I : Type*} [TopologicalSpace I] [CompactSpace I]

def traceCoeff (r : ℝ) (u : L1 C(I, ℂ)) (t : I) (k : ℤ) : ℂ := modeValue r k (u k t) 0
def derivativeCoeff (r : ℝ) (u : L1 C(I, ℂ)) (t : I) (k : ℤ) : ℂ := modeDerivative r k (u k t) 0

theorem traceCoeff_norm_le (r : ℝ) (hr : 0 ≤ r) (u : L1 C(I, ℂ)) (t : I) (k : ℤ) :
    ‖traceCoeff r u t k‖ ≤ ‖u k‖ := by
  exact modeValue_norm_le (ContinuousMap.const I r) (fun _ => hr) u t k 0

theorem summable_traceCoeff (r : ℝ) (hr : 0 ≤ r) (u : L1 C(I, ℂ)) (t : I) :
    Summable (fun k => ‖traceCoeff r u t k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (traceCoeff_norm_le r hr u t) (l1_summable_norm u)

theorem summable_derivativeCoeff (r : ℝ) (hr : 0 < r) (u : L1 C(I, ℂ)) (t : I) :
    Summable (fun k => ‖derivativeCoeff r u t k‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((l1_summable_norm u).mul_left (Real.exp (-1) / r))
  exact fun k => modeDerivative_norm_le (ContinuousMap.const I r) r hr (fun _ => le_rfl) u t k 0

theorem frequency_outside_lower (N : ℕ) (k : ℤ) (hk : k ∉ frequencies N) :
    (N + 1 : ℝ) ≤ |(k : ℝ)| := by
  have h : (N + 1 : ℤ) ≤ |k| := by
    simp only [frequencies, Finset.mem_Icc] at hk
    have hp := le_abs_self k
    have hn := neg_le_abs k
    omega
  exact_mod_cast h

theorem traceCoeff_tail (N : ℕ) (r r₀ : ℝ) (h₀ : 0 ≤ r₀) (hr : r₀ ≤ r)
    (u : L1 C(I, ℂ)) (t : I) (k : ℤ) (hk : k ∉ frequencies N) :
    ‖traceCoeff r u t k‖ ≤ Real.exp (-r₀ * (N + 1)) * ‖u k‖ := by
  change ‖modeValue r k (u k t) 0‖ ≤ _
  rw [modeValue_norm]
  have ha := frequency_outside_lower N k hk
  have he : Real.exp (-r * |(k : ℝ)|) ≤ Real.exp (-r₀ * (N+1)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg (k : ℝ)]
  exact mul_le_mul he ((u k).norm_coe_le_norm t) (norm_nonneg _) (Real.exp_nonneg _)

theorem frequency_damping_tail (N : ℕ) (r r₀ δ : ℝ) (hδ : 0 ≤ δ) (hd : δ < r₀)
    (hr : r₀ ≤ r) (k : ℤ) (hk : k ∉ frequencies N) :
    |(k : ℝ)| * Real.exp (-r * |(k : ℝ)|) ≤ Real.exp (-δ * (N+1)) / (r₀-δ) := by
  have hdiff : 0 < r₀-δ := sub_pos.mpr hd
  have hpeak := frequency_damping_le (r₀-δ) (r-δ) |(k : ℝ)| hdiff
    (by linarith) (abs_nonneg _)
  have hpeak' : |(k : ℝ)| * Real.exp (-(r-δ) * |(k : ℝ)|) ≤ 1 / (r₀-δ) := by
    apply hpeak.trans
    apply div_le_div_of_nonneg_right _ hdiff.le
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have he : Real.exp (-δ * |(k : ℝ)|) ≤ Real.exp (-δ * (N+1)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [frequency_outside_lower N k hk]
  calc
    _ = (|(k : ℝ)| * Real.exp (-(r-δ) * |(k : ℝ)|)) * Real.exp (-δ * |(k : ℝ)|) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (1 / (r₀-δ)) * Real.exp (-δ * (N+1)) :=
      mul_le_mul hpeak' he (Real.exp_nonneg _) (by positivity)
    _ = _ := by ring

theorem derivativeCoeff_tail (N : ℕ) (r r₀ δ : ℝ) (hδ : 0 ≤ δ) (hd : δ < r₀)
    (hr : r₀ ≤ r) (u : L1 C(I, ℂ)) (t : I) (k : ℤ) (hk : k ∉ frequencies N) :
    ‖derivativeCoeff r u t k‖ ≤ (Real.exp (-δ * (N+1)) / (r₀-δ)) * ‖u k‖ := by
  change ‖modeDerivative r k (u k t) 0‖ ≤ _
  rw [modeDerivative_norm]
  exact mul_le_mul (frequency_damping_tail N r r₀ δ hδ hd hr k hk)
    ((u k).norm_coe_le_norm t) (norm_nonneg _)
    (div_nonneg (Real.exp_nonneg _) (sub_pos.mpr hd).le)

/-- Actual real orthogonal projection error of the constructed circle field. -/
theorem trace_projection_error (N : ℕ) (r r₀ : ℝ) (h₀ : 0 ≤ r₀) (hr : r₀ ≤ r)
    (u : L1 C(I, ℂ)) (t : I) :
    ‖circleL2 (traceCoeff r u t) - RealGalerkin.projection N (circleL2 (traceCoeff r u t))‖ ≤
      Real.exp (-r₀ * (N+1)) * ‖u‖ := by
  simpa only [← l1_norm_eq_tsum] using projection_tail_bound N (traceCoeff r u t)
    (summable_traceCoeff r (h₀.trans hr) u t) (fun k => ‖u k‖) (l1_summable_norm u)
    (fun _ => norm_nonneg _) (Real.exp (-r₀ * (N+1))) (Real.exp_nonneg _)
    (traceCoeff_tail N r r₀ h₀ hr u t)

/-- Actual real orthogonal projection error of the constructed circle derivative. -/
theorem derivative_projection_error (N : ℕ) (r r₀ δ : ℝ) (hδ : 0 ≤ δ) (hd : δ < r₀)
    (hr : r₀ ≤ r) (u : L1 C(I, ℂ)) (t : I) :
    ‖circleL2 (derivativeCoeff r u t) - RealGalerkin.projection N (circleL2 (derivativeCoeff r u t))‖ ≤
      (Real.exp (-δ * (N+1)) / (r₀-δ)) * ‖u‖ := by
  have hrpos : 0 < r := lt_of_lt_of_le (lt_of_le_of_lt hδ hd) hr
  simpa only [← l1_norm_eq_tsum] using projection_tail_bound N (derivativeCoeff r u t)
    (summable_derivativeCoeff r hrpos u t) (fun k => ‖u k‖) (l1_summable_norm u)
    (fun _ => norm_nonneg _) (Real.exp (-δ * (N+1)) / (r₀-δ))
    (div_nonneg (Real.exp_nonneg _) (sub_pos.mpr hd).le)
    (derivativeCoeff_tail N r r₀ δ hδ hd hr u t)

theorem trace_projection_error_offset (N : ℕ) (a r r₀ : ℝ) (h₀ : 0 ≤ r₀) (hr : r₀ ≤ r)
    (u : L1 C(I, ℂ)) (t : I) :
    ‖ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ
        (ContinuousMap.const Circle a + realCircleSum (traceCoeff r u t)) -
      RealGalerkin.projection N (ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ
        (ContinuousMap.const Circle a + realCircleSum (traceCoeff r u t)))‖ ≤
      Real.exp (-r₀ * (N+1)) * ‖u‖ := by
  simpa only [← l1_norm_eq_tsum] using projection_tail_bound_offset N a (traceCoeff r u t)
    (summable_traceCoeff r (h₀.trans hr) u t) (fun k => ‖u k‖) (l1_summable_norm u)
    (fun _ => norm_nonneg _) (Real.exp (-r₀ * (N+1))) (Real.exp_nonneg _)
    (traceCoeff_tail N r r₀ h₀ hr u t)

theorem fourier_at_real (k : ℤ) (x : ℝ) :
    (fourier k : C(Circle, ℂ)) (x : Circle) = Complex.exp ((((k : ℝ)*x : ℝ) : ℂ)*Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

theorem modeValue_mul_character (r : ℝ) (k : ℤ) (a : ℂ) (x : ℝ) :
    modeValue r k a 0 * (fourier k : C(Circle, ℂ)) (x : Circle) = modeValue r k a x := by
  rw [fourier_at_real]
  simp [modeValue, Complex.exp_add, mul_left_comm, mul_comm]

theorem circleSum_trace_apply (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (u : L1 C(I, ℂ)) (t : I) (x : ℝ) :
    circleSum (traceCoeff (ρ t) u t) (x : Circle) = rawDecode ρ u t x := by
  rw [circleSum_apply _ (summable_traceCoeff _ (hρ t) u t)]
  apply tsum_congr
  intro k
  exact modeValue_mul_character (ρ t) k (u k t) x

theorem circleSum_derivative_apply (ρ : C(I, ℝ)) (hρ : ∀ t, 0 < ρ t)
    (u : L1 C(I, ℂ)) (t : I) (x : ℝ) :
    circleSum (derivativeCoeff (ρ t) u t) (x : Circle) = rawDerivative ρ u t x := by
  rw [circleSum_apply _ (summable_derivativeCoeff _ (hρ t) u t)]
  apply tsum_congr
  intro k
  change modeDerivative (ρ t) k (u k t) 0 * fourier k (x : Circle) = modeDerivative (ρ t) k (u k t) x
  simp only [modeDerivative, mul_assoc, modeValue_mul_character]

end KerrKoopman.AnalyticTraceTails
