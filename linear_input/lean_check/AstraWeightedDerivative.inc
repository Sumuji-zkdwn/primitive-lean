
/-! Actual termwise spatial differentiation of reconstructed analytic Fourier traces. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal

namespace KerrKoopman.Phase3WeightedDerivative
open Phase3WeightedConvolution Phase3WeightedDecoder

def modeValue (r : ℝ) (k : ℤ) (a : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (((-r * |(k : ℝ)| : ℝ) : ℂ) +
    (((k : ℝ) * x : ℝ) : ℂ) * Complex.I) * a

def modeDerivative (r : ℝ) (k : ℤ) (a : ℂ) (x : ℝ) : ℂ :=
  (((k : ℝ) : ℂ) * Complex.I) * modeValue r k a x

theorem modeValue_norm (r : ℝ) (k : ℤ) (a : ℂ) (x : ℝ) :
    ‖modeValue r k a x‖ = Real.exp (-r * |(k : ℝ)|) * ‖a‖ := by
  simp [modeValue, Complex.norm_exp]

theorem modeDerivative_norm (r : ℝ) (k : ℤ) (a : ℂ) (x : ℝ) :
    ‖modeDerivative r k a x‖ =
      (|(k : ℝ)| * Real.exp (-r * |(k : ℝ)|)) * ‖a‖ := by
  simp [modeDerivative, modeValue_norm, mul_assoc]

theorem hasDerivAt_modeValue (r : ℝ) (k : ℤ) (a : ℂ) (x : ℝ) :
    HasDerivAt (modeValue r k a) (modeDerivative r k a x) x := by
  have hl := (((hasDerivAt_id x).const_mul (k : ℝ)).ofReal_comp.mul_const Complex.I).const_add
    (((-r * |(k : ℝ)| : ℝ) : ℂ))
  convert hl.cexp.mul_const a using 1
  simp [modeValue, modeDerivative, mul_assoc, mul_comm, mul_left_comm]

theorem frequency_damping_le (δ r a : ℝ) (hδ : 0 < δ) (hr : δ ≤ r) (ha : 0 ≤ a) :
    a * Real.exp (-r * a) ≤ Real.exp (-1) / δ := by
  have he : Real.exp (-r * a) ≤ Real.exp (-δ * a) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  apply (le_div_iff₀ hδ).mpr
  have h : (δ * a) * Real.exp (-δ * a) ≤ Real.exp (-1) := by
    simpa only [neg_mul] using Real.mul_exp_neg_le_exp_neg_one (δ * a)
  have hm := mul_le_mul_of_nonneg_left he ha
  nlinarith [mul_le_mul_of_nonneg_right hm hδ.le]

variable {I : Type*} [TopologicalSpace I] [CompactSpace I]

def rawDecode (ρ : C(I, ℝ)) (u : L1 C(I, ℂ)) (t : I) (x : ℝ) : ℂ :=
  ∑' k, modeValue (ρ t) k (u k t) x

def rawDerivative (ρ : C(I, ℝ)) (u : L1 C(I, ℂ)) (t : I) (x : ℝ) : ℂ :=
  ∑' k, modeDerivative (ρ t) k (u k t) x

theorem modeValue_norm_le (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (u : L1 C(I, ℂ)) (t : I) (k : ℤ) (x : ℝ) :
    ‖modeValue (ρ t) k (u k t) x‖ ≤ ‖u k‖ := by
  rw [modeValue_norm]
  have he : Real.exp (-ρ t * |(k : ℝ)|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hρ t)) (abs_nonneg _))
  calc
    _ ≤ 1 * ‖u k t‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
    _ ≤ ‖u k‖ := by simpa using (u k).norm_coe_le_norm t

theorem summable_norm_modeValue (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (u : L1 C(I, ℂ)) (t : I) (x : ℝ) :
    Summable (fun k => ‖modeValue (ρ t) k (u k t) x‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (l1_summable_norm u)
  exact fun k => modeValue_norm_le ρ hρ u t k x

theorem rawDecode_norm_le (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (u : L1 C(I, ℂ)) (t : I) (x : ℝ) : ‖rawDecode ρ u t x‖ ≤ ‖u‖ := by
  calc
    _ ≤ ∑' k, ‖modeValue (ρ t) k (u k t) x‖ :=
      norm_tsum_le_tsum_norm (summable_norm_modeValue ρ hρ u t x)
    _ ≤ ∑' k, ‖u k‖ := Summable.tsum_le_tsum (fun k => modeValue_norm_le ρ hρ u t k x)
      (summable_norm_modeValue ρ hρ u t x) (l1_summable_norm u)
    _ = ‖u‖ := (l1_norm_eq_tsum u).symm

theorem continuous_rawDecode (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (u : L1 C(I, ℂ)) : Continuous (fun p : I × ℝ => rawDecode ρ u p.1 p.2) := by
  apply continuous_tsum (f := fun k (p : I × ℝ) => modeValue (ρ p.1) k (u k p.1) p.2)
    _ (l1_summable_norm u)
    (fun k p => modeValue_norm_le ρ hρ u p.1 k p.2)
  intro k
  unfold modeValue
  fun_prop

theorem modeDerivative_norm_le (ρ : C(I, ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ t, δ ≤ ρ t) (u : L1 C(I, ℂ)) (t : I) (k : ℤ) (x : ℝ) :
    ‖modeDerivative (ρ t) k (u k t) x‖ ≤ (Real.exp (-1) / δ) * ‖u k‖ := by
  rw [modeDerivative_norm]
  have hm := frequency_damping_le δ (ρ t) |(k : ℝ)| hδ (hρ t) (abs_nonneg _)
  calc
    _ ≤ (Real.exp (-1) / δ) * ‖u k t‖ :=
      mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    _ ≤ (Real.exp (-1) / δ) * ‖u k‖ :=
      mul_le_mul_of_nonneg_left ((u k).norm_coe_le_norm t) (by positivity)

/-- All Fourier modes are differentiated, with a summable uniform envelope.
No finite truncation or assumed differentiability of the decoded field occurs. -/
theorem hasDerivAt_rawDecode (ρ : C(I, ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ t, δ ≤ ρ t) (u : L1 C(I, ℂ)) (t : I) (x : ℝ) :
    HasDerivAt (rawDecode ρ u t) (rawDerivative ρ u t x) x := by
  apply hasDerivAt_tsum ((l1_summable_norm u).mul_left (Real.exp (-1) / δ))
    (fun k y => hasDerivAt_modeValue (ρ t) k (u k t) y)
    (fun k y => modeDerivative_norm_le ρ δ hδ hρ u t k y)
    (y₀ := 0)
  exact (summable_norm_modeValue ρ (fun t => hδ.le.trans (hρ t)) u t 0).of_norm

theorem rawDerivative_norm_le (ρ : C(I, ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ t, δ ≤ ρ t) (u : L1 C(I, ℂ)) (t : I) (x : ℝ) :
    ‖rawDerivative ρ u t x‖ ≤ (Real.exp (-1) / δ) * ‖u‖ := by
  have hs := (l1_summable_norm u).mul_left (Real.exp (-1) / δ)
  have hb := fun k => modeDerivative_norm_le ρ δ hδ hρ u t k x
  have hd : Summable (fun k => ‖modeDerivative (ρ t) k (u k t) x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs
  calc
    _ ≤ ∑' k, ‖modeDerivative (ρ t) k (u k t) x‖ := norm_tsum_le_tsum_norm hd
    _ ≤ ∑' k, (Real.exp (-1) / δ) * ‖u k‖ := Summable.tsum_le_tsum hb hd hs
    _ = (Real.exp (-1) / δ) * ‖u‖ := by
      rw [tsum_mul_left, ← l1_norm_eq_tsum]

theorem continuous_rawDerivative (ρ : C(I, ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ t, δ ≤ ρ t) (u : L1 C(I, ℂ)) :
    Continuous (fun p : I × ℝ => rawDerivative ρ u p.1 p.2) := by
  apply continuous_tsum (f := fun k (p : I × ℝ) => modeDerivative (ρ p.1) k (u k p.1) p.2)
    _ ((l1_summable_norm u).mul_left (Real.exp (-1) / δ))
    (fun k p => modeDerivative_norm_le ρ δ hδ hρ u p.1 k p.2)
  intro k
  unfold modeDerivative modeValue
  fun_prop

theorem modeValue_periodic (r : ℝ) (k : ℤ) (a : ℂ) :
    Function.Periodic (modeValue r k a) (2 * Real.pi) := by
  intro x
  have he : (((-r * |(k : ℝ)| : ℝ) : ℂ) +
      (((k : ℝ) * (x + 2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
      (((-r * |(k : ℝ)| : ℝ) : ℂ) + (((k : ℝ) * x : ℝ) : ℂ) * Complex.I) +
        (k : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  simp only [modeValue, he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem rawDecode_periodic (ρ : C(I, ℝ)) (u : L1 C(I, ℂ)) (t : I) :
    Function.Periodic (rawDecode ρ u t) (2 * Real.pi) := by
  intro x
  exact tsum_congr (fun k => modeValue_periodic (ρ t) k (u k t) x)

theorem rawDerivative_periodic (ρ : C(I, ℝ)) (u : L1 C(I, ℂ)) (t : I) :
    Function.Periodic (rawDerivative ρ u t) (2 * Real.pi) := by
  intro x
  apply tsum_congr
  intro k
  unfold modeDerivative
  rw [modeValue_periodic (ρ t) k (u k t) x]

theorem fourierDecode_apply {J : Type*} [TopologicalSpace J] [CompactSpace J]
    (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t) (x : C(J, ℝ)) (u : L1 C(I, ℂ)) (p : I × J) :
    fourierDecode ρ hρ x u p = rawDecode ρ u p.1 (x p.2) := by
  change ContinuousMap.evalCLM ℂ p (∑' k, fourierModeCLM ρ hρ x k (u k)) = _
  rw [(ContinuousMap.evalCLM ℂ p).map_tsum
    (summable_decode (fourierModeCLM ρ hρ x) (fourierModeCLM_norm_le ρ hρ x) u)]
  rfl

end KerrKoopman.Phase3WeightedDerivative
