
/-!
Analytic construction. A bounded decoder for actual absolutely summable
mode traces, with a multiplicativity theorem for the constructed convolution.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal

namespace KerrKoopman.Phase3WeightedDecoder
open Phase3WeightedConvolution

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

def decode (F : ℤ → A →L[ℂ] B) (u : L1 A) : B := ∑' k, F k (u k)

omit [CompleteSpace A] [CompleteSpace B] in
theorem summable_norm_decode (F : ℤ → A →L[ℂ] B)
    (hF : ∀ k a, ‖F k a‖ ≤ ‖a‖) (u : L1 A) :
    Summable (fun k => ‖F k (u k)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hF k (u k))
    (l1_summable_norm u)

omit [CompleteSpace A] in
theorem summable_decode (F : ℤ → A →L[ℂ] B)
    (hF : ∀ k a, ‖F k a‖ ≤ ‖a‖) (u : L1 A) : Summable (fun k => F k (u k)) :=
  (summable_norm_decode F hF u).of_norm

omit [CompleteSpace A] [CompleteSpace B] in
theorem decode_norm_le (F : ℤ → A →L[ℂ] B)
    (hF : ∀ k a, ‖F k a‖ ≤ ‖a‖) (u : L1 A) : ‖decode F u‖ ≤ ‖u‖ := by
  calc
    ‖decode F u‖ ≤ ∑' k, ‖F k (u k)‖ := norm_tsum_le_tsum_norm (summable_norm_decode F hF u)
    _ ≤ ∑' k, ‖u k‖ := Summable.tsum_le_tsum (fun k => hF k (u k))
      (summable_norm_decode F hF u) (l1_summable_norm u)
    _ = ‖u‖ := (l1_norm_eq_tsum u).symm

omit [CompleteSpace A] in
theorem decode_add (F : ℤ → A →L[ℂ] B)
    (hF : ∀ k a, ‖F k a‖ ≤ ‖a‖) (u v : L1 A) :
    decode F (u + v) = decode F u + decode F v := by
  unfold decode
  simp only [lp.coeFn_add, Pi.add_apply, map_add]
  exact (summable_decode F hF u).tsum_add (summable_decode F hF v)

omit [CompleteSpace A] in
theorem decode_smul (F : ℤ → A →L[ℂ] B)
    (hF : ∀ k a, ‖F k a‖ ≤ ‖a‖) (c : ℂ) (u : L1 A) :
    decode F (c • u) = c • decode F u := by
  unfold decode
  simp only [lp.coeFn_smul, Pi.smul_apply, map_smul]
  exact (summable_decode F hF u).tsum_const_smul c

def decodeCLM (F : ℤ → A →L[ℂ] B) (hF : ∀ k a, ‖F k a‖ ≤ ‖a‖) :
    L1 A →L[ℂ] B :=
  ({ toFun := decode F, map_add' := decode_add F hF, map_smul' := decode_smul F hF } :
    L1 A →ₗ[ℂ] B).mkContinuous 1 (by intro u; simpa using decode_norm_le F hF u)

omit [CompleteSpace A] in
theorem decodeCLM_apply (F : ℤ → A →L[ℂ] B) (hF : ∀ k a, ‖F k a‖ ≤ ‖a‖)
    (u : L1 A) : decodeCLM F hF u = decode F u := rfl

omit [CompleteSpace A] [CompleteSpace B] in
theorem decode_single (F : ℤ → A →L[ℂ] B) (k : ℤ) (a : A) :
    decode F (lp.single 1 k a) = F k a := by
  classical
  unfold decode
  rw [tsum_eq_single k]
  · rw [lp.single_apply_self]
  · intro j hj
    rw [lp.single_apply_ne (E := fun _ : ℤ => A) 1 k a hj, map_zero]

/-- The coefficient interaction identity is sufficient for multiplicativity,
because both the lp interaction sum and the reconstructed product converge.
The explicit analytic Fourier decoder below proves that identity. -/
theorem decode_product (w : ℤ → ℤ → A) (hw : ∀ k l, ‖w k l‖ ≤ 1)
    (F : ℤ → A →L[ℂ] B) (hF : ∀ k a, ‖F k a‖ ≤ ‖a‖)
    (hcompat : ∀ k l a b, F (k + l) (w k l * (a * b)) = F k a * F l b)
    (u v : L1 A) : decode F (product w u v) = decode F u * decode F v := by
  change decodeCLM F hF (∑' p, interaction w u v p) = decode F u * decode F v
  rw [(decodeCLM F hF).map_tsum (summable_interaction w hw u v)]
  calc
    (∑' p, decodeCLM F hF (interaction w u v p)) =
        ∑' p : ℤ × ℤ, F p.1 (u p.1) * F p.2 (v p.2) := by
      apply tsum_congr
      intro p
      rw [decodeCLM_apply, interaction, decode_single, hcompat]
    _ = decode F u * decode F v :=
      (tsum_mul_tsum_of_summable_norm (summable_norm_decode F hF u)
        (summable_norm_decode F hF v)).symm

section Fourier

variable {I J : Type*} [TopologicalSpace I] [CompactSpace I]
  [TopologicalSpace J] [CompactSpace J]

/-- Actual damped Fourier mode on a compact time-space product. -/
def fourierMultiplier (ρ : C(I, ℝ)) (x : C(J, ℝ)) (k : ℤ) : C(I × J, ℂ) :=
  ⟨fun p => Complex.exp (((-ρ p.1 * |(k : ℝ)| : ℝ) : ℂ) +
    (((k : ℝ) * x p.2 : ℝ) : ℂ) * Complex.I), by fun_prop⟩

omit [CompactSpace I] [CompactSpace J] in
theorem fourierMultiplier_norm_apply_le (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (x : C(J, ℝ)) (k : ℤ) (p : I × J) : ‖fourierMultiplier ρ x k p‖ ≤ 1 := by
  have h : -ρ p.1 * |(k : ℝ)| ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hρ p.1)) (abs_nonneg _)
  simpa [fourierMultiplier, Complex.norm_exp] using Real.exp_le_one_iff.mpr h

def fourierMode (ρ : C(I, ℝ)) (x : C(J, ℝ)) (k : ℤ) (a : C(I, ℂ)) :
    C(I × J, ℂ) :=
  ⟨fun p => fourierMultiplier ρ x k p * a p.1, by fun_prop⟩

theorem fourierMode_norm_le (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (x : C(J, ℝ)) (k : ℤ) (a : C(I, ℂ)) : ‖fourierMode ρ x k a‖ ≤ ‖a‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg a)).mpr
  intro p
  change ‖fourierMultiplier ρ x k p * a p.1‖ ≤ ‖a‖
  rw [norm_mul]
  calc
    ‖fourierMultiplier ρ x k p‖ * ‖a p.1‖ ≤ 1 * ‖a p.1‖ :=
      mul_le_mul_of_nonneg_right (fourierMultiplier_norm_apply_le ρ hρ x k p) (norm_nonneg _)
    _ ≤ ‖a‖ := by simpa using a.norm_coe_le_norm p.1

def fourierModeCLM (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (x : C(J, ℝ)) (k : ℤ) : C(I, ℂ) →L[ℂ] C(I × J, ℂ) :=
  ({ toFun := fourierMode ρ x k
     map_add' := by intro a b; ext p; simp [fourierMode, mul_add]
     map_smul' := by intro c a; ext p; simp [fourierMode, mul_left_comm] } :
    C(I, ℂ) →ₗ[ℂ] C(I × J, ℂ)).mkContinuous 1
      (by intro a; simpa using fourierMode_norm_le ρ hρ x k a)

theorem fourierModeCLM_norm_le (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (x : C(J, ℝ)) (k : ℤ) (a : C(I, ℂ)) : ‖fourierModeCLM ρ hρ x k a‖ ≤ ‖a‖ :=
  fourierMode_norm_le ρ hρ x k a

omit [CompactSpace I] [CompactSpace J] in
theorem fourierMultiplier_twist (ρ : C(I, ℝ)) (x : C(J, ℝ))
    (k l : ℤ) (p : I × J) :
    fourierMultiplier ρ x (k + l) p * twist ρ k l p.1 =
      fourierMultiplier ρ x k p * fourierMultiplier ρ x l p := by
  simp only [fourierMultiplier, twist, ContinuousMap.coe_mk, Complex.ofReal_exp]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fourierMode_compat (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (x : C(J, ℝ)) (k l : ℤ) (a b : C(I, ℂ)) :
    fourierModeCLM ρ hρ x (k + l) (twist ρ k l * (a * b)) =
      fourierModeCLM ρ hρ x k a * fourierModeCLM ρ hρ x l b := by
  ext p
  change fourierMultiplier ρ x (k+l) p * (twist ρ k l p.1 * (a p.1 * b p.1)) =
    (fourierMultiplier ρ x k p * a p.1) * (fourierMultiplier ρ x l p * b p.1)
  calc
    _ = (fourierMultiplier ρ x (k+l) p * twist ρ k l p.1) * (a p.1 * b p.1) := by ring
    _ = (fourierMultiplier ρ x k p * fourierMultiplier ρ x l p) * (a p.1 * b p.1) := by
      rw [fourierMultiplier_twist]
    _ = _ := by ring

/-- Uniformly convergent Fourier reconstruction on the compact spacetime product. -/
def fourierDecode (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t) (x : C(J, ℝ)) :
    L1 C(I, ℂ) →L[ℂ] C(I × J, ℂ) :=
  decodeCLM (fourierModeCLM ρ hρ x) (fourierModeCLM_norm_le ρ hρ x)

theorem fourierDecode_norm_le (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (x : C(J, ℝ)) (u : L1 C(I, ℂ)) : ‖fourierDecode ρ hρ x u‖ ≤ ‖u‖ :=
  decode_norm_le _ (fourierModeCLM_norm_le ρ hρ x) u

/-- The actual twisted lp convolution reconstructs to ordinary pointwise multiplication. -/
theorem fourierDecode_product (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (x : C(J, ℝ)) (u v : L1 C(I, ℂ)) :
    fourierDecode ρ hρ x (twistedProduct ρ hρ u v) =
      fourierDecode ρ hρ x u * fourierDecode ρ hρ x v :=
  decode_product (twist ρ) (twist_norm_le ρ hρ) _ (fourierModeCLM_norm_le ρ hρ x)
    (fourierMode_compat ρ hρ x) u v

end Fourier
end KerrKoopman.Phase3WeightedDecoder
