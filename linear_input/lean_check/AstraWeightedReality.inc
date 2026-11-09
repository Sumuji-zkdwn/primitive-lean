
/-! Hermitian symmetry for the actual weighted Fourier trace convolution. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal

namespace KerrKoopman.Phase3WeightedReality
open Phase3WeightedConvolution Phase3WeightedDecoder

variable {I : Type*} [TopologicalSpace I] [CompactSpace I]

def Hermitian (u : L1 C(I, ℂ)) : Prop := ∀ k t, u (-k) t = star (u k t)

def modeEval (k : ℤ) (t : I) : L1 C(I, ℂ) →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ t).comp (lp.evalCLM ℂ (fun _ : ℤ => C(I, ℂ)) 1 k)

theorem modeEval_apply (k : ℤ) (t : I) (u : L1 C(I, ℂ)) :
    modeEval k t u = u k t := rfl

theorem hermitian_zero : Hermitian (0 : L1 C(I, ℂ)) := by
  intro k t
  simp

theorem Hermitian.add {u v : L1 C(I, ℂ)} (hu : Hermitian u) (hv : Hermitian v) :
    Hermitian (u + v) := by
  intro k t
  simpa using congrArg₂ (· + ·) (hu k t) (hv k t)

theorem Hermitian.smul {u : L1 C(I, ℂ)} (hu : Hermitian u) (c : ℝ) :
    Hermitian (c • u) := by
  intro k t
  simpa using congrArg (fun z : ℂ => c • z) (hu k t)

theorem isClosed_hermitian : IsClosed {u : L1 C(I, ℂ) | Hermitian u} := by
  simp only [Hermitian, Set.setOf_forall]
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro t
  exact isClosed_eq (modeEval (-k) t).continuous ((modeEval k t).continuous.star)

theorem product_mode_apply (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    (u v : L1 C(I, ℂ)) (k : ℤ) (t : I) :
    twistedProductReal ρ hρ u v k t =
      ∑' p : ℤ × ℤ, if k = p.1 + p.2 then
        twist ρ p.1 p.2 t * (u p.1 t * v p.2 t) else 0 := by
  classical
  change modeEval k t (∑' p, interaction (twist ρ) u v p) = _
  rw [(modeEval k t).map_tsum (summable_interaction (twist ρ) (twist_norm_le ρ hρ) u v)]
  apply tsum_congr
  intro p
  by_cases hp : k = p.1 + p.2
  · subst k
    simp [modeEval_apply, interaction]
  · rw [if_neg hp]
    change (lp.single (E := fun _ : ℤ => C(I, ℂ)) 1 (p.1+p.2)
      (twist ρ p.1 p.2 * (u p.1 * v p.2))) k t = 0
    rw [lp.single_apply_ne (E := fun _ : ℤ => C(I, ℂ)) 1 _ _ hp]
    rfl

omit [CompactSpace I] in
theorem twist_neg (ρ : C(I, ℝ)) (k l : ℤ) (t : I) :
    twist ρ (-k) (-l) t = twist ρ k l t := by
  simp only [twist, ContinuousMap.coe_mk, ← neg_add, Int.cast_neg, abs_neg]

omit [CompactSpace I] in
theorem twist_star (ρ : C(I, ℝ)) (k l : ℤ) (t : I) :
    star (twist ρ k l t) = twist ρ k l t := by
  change star ((Real.exp (ρ t * (|((k+l : ℤ) : ℝ)| - |(k : ℝ)| - |(l : ℝ)|)) : ℝ) : ℂ) = _
  exact Complex.conj_ofReal _

/-- The genuine full convolution preserves the conjugate symmetry of Fourier coefficients. -/
theorem Hermitian.product (ρ : C(I, ℝ)) (hρ : ∀ t, 0 ≤ ρ t)
    {u v : L1 C(I, ℂ)} (hu : Hermitian u) (hv : Hermitian v) :
    Hermitian (twistedProductReal ρ hρ u v) := by
  classical
  intro k t
  rw [product_mode_apply, product_mode_apply, tsum_star]
  rw [← tsum_comp_neg (fun p : ℤ × ℤ =>
    if -k = p.1 + p.2 then twist ρ p.1 p.2 t * (u p.1 t * v p.2 t) else 0)]
  apply tsum_congr
  intro p
  change (if -k = -p.1 + -p.2 then _ else _) = _
  have heq : (-k = -p.1 + -p.2) ↔ k = p.1 + p.2 := by omega
  simp only [heq]
  split_ifs with hp
  · change twist ρ (-p.1) (-p.2) t * (u (-p.1) t * v (-p.2) t) = _
    rw [twist_neg, hu, hv]
    simp [star_mul, twist_star, mul_comm]
  · simp

end KerrKoopman.Phase3WeightedReality
