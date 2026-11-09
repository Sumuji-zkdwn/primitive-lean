
/-!
# Canonical continuous representatives of the actual finite Galerkin space

The inverse to toLp is constructed on the finite continuous trigonometric
span. It gives bounded point evaluation only on the finite space, without
asserting point evaluation is continuous on the full L2 space.
-/

namespace KerrKoopman.FiniteRepresentatives

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open MaterialL2

abbrev Circle := RealGalerkin.Circle

def toL2 : C(Circle, ℝ) →L[ℝ] RealCircleL2 :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℝ

def mode (N : ℕ) (i : Fin (N+1) × Bool) : C(Circle, ℝ) :=
  if i.2 then RealGalerkin.cosine i.1 else RealGalerkin.sine i.1

def continuousSpace (N : ℕ) : Submodule ℝ C(Circle, ℝ) :=
  Submodule.span ℝ (Set.range (mode N))

instance continuousSpace_finiteDimensional (N : ℕ) : FiniteDimensional ℝ (continuousSpace N) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range (mode N))

theorem toL2_mode (N : ℕ) (i : Fin (N+1) × Bool) :
    toL2 (mode N i) = RealGalerkin.realMode N i := by
  cases i with
  | mk k b => cases b <;> rfl

theorem toL2_injective : Function.Injective toL2 :=
  ContinuousMap.toLp_injective AddCircle.haarAddCircle

theorem toL2_mem (N : ℕ) {f : C(Circle, ℝ)} (hf : f ∈ continuousSpace N) :
    toL2 f ∈ RealGalerkin.space N := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      rw [toL2_mode]
      exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simpa only [map_zero] using (RealGalerkin.space N).zero_mem
  | add f g hf hg ihf ihg =>
      simpa only [map_add] using (RealGalerkin.space N).add_mem ihf ihg
  | smul c f hf ih => simpa only [map_smul] using (RealGalerkin.space N).smul_mem c ih

def toFinite (N : ℕ) : continuousSpace N →ₗ[ℝ] RealGalerkin.space N :=
  (toL2.toLinearMap.comp (continuousSpace N).subtype).codRestrict (RealGalerkin.space N)
    (fun f => toL2_mem N f.property)

theorem toFinite_injective (N : ℕ) : Function.Injective (toFinite N) := by
  intro f g h
  apply Subtype.ext
  apply toL2_injective
  exact congrArg Subtype.val h

theorem toL2_surjective_on (N : ℕ) {f : RealCircleL2} (hf : f ∈ RealGalerkin.space N) :
    ∃ g : continuousSpace N, toL2 (g : C(Circle, ℝ)) = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      exact ⟨⟨mode N i, Submodule.subset_span ⟨i, rfl⟩⟩, toL2_mode N i⟩
  | zero => exact ⟨0, map_zero toL2⟩
  | add f g hf hg ihf ihg =>
      obtain ⟨F, hF⟩ := ihf
      obtain ⟨G, hG⟩ := ihg
      refine ⟨F+G, ?_⟩
      change toL2 ((F : C(Circle, ℝ)) + (G : C(Circle, ℝ))) = _
      rw [map_add, hF, hG]
  | smul c f hf ih =>
      obtain ⟨F, hF⟩ := ih
      refine ⟨c • F, ?_⟩
      change toL2 (c • (F : C(Circle, ℝ))) = _
      rw [map_smul, hF]

theorem toFinite_surjective (N : ℕ) : Function.Surjective (toFinite N) := by
  intro f
  obtain ⟨g, hg⟩ := toL2_surjective_on N f.property
  exact ⟨g, Subtype.ext hg⟩

def finiteEquiv (N : ℕ) : continuousSpace N ≃L[ℝ] RealGalerkin.space N :=
  (LinearEquiv.ofBijective (toFinite N) ⟨toFinite_injective N, toFinite_surjective N⟩).toContinuousLinearEquiv

/-- The unique continuous representative in the actual finite trigonometric span. -/
def representative (N : ℕ) : RealGalerkin.space N →L[ℝ] C(Circle, ℝ) :=
  (continuousSpace N).subtypeL.comp (finiteEquiv N).symm.toContinuousLinearMap

theorem representative_mem (N : ℕ) (f : RealGalerkin.space N) :
    representative N f ∈ continuousSpace N := (finiteEquiv N).symm f |>.property

theorem toL2_representative (N : ℕ) (f : RealGalerkin.space N) :
    toL2 (representative N f) = (f : RealCircleL2) := by
  exact congrArg Subtype.val ((finiteEquiv N).apply_symm_apply f)

theorem representative_unique (N : ℕ) (f : RealGalerkin.space N) (g : C(Circle, ℝ))
    (hg : toL2 g = (f : RealCircleL2)) : representative N f = g := by
  apply toL2_injective
  rw [toL2_representative, hg]

def evaluate (N : ℕ) (x : ℝ) : RealGalerkin.space N →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ (x : Circle)).comp (representative N)

theorem evaluate_apply (N : ℕ) (f : RealGalerkin.space N) (x : ℝ) :
    evaluate N x f = representative N f (x : Circle) := rfl

theorem evaluate_hasDerivAt (N : ℕ) (z : ℝ → RealGalerkin.space N)
    (dz : RealGalerkin.space N) (t x : ℝ) (hz : HasDerivAt z dz t) :
    HasDerivAt (fun s => representative N (z s) (x : Circle)) (representative N dz (x : Circle)) t :=
  (evaluate N x).hasFDerivAt.comp_hasDerivAt t hz

theorem cosine_coe (k : ℕ) (x : ℝ) : RealGalerkin.cosine k (x : Circle) = Real.cos ((k : ℝ)*x) := by
  change (fourier (k : ℤ) (x : AddCircle (2*Real.pi))).re = _
  rw [fourier_coe_apply, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have he : 2*(Real.pi : ℂ)*Complex.I*(k : ℤ)*(x : ℂ)/(2*(Real.pi : ℂ)) =
      (((k : ℝ)*x : ℝ) : ℂ)*Complex.I := by
    push_cast
    field_simp
  rw [he, Complex.exp_ofReal_mul_I_re]

theorem sine_coe (k : ℕ) (x : ℝ) : RealGalerkin.sine k (x : Circle) = Real.sin ((k : ℝ)*x) := by
  change (fourier (k : ℤ) (x : AddCircle (2*Real.pi))).im = _
  rw [fourier_coe_apply, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have he : 2*(Real.pi : ℂ)*Complex.I*(k : ℤ)*(x : ℂ)/(2*(Real.pi : ℂ)) =
      (((k : ℝ)*x : ℝ) : ℂ)*Complex.I := by
    push_cast
    field_simp
  rw [he, Complex.exp_ofReal_mul_I_im]

/-- Probability-Haar integration is exactly the normalized real interval integral. -/
theorem haar_integral_eq_interval (f : Circle → ℝ) :
    (∫ x, f x ∂AddCircle.haarAddCircle) =
      (∫ x in 0..(2*Real.pi), f (x : Circle))/(2*Real.pi) := by
  rw [AddCircle.integral_haarAddCircle]
  have hi := AddCircle.intervalIntegral_preimage (2*Real.pi) 0 f
  simp only [zero_add] at hi
  rw [← hi]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

end
end KerrKoopman.FiniteRepresentatives
