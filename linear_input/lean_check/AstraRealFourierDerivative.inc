
/-!
# Real Fourier differentiation on the actual real Galerkin space

Real-to-complex embedding and real-part recovery are actual pointwise L2
maps. They connect the concrete cosine/sine span to the earlier proved
complex Fourier derivative, without extending the nonlinear material law.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ComplexConjugate
open KerrKoopman.MaterialL2

namespace KerrKoopman.RealFourierDerivative

instance complexL2ScalarTower : IsScalarTower ℝ ℂ FourierProjection.CircleL2 :=
  MeasureTheory.Lp.instIsScalarTower

def complexify : RealCircleL2 →L[ℝ] FourierProjection.CircleL2 :=
  Complex.ofRealCLM.compLpL 2 AddCircle.haarAddCircle

def realPart : FourierProjection.CircleL2 →L[ℝ] RealCircleL2 :=
  Complex.reCLM.compLpL 2 AddCircle.haarAddCircle

def imagPart : FourierProjection.CircleL2 →L[ℝ] RealCircleL2 :=
  Complex.imCLM.compLpL 2 AddCircle.haarAddCircle

theorem complexify_ae (f : RealCircleL2) :
    complexify f =ᵐ[AddCircle.haarAddCircle] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

theorem realPart_ae (f : FourierProjection.CircleL2) :
    realPart f =ᵐ[AddCircle.haarAddCircle] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLpL f

theorem imagPart_ae (f : FourierProjection.CircleL2) :
    imagPart f =ᵐ[AddCircle.haarAddCircle] fun x => (f x).im :=
  Complex.imCLM.coeFn_compLpL f

theorem realPart_complexify (f : RealCircleL2) : realPart (complexify f) = f := by
  apply Lp.ext
  filter_upwards [realPart_ae (complexify f), complexify_ae f] with x hx hy
  simp [hx, hy]

theorem complexify_norm_le (f : RealCircleL2) : ‖complexify f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [complexify_ae f] with x hx
  simp [hx]

theorem realPart_norm_le (f : FourierProjection.CircleL2) : ‖realPart f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [realPart_ae f] with x hx
  rw [hx]
  simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (f x)

theorem complexify_norm (f : RealCircleL2) : ‖complexify f‖ = ‖f‖ := by
  apply le_antisymm (complexify_norm_le f)
  simpa only [realPart_complexify] using realPart_norm_le (complexify f)

theorem basis_ae (k : ℤ) :
    FourierProjection.basis k =ᵐ[AddCircle.haarAddCircle]
      (fourier k : C(RealGalerkin.Circle, ℂ)) := by
  simpa only [FourierProjection.basis, coe_fourierBasis] using
    (coeFn_fourierLp (T := 2 * Real.pi) 2 k)

theorem realPart_basis (k : ℕ) :
    realPart (FourierProjection.basis (k : ℤ)) = RealGalerkin.cosineL2 k := by
  apply Lp.ext
  filter_upwards [realPart_ae (FourierProjection.basis (k : ℤ)), basis_ae (k : ℤ),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) AddCircle.haarAddCircle
      (RealGalerkin.cosine k)] with x hx hy hz
  change (RealGalerkin.cosineL2 k) x = (fourier (k : ℤ) x).re at hz
  rw [hx, hy, hz]

theorem imagPart_basis (k : ℕ) :
    imagPart (FourierProjection.basis (k : ℤ)) = RealGalerkin.sineL2 k := by
  apply Lp.ext
  filter_upwards [imagPart_ae (FourierProjection.basis (k : ℤ)), basis_ae (k : ℤ),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) AddCircle.haarAddCircle
      (RealGalerkin.sine k)] with x hx hy hz
  change (RealGalerkin.sineL2 k) x = (fourier (k : ℤ) x).im at hz
  rw [hx, hy, hz]

theorem complexify_cosine (k : ℕ) :
    complexify (RealGalerkin.cosineL2 k) =
      (1 / 2 : ℂ) • (FourierProjection.basis (k : ℤ) + FourierProjection.basis (-(k : ℤ))) := by
  apply Lp.ext
  filter_upwards [complexify_ae (RealGalerkin.cosineL2 k),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) AddCircle.haarAddCircle (RealGalerkin.cosine k),
    Lp.coeFn_smul (1 / 2 : ℂ)
      (FourierProjection.basis (k : ℤ) + FourierProjection.basis (-(k : ℤ))),
    Lp.coeFn_add (FourierProjection.basis (k : ℤ)) (FourierProjection.basis (-(k : ℤ))),
    basis_ae (k : ℤ), basis_ae (-(k : ℤ))] with x hx hc hs ha hp hn
  change (RealGalerkin.cosineL2 k) x = (fourier (k : ℤ) x).re at hc
  simp only [hx, hc, hs, Pi.smul_apply, ha, Pi.add_apply, hp, hn, fourier_neg, smul_eq_mul]
  apply Complex.ext
  · simp
    ring
  · simp

theorem complexify_sine (k : ℕ) :
    complexify (RealGalerkin.sineL2 k) =
      (-(Complex.I / 2)) •
        (FourierProjection.basis (k : ℤ) - FourierProjection.basis (-(k : ℤ))) := by
  apply Lp.ext
  filter_upwards [complexify_ae (RealGalerkin.sineL2 k),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) AddCircle.haarAddCircle (RealGalerkin.sine k),
    Lp.coeFn_smul (-(Complex.I / 2))
      (FourierProjection.basis (k : ℤ) - FourierProjection.basis (-(k : ℤ))),
    Lp.coeFn_sub (FourierProjection.basis (k : ℤ)) (FourierProjection.basis (-(k : ℤ))),
    basis_ae (k : ℤ), basis_ae (-(k : ℤ))] with x hx hc hs ha hp hn
  change (RealGalerkin.sineL2 k) x = (fourier (k : ℤ) x).im at hc
  simp only [hx, hc, hs, Pi.smul_apply, ha, Pi.sub_apply, hp, hn, fourier_neg, smul_eq_mul]
  apply Complex.ext
  · simp
    ring
  · simp

theorem complexify_smul (a : ℝ) (f : RealCircleL2) :
    complexify (a • f) = (a : ℂ) • complexify f := by
  rw [map_smul]
  exact (algebraMap_smul ℂ a (complexify f)).symm

theorem derivative_basis (N : ℕ) (k : ℤ) :
    FourierProjection.derivative N (FourierProjection.basis k) =
      if k ∈ FourierProjection.frequencies N then
        (Complex.I * (k : ℂ)) • FourierProjection.basis k else 0 := by
  classical
  simp [FourierProjection.derivative_apply,
    orthonormal_iff_ite.mp FourierProjection.basis.orthonormal]

theorem derivative_complexify_cosine (N k : ℕ) (hk : k ≤ N) :
    FourierProjection.derivative N (complexify (RealGalerkin.cosineL2 k)) =
      complexify ((-(k : ℝ)) • RealGalerkin.sineL2 k) := by
  have hp : (k : ℤ) ∈ FourierProjection.frequencies N := by
    simp only [FourierProjection.frequencies, Finset.mem_Icc]
    omega
  have hn : -(k : ℤ) ∈ FourierProjection.frequencies N := by
    simp only [FourierProjection.frequencies, Finset.mem_Icc]
    omega
  rw [complexify_cosine, map_smul, map_add, derivative_basis, derivative_basis,
    ite_eq_left hp, ite_eq_left hn, complexify_smul, complexify_sine]
  push_cast
  module

theorem derivative_complexify_sine (N k : ℕ) (hk : k ≤ N) :
    FourierProjection.derivative N (complexify (RealGalerkin.sineL2 k)) =
      complexify ((k : ℝ) • RealGalerkin.cosineL2 k) := by
  have hp : (k : ℤ) ∈ FourierProjection.frequencies N := by
    simp only [FourierProjection.frequencies, Finset.mem_Icc]
    omega
  have hn : -(k : ℤ) ∈ FourierProjection.frequencies N := by
    simp only [FourierProjection.frequencies, Finset.mem_Icc]
    omega
  rw [complexify_sine, map_smul, map_sub, derivative_basis, derivative_basis,
    ite_eq_left hp, ite_eq_left hn, complexify_smul, complexify_cosine]
  push_cast
  simp only [smul_sub, smul_add, smul_smul]
  have hc (z : ℂ) : -(Complex.I / 2) * (Complex.I * z) = z / 2 := by
    calc
      -(Complex.I / 2) * (Complex.I * z) = -(Complex.I * Complex.I) * z / 2 := by ring
      _ = z / 2 := by rw [Complex.I_mul_I]; ring
  rw [hc, hc]
  module

/-- The real part of the genuine complex Fourier spatial derivative. -/
def derivative (N : ℕ) : RealCircleL2 →L[ℝ] RealCircleL2 :=
  realPart.comp (((FourierProjection.derivative N).restrictScalars ℝ).comp complexify)

theorem derivative_apply (N : ℕ) (f : RealCircleL2) :
    derivative N f = realPart (FourierProjection.derivative N (complexify f)) := rfl

theorem derivative_cosine (N k : ℕ) (hk : k ≤ N) :
    derivative N (RealGalerkin.cosineL2 k) = -(k : ℝ) • RealGalerkin.sineL2 k := by
  rw [derivative_apply, derivative_complexify_cosine N k hk, realPart_complexify]

theorem derivative_sine (N k : ℕ) (hk : k ≤ N) :
    derivative N (RealGalerkin.sineL2 k) = (k : ℝ) • RealGalerkin.cosineL2 k := by
  rw [derivative_apply, derivative_complexify_sine N k hk, realPart_complexify]

theorem cosine_mem (N k : ℕ) (hk : k ≤ N) : RealGalerkin.cosineL2 k ∈ RealGalerkin.space N := by
  apply Submodule.subset_span
  refine ⟨(⟨k, by omega⟩, true), ?_⟩
  rfl

theorem sine_mem (N k : ℕ) (hk : k ≤ N) : RealGalerkin.sineL2 k ∈ RealGalerkin.space N := by
  apply Submodule.subset_span
  refine ⟨(⟨k, by omega⟩, false), ?_⟩
  rfl

theorem derivative_mem (N : ℕ) {f : RealCircleL2} (hf : f ∈ RealGalerkin.space N) :
    derivative N f ∈ RealGalerkin.space N := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨k, b⟩, rfl⟩ := hx
      have hk : k.val ≤ N := by omega
      cases b
      · simpa only [RealGalerkin.realMode, Bool.false_eq_true, ↓reduceIte,
          derivative_sine N k.val hk] using
          (RealGalerkin.space N).smul_mem (k : ℝ) (cosine_mem N k.val hk)
      · simpa only [RealGalerkin.realMode, ↓reduceIte,
          derivative_cosine N k.val hk] using
          (RealGalerkin.space N).smul_mem (-(k : ℝ)) (sine_mem N k.val hk)
  | zero => simpa only [map_zero] using (RealGalerkin.space N).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using (RealGalerkin.space N).add_mem ihx ihy
  | smul a x hx ih => simpa only [map_smul] using (RealGalerkin.space N).smul_mem a ih

theorem derivative_norm_le (N : ℕ) (f : RealCircleL2) :
    ‖derivative N f‖ ≤ (N : ℝ) * ‖f‖ := by
  rw [derivative_apply]
  exact (realPart_norm_le _).trans (by
    simpa only [complexify_norm] using FourierProjection.derivative_norm_le N (complexify f))

/-- Actual bounded spatial derivative on the same finite real space as projectedMaterial. -/
def finiteDerivative (N : ℕ) : RealGalerkin.space N →L[ℝ] RealGalerkin.space N :=
  ((derivative N).comp (RealGalerkin.space N).subtypeL).codRestrict
    (RealGalerkin.space N) (fun f => derivative_mem N f.property)

theorem finiteDerivative_coe (N : ℕ) (f : RealGalerkin.space N) :
    (finiteDerivative N f : RealCircleL2) = derivative N (f : RealCircleL2) := rfl

theorem finiteDerivative_norm_le (N : ℕ) (f : RealGalerkin.space N) :
    ‖finiteDerivative N f‖ ≤ (N : ℝ) * ‖f‖ := derivative_norm_le N f

theorem finiteDerivative_operator_norm_le (N : ℕ) : ‖finiteDerivative N‖ ≤ (N : ℝ) := by
  apply (finiteDerivative N).opNorm_le_bound (Nat.cast_nonneg N)
  exact finiteDerivative_norm_le N

end KerrKoopman.RealFourierDerivative
