
/-!
# Differentiation of the actual finite Fourier polynomial

The bounded map is d/dx composed with the exact Fourier cutoff. Its multiplier
is i*k on the circle of circumference 2*pi. The norm estimate is proved from
orthonormality, not assumed as a finite matrix bound.
-/

noncomputable section

open scoped ComplexConjugate

namespace KerrKoopman.FourierProjection

/-- Spatial derivative after the exact Fourier cutoff. -/
def derivative (N : ℕ) : CircleL2 →L[ℂ] CircleL2 :=
  ∑ k ∈ frequencies N,
    (Complex.I * (k : ℂ)) • InnerProductSpace.rankOne ℂ (basis k) (basis k)

theorem derivative_apply (N : ℕ) (f : CircleL2) :
    derivative N f = ∑ k ∈ frequencies N,
      (Complex.I * (k : ℂ) * inner ℂ (basis k) f) • basis k := by
  simp [derivative, InnerProductSpace.rankOne_apply, smul_smul]

theorem derivative_coefficient (N : ℕ) (f : CircleL2) (k : ℤ) :
    inner ℂ (basis k) (derivative N f) =
      if k ∈ frequencies N then Complex.I * (k : ℂ) * inner ℂ (basis k) f else 0 := by
  classical
  rw [derivative_apply]
  simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp basis.orthonormal]

/-- The derivative annihilates the mean Fourier coefficient. -/
theorem derivative_mean_zero (N : ℕ) (f : CircleL2) :
    inner ℂ (basis 0) (derivative N f) = 0 := by
  simp [derivative_coefficient]

theorem derivative_mem_bandlimited (N : ℕ) (f : CircleL2) :
    derivative N f ∈ bandlimited N := by
  rw [derivative_apply]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨k, hk, rfl⟩

/-- Skew symmetry of the actual finite Fourier spatial derivative. -/
theorem derivative_inner (N : ℕ) (f g : CircleL2) :
    inner ℂ (derivative N f) g = -inner ℂ f (derivative N g) := by
  simp only [derivative_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    map_mul, Complex.conj_I, map_intCast, inner_conj_symm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem derivative_norm_sq (N : ℕ) (f : CircleL2) :
    ‖derivative N f‖ ^ 2 = ∑ k ∈ frequencies N,
      ‖Complex.I * (k : ℂ) * inner ℂ (basis k) f‖ ^ 2 := by
  rw [derivative_apply]
  simpa only [LinearIsometry.toSpanSingleton_apply] using
    basis.orthonormal.orthogonalFamily.norm_sum
      (fun k => Complex.I * (k : ℂ) * inner ℂ (basis k) f) (frequencies N)

theorem frequency_norm_le (N : ℕ) {k : ℤ} (hk : k ∈ frequencies N) :
    ‖(k : ℂ)‖ ≤ (N : ℝ) := by
  have h := Finset.mem_Icc.mp hk
  have hreal : |(k : ℝ)| ≤ (N : ℝ) := by
    apply abs_le.mpr
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  simpa using hreal

theorem derivative_norm_le (N : ℕ) (f : CircleL2) :
    ‖derivative N f‖ ≤ (N : ℝ) * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg N) (norm_nonneg f))).mp
  rw [derivative_norm_sq, mul_pow]
  calc
    ∑ k ∈ frequencies N, ‖Complex.I * (k : ℂ) * inner ℂ (basis k) f‖ ^ 2
      ≤ ∑ k ∈ frequencies N, (N : ℝ)^2 * ‖inner ℂ (basis k) f‖^2 := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [norm_mul, Complex.norm_I, one_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (frequency_norm_le N hk) 2)
          (sq_nonneg _)
    _ = (N : ℝ)^2 * ∑ k ∈ frequencies N, ‖inner ℂ (basis k) f‖^2 := by
      rw [Finset.mul_sum]
    _ ≤ (N : ℝ)^2 * ‖f‖^2 := by
      exact mul_le_mul_of_nonneg_left
        (basis.orthonormal.sum_inner_products_le (s := frequencies N) f) (sq_nonneg _)

theorem derivative_operator_norm_le (N : ℕ) : ‖derivative N‖ ≤ (N : ℝ) := by
  apply (derivative N).opNorm_le_bound (Nat.cast_nonneg N)
  exact derivative_norm_le N

/-- The spatial derivative as an endomorphism of the actual finite Fourier space. -/
def bandlimitedDerivative (N : ℕ) : bandlimited N →L[ℂ] bandlimited N :=
  ((derivative N).codRestrict (bandlimited N) (derivative_mem_bandlimited N)).comp
    (bandlimited N).subtypeL

theorem bandlimitedDerivative_coe (N : ℕ) (f : bandlimited N) :
    (bandlimitedDerivative N f : CircleL2) = derivative N (f : CircleL2) := rfl

theorem bandlimitedDerivative_norm_le (N : ℕ) (f : bandlimited N) :
    ‖bandlimitedDerivative N f‖ ≤ (N : ℝ) * ‖f‖ :=
  derivative_norm_le N (f : CircleL2)

theorem bandlimitedDerivative_operator_norm_le (N : ℕ) :
    ‖bandlimitedDerivative N‖ ≤ (N : ℝ) := by
  apply (bandlimitedDerivative N).opNorm_le_bound (Nat.cast_nonneg N)
  exact bandlimitedDerivative_norm_le N

theorem derivative_projection (N : ℕ) (f : CircleL2) :
    derivative N (projection N f) = derivative N f := by
  rw [derivative_apply N (projection N f)]
  conv_rhs => rw [derivative_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [projection_coefficient, ite_eq_left hk]

/-- The smooth periodic representative of the projected L2 element. -/
def polynomial (N : ℕ) (f : CircleL2) (x : ℝ) : ℂ :=
  ∑ k ∈ frequencies N, inner ℂ (basis k) f * fourier k (x : AddCircle (2 * Real.pi))

/-- The corresponding classical derivative of that representative. -/
def polynomialDerivative (N : ℕ) (f : CircleL2) (x : ℝ) : ℂ :=
  ∑ k ∈ frequencies N,
    (Complex.I * (k : ℂ) * inner ℂ (basis k) f) *
      fourier k (x : AddCircle (2 * Real.pi))

/-- The continuous circle representative, before taking its L2 equivalence class. -/
def circlePolynomial (N : ℕ) (f : CircleL2) : C(AddCircle (2 * Real.pi), ℂ) :=
  ∑ k ∈ frequencies N, inner ℂ (basis k) f • fourier k

theorem circlePolynomial_toLp (N : ℕ) (f : CircleL2) :
    ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (circlePolynomial N f) =
      projection N f := by
  simp [circlePolynomial, projection_apply, basis, coe_fourierBasis, fourierLp]

theorem circlePolynomial_apply (N : ℕ) (f : CircleL2) (x : ℝ) :
    circlePolynomial N f (x : AddCircle (2 * Real.pi)) = polynomial N f x := by
  simp [circlePolynomial, polynomial]

theorem hasDerivAt_polynomial (N : ℕ) (f : CircleL2) (x : ℝ) :
    HasDerivAt (polynomial N f) (polynomialDerivative N f x) x := by
  unfold polynomial polynomialDerivative
  convert HasDerivAt.fun_sum (fun k (_ : k ∈ frequencies N) =>
    (hasDerivAt_fourier (2 * Real.pi) k x).const_mul (inner ℂ (basis k) f)) using 1
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end KerrKoopman.FourierProjection
