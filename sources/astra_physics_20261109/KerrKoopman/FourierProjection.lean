import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Tactic

/-!
# Actual normalized-circle Fourier cutoffs

The operator below is a finite sum of the actual AddCircle Fourier basis,
on L2 for probability Haar measure. No projection properties are hypotheses.
Complex L2 is used here; applying a real material law requires a separate
real-valued-subspace / Nemytskii bridge.
-/

noncomputable section

open scoped ComplexConjugate
open MeasureTheory
open Filter
open scoped Topology

namespace KerrKoopman.FourierProjection

instance positiveTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The actual L2 space on the circle of circumference 2 pi, with total measure one. -/
abbrev CircleL2 := Lp ℂ 2 (@AddCircle.haarAddCircle (2 * Real.pi) positiveTwoPi)

/-- Mathlib's complete orthonormal Fourier basis, with frequencies indexed by integers. -/
def basis : HilbertBasis ℤ ℂ CircleL2 := fourierBasis

/-- The integer frequencies from -N to N inclusive. -/
def frequencies (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- Exact finite Fourier projection, as a continuous linear operator on physical L2. -/
def projection (N : ℕ) : CircleL2 →L[ℂ] CircleL2 :=
  ∑ k ∈ frequencies N, InnerProductSpace.rankOne ℂ (basis k) (basis k)

theorem projection_apply (N : ℕ) (f : CircleL2) :
    projection N f = ∑ k ∈ frequencies N, inner ℂ (basis k) f • basis k := by
  simp [projection, InnerProductSpace.rankOne_apply]

/-- The coefficients are the normalized Haar integrals, not point-grid FFT values. -/
theorem projection_fourierCoeff (N : ℕ) (f : CircleL2) :
    projection N f =
      ∑ k ∈ frequencies N, fourierCoeff f k • fourierLp 2 k := by
  rw [projection_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← basis.repr_apply_apply]
  simp [basis, fourierBasis_repr, coe_fourierBasis]

theorem projection_coefficient (N : ℕ) (f : CircleL2) (k : ℤ) :
    inner ℂ (basis k) (projection N f) =
      if k ∈ frequencies N then inner ℂ (basis k) f else 0 := by
  classical
  rw [projection_apply]
  simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp basis.orthonormal]

theorem projection_idempotent (N : ℕ) (f : CircleL2) :
    projection N (projection N f) = projection N f := by
  rw [projection_apply N (projection N f)]
  conv_rhs => rw [projection_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [projection_coefficient, if_pos hk]

/-- Self-adjointness is proved for the constructed operator. -/
theorem projection_inner (N : ℕ) (f g : CircleL2) :
    inner ℂ (projection N f) g = inner ℂ f (projection N g) := by
  simp only [projection_apply, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, inner_conj_symm]
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

theorem projection_residual_orthogonal (N : ℕ) (f g : CircleL2) :
    inner ℂ (projection N f) (g - projection N g) = 0 := by
  rw [inner_sub_right, projection_inner, projection_inner,
    projection_idempotent, sub_self]

theorem projection_norm_sq (N : ℕ) (f : CircleL2) :
    ‖projection N f‖ ^ 2 =
      ∑ k ∈ frequencies N, ‖inner ℂ (basis k) f‖ ^ 2 := by
  rw [projection_apply]
  simpa only [LinearIsometry.toSpanSingleton_apply] using
    basis.orthonormal.orthogonalFamily.norm_sum
      (fun k => inner ℂ (basis k) f) (frequencies N)

theorem projection_norm_le (N : ℕ) (f : CircleL2) :
    ‖projection N f‖ ≤ ‖f‖ := by
  have h := basis.orthonormal.sum_inner_products_le (s := frequencies N) f
  rw [← projection_norm_sq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem projection_operator_norm_le (N : ℕ) : ‖projection N‖ ≤ 1 := by
  apply (projection N).opNorm_le_bound (by norm_num)
  intro f
  simpa using projection_norm_le N f

theorem projection_lipschitz (N : ℕ) : LipschitzWith 1 (projection N) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa [dist_eq_norm, ← map_sub] using projection_norm_le N (f - g)

/-- The actual finite Fourier subspace of L2. -/
def bandlimited (N : ℕ) : Submodule ℂ CircleL2 :=
  Submodule.span ℂ (basis '' (frequencies N : Set ℤ))

instance bandlimited_finiteDimensional (N : ℕ) :
    FiniteDimensional ℂ (bandlimited N) := by
  exact FiniteDimensional.span_of_finite ℂ ((frequencies N).finite_toSet.image basis)

theorem projection_mem_bandlimited (N : ℕ) (f : CircleL2) :
    projection N f ∈ bandlimited N := by
  rw [projection_apply]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨k, hk, rfl⟩

theorem projection_basis (N : ℕ) (k : ℤ) :
    projection N (basis k) = if k ∈ frequencies N then basis k else 0 := by
  classical
  simp [projection_apply, orthonormal_iff_ite.mp basis.orthonormal]

theorem projection_eq_self (N : ℕ) {f : CircleL2} (hf : f ∈ bandlimited N) :
    projection N f = f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      rw [projection_basis, if_pos (show k ∈ frequencies N from hk)]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
  | smul a x hx ih => simp only [map_smul, ih]

/-- The explicit symmetric cutoffs exhaust every Fourier mode. -/
theorem frequencies_tendsto : Tendsto frequencies atTop atTop := by
  have hm : Monotone frequencies := by
    intro N M hNM k hk
    simp only [frequencies, Finset.mem_Icc] at hk ⊢
    omega
  apply hm.tendsto_atTop_finset
  intro k
  refine ⟨k.natAbs, ?_⟩
  simp only [frequencies, Finset.mem_Icc]
  have hp : k ≤ (k.natAbs : ℤ) := Int.le_natAbs
  have hn : -k ≤ (k.natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using
      (show -k ≤ ((-k).natAbs : ℤ) from Int.le_natAbs)
  omega

/-- Strong convergence of the actual Fourier projections to the original L2 field. -/
theorem projection_tendsto (f : CircleL2) :
    Tendsto (fun N => projection N f) atTop (𝓝 f) := by
  have h := (basis.hasSum_repr f).comp frequencies_tendsto
  simpa only [projection_apply, basis.repr_apply_apply] using h

end KerrKoopman.FourierProjection
