import KerrKoopman.MaterialL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Actual real trigonometric Galerkin material map

The subspace is constructed from the real and imaginary parts of the actual
normalized-circle Fourier monomials of frequencies 0,...,N. Its orthogonal
projection is constructed, not assumed. Thus reality is built into the state
space and the nonlinear material map remains the real constitutive law.
This file does not yet identify this real projection with the preceding
complex Fourier projection under complexification.
-/

noncomputable section

open MeasureTheory
open KerrKoopman.FourierProjection KerrKoopman.MaterialL2

namespace KerrKoopman.RealGalerkin

abbrev Circle := AddCircle (2 * Real.pi)

/-- The actual cosine character as a real continuous function on the circle. -/
def cosine (k : ℕ) : C(Circle, ℝ) :=
  ⟨fun x => (fourier (k : ℤ) x).re,
    Complex.continuous_re.comp (fourier (k : ℤ)).continuous⟩

/-- The actual sine character as a real continuous function on the circle. -/
def sine (k : ℕ) : C(Circle, ℝ) :=
  ⟨fun x => (fourier (k : ℤ) x).im,
    Complex.continuous_im.comp (fourier (k : ℤ)).continuous⟩

def cosineL2 (k : ℕ) : RealCircleL2 :=
  ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ (cosine k)

def sineL2 (k : ℕ) : RealCircleL2 :=
  ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ (sine k)

/-- A finite explicit family; the harmless zero sine mode may be redundant. -/
def realMode (N : ℕ) (i : Fin (N + 1) × Bool) : RealCircleL2 :=
  if i.2 then cosineL2 i.1 else sineL2 i.1

/-- The actual real trigonometric polynomial subspace, with frequencies at most N. -/
def space (N : ℕ) : Submodule ℝ RealCircleL2 :=
  Submodule.span ℝ (Set.range (realMode N))

instance space_finiteDimensional (N : ℕ) : FiniteDimensional ℝ (space N) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range (realMode N))

/-- Constructed real L2 orthogonal projection onto the concrete trigonometric span. -/
def projection (N : ℕ) : RealCircleL2 →L[ℝ] RealCircleL2 :=
  (space N).starProjection

theorem projection_mem (N : ℕ) (f : RealCircleL2) : projection N f ∈ space N :=
  (space N).starProjection_apply_mem f

theorem projection_eq_self (N : ℕ) {f : RealCircleL2} (hf : f ∈ space N) :
    projection N f = f := (space N).starProjection_eq_self_iff.mpr hf

theorem projection_idempotent (N : ℕ) (f : RealCircleL2) :
    projection N (projection N f) = projection N f :=
  projection_eq_self N (projection_mem N f)

theorem projection_norm_le (N : ℕ) (f : RealCircleL2) :
    ‖projection N f‖ ≤ ‖f‖ := (space N).norm_starProjection_apply_le f

theorem projection_lipschitz (N : ℕ) : LipschitzWith 1 (projection N) :=
  (space N).lipschitzWith_starProjection

theorem projection_inner (N : ℕ) (f g : RealCircleL2) :
    inner ℝ (projection N f) g = inner ℝ f (projection N g) :=
  (space N).inner_starProjection_left_eq_right f g

theorem projection_residual_orthogonal (N : ℕ) (f : RealCircleL2) :
    f - projection N f ∈ (space N)ᗮ :=
  (space N).sub_starProjection_mem_orthogonal f

/-- The actual Galerkin nonlinearity: real pointwise g, then exact L2 projection. -/
def projectedMaterial (N : ℕ) (f : space N) : space N :=
  (space N).orthogonalProjection (material (f : RealCircleL2))

theorem projectedMaterial_coe (N : ℕ) (f : space N) :
    (projectedMaterial N f : RealCircleL2) =
      projection N (material (f : RealCircleL2)) := rfl

theorem projectedMaterial_norm_sub_le (N : ℕ) (f g : space N) :
    ‖projectedMaterial N f - projectedMaterial N g‖ ≤ ‖f - g‖ := by
  change ‖projection N (material (f : RealCircleL2)) -
    projection N (material (g : RealCircleL2))‖ ≤ ‖(f : RealCircleL2) - (g : RealCircleL2)‖
  rw [← map_sub]
  exact (projection_norm_le N _).trans (material_norm_sub_le _ _)

/-- Global L2 Lipschitz continuity is on the actual finite real space. -/
theorem projectedMaterial_lipschitz (N : ℕ) : LipschitzWith 1 (projectedMaterial N) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
    projectedMaterial_norm_sub_le N f g

theorem projectedMaterial_zero (N : ℕ) : projectedMaterial N 0 = 0 := by
  apply Subtype.ext
  simp [projectedMaterial_coe, MaterialL2.material_zero]

end KerrKoopman.RealGalerkin
