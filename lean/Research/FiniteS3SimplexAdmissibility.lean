import Mathlib.Tactic

/-!
# Finite S³ simplex: exact algebraic wall certificates

The domain is the boundary of a four-simplex (a triangulated S³). The five
unit-quaternion site vectors are e₀,e₁,e₂,e₃,(-1/2,-1/2,-1/2,-1/2).
The independent SymPy checker constructs all five tetrahedral faces and their
4×4 determinants. At t=1/6 the facet opposite e₀ contains the origin in its
convex hull, so normalized affine interpolation fails to be defined there.

This file checks only elementary rational/polynomial certificates. It does NOT
kernel-formalize convex hull membership, the topological degree theorem,
continuous homotopy, Skyrme dynamics or any gravitational field equations.
-/

namespace FiniteS3SimplexAdmissibility

/-- All five initial simplex coefficients are strictly positive and sum to one. -/
theorem initial_weights_sum :
    4 * (1 / 6 : ℝ) + (1 / 3 : ℝ) = 1 := by
  norm_num

/-- Each coordinate of their convex combination is zero. -/
theorem initial_origin_coordinate :
    (1 / 6 : ℝ) + (1 / 3 : ℝ) * (-1 / 2) = 0 := by
  norm_num

/-- Unnormalized coefficients for the affine preimage of the origin. -/
theorem moving_barycentric_sum (t : ℝ) :
    (1 - 6 * t) + 3 + 2 = 6 * (1 - t) := by
  ring

/-- The zeroth coordinate vanishes with the unnormalized weights. -/
theorem moving_origin_coordinate_zero (t : ℝ) :
    (1 - 6 * t) + 3 * t + (3 * t - 1) = 0 := by
  ring

/-- Each of the other three coordinates vanishes. -/
theorem moving_origin_other_coordinates (t : ℝ) :
    (1 - t) + (t - 1) = 0 := by
  ring

/-- Positive weights on the obstructing tetrahedral facet. -/
theorem wall_facet_weights_sum :
    3 * (1 / 5 : ℝ) + (2 / 5 : ℝ) = 1 := by
  norm_num

/-- Facet zero: the first Cartesian coordinate, at t=1/6. -/
theorem wall_facet_coordinate_zero :
    3 * (1 / 5 : ℝ) * (1 / 6) + (2 / 5) * (-1 / 4) = 0 := by
  norm_num

/-- Facet zero: each of the remaining three coordinates, at t=1/6. -/
theorem wall_facet_coordinate_other :
    (1 / 5 : ℝ) * (5 / 6) + (2 / 5) * (-5 / 12) = 0 := by
  norm_num

/-- The affine obstruction is on the unique rational wall t=1/6. -/
theorem wall_parameter_iff (t : ℝ) :
    (6 * t - 1) / 5 = 0 ↔ t = 1 / 6 := by
  constructor <;> intro h <;> linarith

/-- The same L=(5,-1,-1,-1) evaluates to 6t-1 on the four moving vertices. -/
theorem separating_functional_coordinates (t : ℝ) :
    5 * t - (1 - t) = 6 * t - 1 ∧
    5 * ((3 * t - 1) / 2) - 3 * ((t - 1) / 2) = 6 * t - 1 := by
  constructor <;> ring

/-- Both squared normalization factors are strictly positive for all real t. -/
theorem moving_vertex_norms_pos (t : ℝ) :
    0 < 2 * t ^ 2 - 2 * t + 1 ∧
    0 < 3 * t ^ 2 - 3 * t + 1 := by
  constructor <;> nlinarith [sq_nonneg (t - (1 / 2 : ℝ))]

/-- Polynomial factor for the face opposite the first vertex; the matrix
    determinant-to-polynomial step is independently checked in SymPy. -/
theorem opposite_facet_determinant_polynomial (t : ℝ) :
    3 * t ^ 4 - (19 / 2) * t ^ 3 + (21 / 2) * t ^ 2 -
        (9 / 2) * t + (1 / 2) =
      (t - 1) ^ 3 * (6 * t - 1) / 2 := by
  ring

end FiniteS3SimplexAdmissibility
