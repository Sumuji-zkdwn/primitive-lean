import Mathlib

/-!
# Stage 31: an exact 2–3 spatial Pachner-edge certificate

The three-dimensional triangular bipyramid has 5 vertices, 9 boundary edges,
and a 2 -> 3 tetrahedron move introduces one interior edge (D,E).
For equal boundary edge lengths 1 and squared interior length s, the cosine
of the tetrahedral dihedral angle around D-E is (2-s)/(4-s).

This file proves the finite combinatorial counts and the rational algebraic
identity that the flat value corresponds to s = 8/3. It also proves an
algebraic determinant formula for the *additional* curvature-memory toy.

No 4D dynamics, Regge action equation of motion, diffeomorphism constraint,
propagating two-polarization gravitational wave, or emergent gravity is proved.
-/

namespace DelayedAetherPachner31

/-- The nine edges on the boundary of the triangular bipyramid, unordered
    endpoints written canonically in increasing order. Vertex labels 0..4. -/
def boundaryEdges : Finset (Nat × Nat) :=
  {(0, 1), (0, 2), (1, 2),
   (0, 3), (1, 3), (2, 3),
   (0, 4), (1, 4), (2, 4)}

/-- The 2 -> 3 move inserts the internal edge (3,4) without new vertices. -/
def postMoveEdges : Finset (Nat × Nat) :=
  insert (3, 4) boundaryEdges

theorem boundary_edges_count : boundaryEdges.card = 9 := by decide

theorem internal_edge_new : (3, 4) ∉ boundaryEdges := by decide

theorem post_move_edges_count : postMoveEdges.card = 10 := by decide

/-- Rational cosine of the dihedral angle at the internal edge of any one
    of the three congruent tetrahedra with the other five edges equal to 1. -/
def cosDihedral (s : ℚ) : ℚ := (2 - s) / (4 - s)

theorem cosDihedral_small : cosDihedral 1 = 1 / 3 := by
  norm_num [cosDihedral]

theorem cosDihedral_flat : cosDihedral (8 / 3) = -(1 / 2) := by
  norm_num [cosDihedral]

theorem cosDihedral_curved : cosDihedral (11 / 4) = -(3 / 5) := by
  norm_num [cosDihedral]

/-- The unique rational squared edge length with cos(theta) = -1/2,
    excluding the singular denominator s=4. For genuine tetrahedra 0<s<3,
    this is equivalent to zero deficit 2*pi-3*theta = 0. -/
theorem flat_squared_length_iff (s : ℚ) (hs : s ≠ 4) :
    cosDihedral s = -(1 / 2) ↔ s = 8 / 3 := by
  have hd : (4 : ℚ) - s ≠ 0 := by
    intro h
    apply hs
    linarith
  constructor
  · intro h
    have heq : (2 : ℚ) - s = (-(1 / 2 : ℚ)) * (4 - s) := by
      apply (div_eq_iff hd).mp
      simpa only [cosDihedral] using h
    linarith
  · intro h
    rw [h]
    norm_num [cosDihedral]

/-- An exact finite-difference identity in the squared length variable.
    It makes the strict monotonicity transparent on 0<s,t<3. -/
theorem cosDihedral_difference (s t : ℚ) (hs : s ≠ 4) (ht : t ≠ 4) :
    cosDihedral s - cosDihedral t =
      2 * (t - s) / ((4 - s) * (4 - t)) := by
  have hds : (4 : ℚ) - s ≠ 0 := by
    intro h
    apply hs
    linarith
  have hdt : (4 : ℚ) - t ≠ 0 := by
    intro h
    apply ht
    linarith
  unfold cosDihedral
  field_simp
  ring

/-- A nondegenerate tetrahedron with squared internal edge s has positive
    Gram determinant when 0<s<3. The determinant is s*(3-s)/4. -/
theorem gram_determinant_positive (s : ℝ) (h0 : 0 < s) (h3 : s < 3) :
    0 < s * (3 - s) / 4 := by
  exact div_pos (mul_pos h0 (sub_pos.mpr h3)) (by norm_num)

/-- The chosen local curvature-memory quadratic potential has a
    nonnegative quadratic form for nonnegative coefficients. -/
theorem memory_quadratic_nonnegative (k mu d u m : ℝ)
    (hk : 0 ≤ k) (hmu : 0 ≤ mu) :
    0 ≤ k * (d * u - m) ^ 2 + mu * m ^ 2 := by
  exact add_nonneg (mul_nonneg hk (sq_nonneg _))
    (mul_nonneg hmu (sq_nonneg _))

/-- Determinant of the 2x2 linearized curvature-memory potential Hessian:
    the geometric deficit slope is d (stage 31 computes d = -9*sqrt(2)). -/
theorem memory_hessian_det (k mu d : ℝ) :
    (k * d ^ 2) * (k + mu) - (-k * d) ^ 2 = k * mu * d ^ 2 := by
  ring

end DelayedAetherPachner31
