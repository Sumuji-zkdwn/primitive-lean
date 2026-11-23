import Mathlib

/-!
# Stage 32: finite four-dimensional 2–4 Pachner-edge certificates

**Scope.** Two Euclidean 4-simplices sharing a tetrahedron are replaced by
four 4-simplices surrounding a new internal edge (4,5). The fourteen old
boundary edges are fixed. The 4D Regge action and its Schläfli derivative
are *inputs from known geometry*, not consequences of a primitive aether law.

This module proves finite combinatorial and rational/real algebra claims.
The actual 4-simplex Gram inverse, dihedral arccos, Schläfli identity,
second derivative of the full Regge action, and nonlinear dynamics are
independently checked in Python/SymPy/mpmath, **not** proved here in Lean.
No Lorentzian spacetime, two propagating graviton modes, or emergence of GR.
-/

namespace DelayedAetherPachner32

/-- Four vertices 0..3 form a common tetrahedron, with opposite vertices
    4 and 5. Its fourteen old edges exclude precisely the new edge (4,5). -/
def boundaryEdges : Finset (Nat × Nat) :=
  {(0,1), (0,2), (0,3), (1,2), (1,3), (2,3),
   (0,4), (1,4), (2,4), (3,4),
   (0,5), (1,5), (2,5), (3,5)}

def afterEdges : Finset (Nat × Nat) := insert (4,5) boundaryEdges

/-- Exactly four internal triangular hinges appear around the new edge. -/
def internalHinges : Finset (Nat × Nat × Nat) :=
  {(0,4,5), (1,4,5), (2,4,5), (3,4,5)}

theorem boundary_edges_count : boundaryEdges.card = 14 := by decide

theorem inserted_edge_is_new : (4,5) ∉ boundaryEdges := by decide

theorem after_edges_count : afterEdges.card = 15 := by decide

theorem internal_hinges_count : internalHinges.card = 4 := by decide

/-- A rational cosine of the interior dihedral angle about an EF-v triangle.
    This formula is independently derived from the 4x4 4-simplex Gram inverse. -/
def innerCos (s : ℚ) : ℚ := (s-2)/(2*(s-3))

theorem inner_cos_regular : innerCos 1 = 1/4 := by
  norm_num [innerCos]

theorem inner_cos_curved_stationary : innerCos 2 = 0 := by
  norm_num [innerCos]

theorem inner_cos_flat : innerCos (5/2) = -(1/2) := by
  norm_num [innerCos]

/-- The flat interior hinge cosine -1/2 has one nonsingular squared edge. -/
theorem flat_squared_edge_unique (s : ℚ) (hs : s ≠ 3) :
    innerCos s = -(1/2) ↔ s = 5/2 := by
  have hd : (2:ℚ)*(s-3) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact sub_ne_zero.mpr hs
  constructor
  · intro h
    have heq : s-2 = (-(1/2:ℚ))*(2*(s-3)) := by
      apply (div_eq_iff hd).mp
      simpa only [innerCos] using h
    linarith
  · intro h
    rw [h]
    norm_num [innerCos]

/-- Exact difference identity; on 0 < s,t < 8/3, it forces strict
    decrease of the cosine as squared interior length increases. -/
theorem inner_cos_difference (s t : ℚ) (hs : s ≠ 3) (ht : t ≠ 3) :
    innerCos s - innerCos t = (t-s)/(2*(s-3)*(t-3)) := by
  have hds : s-3 ≠ 0 := sub_ne_zero.mpr hs
  have hdt : t-3 ≠ 0 := sub_ne_zero.mpr ht
  unfold innerCos
  field_simp
  ring

/-- Symbolic value of the complete 4x4 Euclidean Gram determinant.
    The underlying matrix determinant is independently computed in SymPy. -/
noncomputable def gram4Det (s : ℝ) : ℝ := s*(8-3*s)/16

theorem gram4_det_positive (s : ℝ) (h0 : 0 < s) (h8 : s < 8/3) :
    0 < gram4Det s := by
  unfold gram4Det
  have h : 0 < 8-3*s := by linarith
  positivity

theorem gram4_det_flat : gram4Det (5/2) = 5/64 := by
  norm_num [gram4Det]

/-- A nonzero angle deficit can still make the Schläfli-reduced gradient
    vanish when the triangle's area derivative has factor (2-s)=0.
    This is an algebraic factor theorem, NOT a Lean proof of Schläfli. -/
theorem stationary_factor (delta s : ℝ) :
    delta*(2-s)=0 ↔ delta=0 ∨ s=2 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hd | hs
    · exact Or.inl hd
    · exact Or.inr (by linarith)
  · rintro (hd | hs)
    · simp [hd]
    · simp [hs]

/-- A chosen nonnegative quadratic curvature-memory energy. -/
theorem memory_quadratic_nonnegative (k mu d u m : ℝ)
    (hk : 0 ≤ k) (hm : 0 ≤ mu) :
    0 ≤ k*(d*u-m)^2+mu*m^2 := by
  exact add_nonneg (mul_nonneg hk (sq_nonneg _))
    (mul_nonneg hm (sq_nonneg _))

/-- Exact Schur-complement polynomial in the coupled curvature/memory Hessian.
    Inserting h=8sqrt(5) and d=-4sqrt(30) requires external geometric inputs. -/
theorem memory_hessian_determinant (h d k mu : ℝ) :
    (h+k*d^2)*(k+mu) - (-k*d)^2 =
      h*(k+mu)+k*mu*d^2 := by
  ring

end DelayedAetherPachner32
