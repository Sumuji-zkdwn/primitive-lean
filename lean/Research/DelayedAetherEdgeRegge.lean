import Mathlib

/-!
# Delayed-aether edge/Regge algebraic certificates (stages 29–30)

This is a **narrow** Lean formalization. We prove:
* seven local squared-edge measurements induced by one constant symmetric
  three-metric satisfy a single compatibility identity;
* a flat but non-affine coordinate embedding can violate that finite-stencil
  identity without introducing Riemannian curvature;
* an explicitly GIVEN rank-one five-edge Hessian annihilates vectors whose
  coordinate sum is zero, while a fixed edge-spring term removes that kernel;
* a curvature-memory term with the SAME rank-one direction preserves it.

The Regge Hessian coefficient and geometric origin are **assumptions** here,
supported by independent finite computations in stage 30. This file does NOT
derive the Regge action, quantify lattice graviton modes, prove Einstein
constraints, or derive physical gravity from gel-like dynamics.
-/

namespace DelayedAetherEdgeRegge

/-- Deviation of seven squared edge lengths from a single constant 3-metric. -/
def mismatch (b : Fin 7 → ℝ) : ℝ :=
  b 6 - b 3 - b 4 - b 5 + b 0 + b 1 + b 2

/-- The 3 axis, 3 face-diagonal and 1 body-diagonal squared lengths
    in terms of six entries of a symmetric bilinear form. -/
def metricEdges (g11 g22 g33 g12 g13 g23 : ℝ) : Fin 7 → ℝ :=
  ![g11, g22, g33,
    g11 + g22 + 2 * g12,
    g11 + g33 + 2 * g13,
    g22 + g33 + 2 * g23,
    g11 + g22 + g33 + 2 * g12 + 2 * g13 + 2 * g23]

/-- Any such metric's seven squared-length measurements satisfy the identity. -/
theorem metricEdges_mismatch_zero
    (g11 g22 g33 g12 g13 g23 : ℝ) :
    mismatch (metricEdges g11 g22 g33 g12 g13 g23) = 0 := by
  simp [mismatch, metricEdges]
  ring

/-- A flat Euclidean embedding with a non-affine coordinate change can have a
    finite-stencil mismatch. This is an exact algebraic identity; it is NOT a
    nonzero-curvature certificate. -/
theorem flat_stencil_mismatch (a eps : ℝ) :
    mismatch
      (![a ^ 2, a ^ 2, a ^ 2, 2 * a ^ 2, 2 * a ^ 2,
         2 * a ^ 2 + (eps * a ^ 2) ^ 2,
         (a + eps * a ^ 2) ^ 2 + 2 * a ^ 2]) =
      2 * eps * a ^ 3 := by
  simp [mismatch]
  ring

/-- Algebraic rank-one model for the 5-edge Hessian on a 4D 1–5 Regge patch.
    The coefficient `c` (e.g. `8 * sqrt 5`) is NOT derived in this file. -/
def rankOne (c : ℝ) (v : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun _ => c * ∑ i, v i

/-- Every sum-zero edge variation is in the rank-one Hessian kernel. -/
theorem rankOne_zero_on_sum_zero (c : ℝ) (v : Fin 5 → ℝ)
    (hv : ∑ i, v i = 0) :
    rankOne c v = fun _ => 0 := by
  funext i
  simp [rankOne, hv]

/-- Fixed-edge spring term adds a full-rank identity to the rank-one matrix. -/
def edgeSpring (c : ℝ) (v : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun i => rankOne c v i + v i

/-- On the old gauge directions, the spring energy responds nontrivially. -/
theorem edgeSpring_on_sum_zero (c : ℝ) (v : Fin 5 → ℝ)
    (hv : ∑ i, v i = 0) :
    edgeSpring c v = v := by
  funext i
  simp [edgeSpring, rankOne, hv]

/-- The former sum-zero kernel is removed by adding the identity. -/
theorem edgeSpring_zero_implies_zero (c : ℝ) (v : Fin 5 → ℝ)
    (hv : ∑ i, v i = 0)
    (hs : edgeSpring c v = fun _ => 0) :
    v = fun _ => 0 := by
  calc
    v = edgeSpring c v := (edgeSpring_on_sum_zero c v hv).symm
    _ = fun _ => 0 := hs

/-- Curvature memory is modeled only by an additional rank-one coefficient. -/
def curvatureMemory (c eta : ℝ) (v : Fin 5 → ℝ) : Fin 5 → ℝ :=
  rankOne (c + eta) v

/-- A rank-one curvature-memory correction preserves every sum-zero direction. -/
theorem curvatureMemory_preserves_sum_zero (c eta : ℝ) (v : Fin 5 → ℝ)
    (hv : ∑ i, v i = 0) :
    curvatureMemory c eta v = fun _ => 0 := by
  exact rankOne_zero_on_sum_zero (c + eta) v hv

end DelayedAetherEdgeRegge
