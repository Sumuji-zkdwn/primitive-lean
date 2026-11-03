/-!
# Pair-interaction cocycles as a gravitational specialization of the chain law

A self-contained algebraic supplement to the existing composition/area chain.
For finite, disjoint collections of labelled particles, pair interactions define
a symmetric, exact (coboundary) two-cocycle.  The original signed-area
cocycle is *not* identified with the gravitational one.

The Newton kernel is chosen, not inferred from the cocycle equation.
On a positively oriented one-dimensional separation, differentiating the
chosen 1/r potential gives the inverse-square attractive force.  We do NOT
prove that the cocycle alone forces 1/r, nor general relativity, nor
that the pair potential is well-defined at collisions.
-/

noncomputable section

namespace LinearInputGravityCocycle

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- The new pair interaction between two finite sets of particle labels. -/
def crossEnergy (W : ι → ι → ℝ) (A B : Finset ι) : ℝ :=
  ∑ i ∈ A, ∑ j ∈ B, W i j

theorem cross_empty_left (W : ι → ι → ℝ) (A : Finset ι) :
    crossEnergy W ∅ A = 0 := by
  simp [crossEnergy]

theorem cross_empty_right (W : ι → ι → ℝ) (A : Finset ι) :
    crossEnergy W A ∅ = 0 := by
  simp [crossEnergy]

theorem cross_union_left (W : ι → ι → ℝ) (A B C : Finset ι)
    (hAB : Disjoint A B) :
    crossEnergy W (A ∪ B) C = crossEnergy W A C + crossEnergy W B C := by
  simp [crossEnergy, Finset.sum_union hAB]

theorem cross_union_right (W : ι → ι → ℝ) (A B C : Finset ι)
    (hBC : Disjoint B C) :
    crossEnergy W A (B ∪ C) = crossEnergy W A B + crossEnergy W A C := by
  simp [crossEnergy, Finset.sum_union hBC, Finset.sum_add_distrib]

/-- The cocycle identity is a formal consequence of disjoint-union additivity. -/
theorem cross_cocycle (W : ι → ι → ℝ) (A B C : Finset ι)
    (hAB : Disjoint A B) (hBC : Disjoint B C) :
    crossEnergy W A B + crossEnergy W (A ∪ B) C =
      crossEnergy W B C + crossEnergy W A (B ∪ C) := by
  rw [cross_union_left W A B C hAB, cross_union_right W A B C hBC]
  ring

/-- Symmetric pair interactions produce a symmetric cross term. -/
theorem cross_symmetric (W : ι → ι → ℝ)
    (hW : ∀ i j, W i j = W j i) (A B : Finset ι) :
    crossEnergy W A B = crossEnergy W B A := by
  unfold crossEnergy
  calc
    (∑ i ∈ A, ∑ j ∈ B, W i j) =
        ∑ j ∈ B, ∑ i ∈ A, W i j := by rw [Finset.sum_comm]
    _ = ∑ j ∈ B, ∑ i ∈ A, W j i := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      exact hW i j

/-- Pair energy inside one collection, with self-interactions removed. -/
def internalEnergy (W : ι → ι → ℝ) (A : Finset ι) : ℝ :=
  (crossEnergy W A A - ∑ i ∈ A, W i i) / 2

/-- Additivity fails by precisely the symmetric inter-system interaction. -/
theorem internal_union (W : ι → ι → ℝ)
    (hW : ∀ i j, W i j = W j i)
    (A B : Finset ι) (hAB : Disjoint A B) :
    internalEnergy W (A ∪ B) =
      internalEnergy W A + internalEnergy W B + crossEnergy W A B := by
  unfold internalEnergy
  rw [cross_union_left W A B (A ∪ B) hAB]
  rw [cross_union_right W A A B hAB,
      cross_union_right W B A B hAB]
  rw [Finset.sum_union hAB]
  have hswap : crossEnergy W B A = crossEnergy W A B :=
    cross_symmetric W hW B A
  rw [hswap]
  ring

/-- Unlike the area extension, the symmetric gravitational cocycle is exact. -/
theorem cross_is_coboundary (W : ι → ι → ℝ)
    (hW : ∀ i j, W i j = W j i)
    (A B : Finset ι) (hAB : Disjoint A B) :
    crossEnergy W A B =
      internalEnergy W (A ∪ B) - internalEnergy W A - internalEnergy W B := by
  rw [internal_union W hW A B hAB]
  ring

variable {X : Type*} [MetricSpace X]

/-- Chosen Newtonian potential kernel on labelled non-colliding points.
The if-branch removes self-interaction; distinct labels may still collide,
in which case field-theoretic physical interpretation is excluded. -/
def newtonKernel (G : ℝ) (mass : ι → ℝ) (pos : ι → X)
    (i j : ι) : ℝ :=
  if i = j then 0 else -(G * mass i * mass j) / dist (pos i) (pos j)

theorem newton_kernel_symmetric
    (G : ℝ) (mass : ι → ℝ) (pos : ι → X) (i j : ι) :
    newtonKernel G mass pos i j = newtonKernel G mass pos j i := by
  by_cases hij : i = j
  · subst j
    simp [newtonKernel]
  · have hji : j ≠ i := Ne.symm hij
    simp only [newtonKernel, if_neg hij, if_neg hji]
    rw [dist_comm (pos i) (pos j)]
    ring

theorem newton_cross_symmetric
    (G : ℝ) (mass : ι → ℝ) (pos : ι → X) (A B : Finset ι) :
    crossEnergy (newtonKernel G mass pos) A B =
      crossEnergy (newtonKernel G mass pos) B A := by
  exact cross_symmetric _ (newton_kernel_symmetric G mass pos) A B

/-- Gravitational cross interaction satisfies the generic chain cocycle. -/
theorem newton_cross_cocycle (G : ℝ) (mass : ι → ℝ)
    (pos : ι → X) (A B C : Finset ι)
    (hAB : Disjoint A B) (hBC : Disjoint B C) :
    crossEnergy (newtonKernel G mass pos) A B +
        crossEnergy (newtonKernel G mass pos) (A ∪ B) C =
      crossEnergy (newtonKernel G mass pos) B C +
        crossEnergy (newtonKernel G mass pos) A (B ∪ C) := by
  exact cross_cocycle _ A B C hAB hBC

theorem newton_cross_is_coboundary (G : ℝ) (mass : ι → ℝ)
    (pos : ι → X) (A B : Finset ι) (hAB : Disjoint A B) :
    crossEnergy (newtonKernel G mass pos) A B =
        internalEnergy (newtonKernel G mass pos) (A ∪ B) -
        internalEnergy (newtonKernel G mass pos) A -
        internalEnergy (newtonKernel G mass pos) B := by
  exact cross_is_coboundary _ (newton_kernel_symmetric G mass pos) A B hAB

/-- Potential along an ordered one-dimensional separation x < y. -/
def linePotential (G m1 m2 y x : ℝ) : ℝ :=
  -(G * m1 * m2) / (y - x)

/-- The actual derivative of the chosen inverse-distance potential. -/
theorem line_potential_derivative
    (G m1 m2 y x : ℝ) (hxy : x < y) :
    HasDerivAt (linePotential G m1 m2 y)
      (-(G * m1 * m2) / (y - x) ^ 2) x := by
  have hsep : y - x ≠ 0 := ne_of_gt (sub_pos.mpr hxy)
  have hden : HasDerivAt (fun t : ℝ => y - t) (-1) x := by
    convert (hasDerivAt_const x y).sub (hasDerivAt_id x) using 1 <;> ring
  have hnum : HasDerivAt (fun _ : ℝ => -(G * m1 * m2)) 0 x :=
    hasDerivAt_const x _
  have h := hnum.div hden hsep
  convert h using 1 <;> dsimp [linePotential] <;> ring

/-- Negative potential gradient is a positive inverse-square attraction. -/
theorem line_force_inverse_square
    (G m1 m2 y x : ℝ) (hxy : x < y) :
    -deriv (linePotential G m1 m2 y) x =
      G * m1 * m2 / (y - x) ^ 2 := by
  rw [(line_potential_derivative G m1 m2 y x hxy).deriv]
  ring

theorem line_force_attractive
    (G m1 m2 y x : ℝ) (hG : 0 < G) (hm1 : 0 < m1)
    (hm2 : 0 < m2) (hxy : x < y) :
    0 < -deriv (linePotential G m1 m2 y) x := by
  rw [line_force_inverse_square G m1 m2 y x hxy]
  exact div_pos (mul_pos (mul_pos hG hm1) hm2)
    (pow_pos (sub_pos.mpr hxy) 2)

end LinearInputGravityCocycle
