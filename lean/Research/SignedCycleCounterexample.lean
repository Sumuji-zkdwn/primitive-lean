import Research.SquareZeroNetwork
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# A signed cycle whose aggregate is nilpotent

This file is intended to be checked against SquareZeroNetwork.lean at
2e450b63d73d23b972920637df503bb425524ce3. Matrix rows are destinations and
columns are sources. `support s t` means that the aggregate coefficient of
the directed edge s -> t is nonzero.
-/

namespace SquareZeroNetwork.SignedCycle

/-- The four nonzero weighted edge transfers, with the signs from the example. -/
def edgeSum (v : Vec 3) : Vec 3 := fun j =>
  edge 1 0 1 v j + edge 2 0 1 v j +
  edge 0 1 1 v j + edge 0 2 (-1) v j

/-- Rows are destinations; columns are sources. -/
def A : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1; 1, 0, 0; -1, 0, 0]

/-- The claimed square, made explicit so it can also serve as a witness. -/
def A2 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 0; 0, 1, 1; 0, -1, -1]

/-- The sum of the original edge maps is exactly multiplication by A. -/
theorem edgeSum_eq_A_mulVec (v : Vec 3) : edgeSum v = A.mulVec v := by
  funext j
  fin_cases j <;>
    simp [edgeSum, edge, A, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Every constituent edge map is square-zero, by the original theorem. -/
theorem edges_square_zero (v : Vec 3) :
    edge 1 0 1 (edge 1 0 1 v) = (fun _ => 0) ∧
    edge 2 0 1 (edge 2 0 1 v) = (fun _ => 0) ∧
    edge 0 1 1 (edge 0 1 1 v) = (fun _ => 0) ∧
    edge 0 2 (-1) (edge 0 2 (-1) v) = (fun _ => 0) := by
  exact ⟨edge_square_zero 1 0 (by decide) 1 v,
    edge_square_zero 2 0 (by decide) 1 v,
    edge_square_zero 0 1 (by decide) 1 v,
    edge_square_zero 0 2 (by decide) (-1) v⟩

theorem square_eq : A ^ 2 = A2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, A2, pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_two]

theorem square_ne_zero : A ^ 2 ≠ 0 := by
  intro h
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 1 1) h
  norm_num [square_eq, A2] at h11

theorem cube_eq_zero : A ^ 3 = 0 := by
  rw [pow_succ, square_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, A2, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_two]

/-- Directed support of the matrix, in source-to-destination order. -/
def support (src dst : Fin 3) : Prop := A dst src ≠ 0

/-- The complete nonzero support consists of exactly the four displayed edges. -/
theorem support_iff (src dst : Fin 3) :
    support src dst ↔
      (src = 1 ∧ dst = 0) ∨ (src = 2 ∧ dst = 0) ∨
      (src = 0 ∧ dst = 1) ∨ (src = 0 ∧ dst = 2) := by
  fin_cases src <;> fin_cases dst <;> norm_num [support, A]

/-- The two length-two directed cycles in the support. -/
theorem two_directed_cycles :
    support 0 1 ∧ support 1 0 ∧ support 0 2 ∧ support 2 0 := by
  norm_num [support, A]

/-- A directly usable package: cyclic support and nilpotency index three. -/
theorem signed_cycle_counterexample :
    support 0 1 ∧ support 1 0 ∧ A ^ 2 ≠ 0 ∧ A ^ 3 = 0 := by
  exact ⟨two_directed_cycles.1, two_directed_cycles.2.1, square_ne_zero, cube_eq_zero⟩

end SquareZeroNetwork.SignedCycle
