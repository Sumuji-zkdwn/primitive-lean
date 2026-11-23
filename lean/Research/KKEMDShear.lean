import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Fibre-shear naturality of a generic symmetric 5D tensor
An arbitrary 4D gauge 1-form is the coordinate shear dpsi' = dpsi+A_mu dx^mu.
Any covariant 5D 2-tensor transforms as R' = T.transpose * R * T.
We prove the triangular change is invertible and the full 25 component
tensor transformation including the vertical and mixed blocks.
This is algebraic gauge naturality, not a Lean proof that a given
metric's Ricci tensor has the universal EMD residual decomposition.
-/
namespace KKEMDShear
abbrev Mat5 := Matrix (Fin 5) (Fin 5) ℚ
def shift (a0 a1 a2 a3 : ℚ) : Mat5 :=
  !![1,0,0,0,0;
     0,1,0,0,0;
     0,0,1,0,0;
     0,0,0,1,0;
     a0,a1,a2,a3,1]
def unshift (a0 a1 a2 a3 : ℚ) : Mat5 :=
  !![1,0,0,0,0;
     0,1,0,0,0;
     0,0,1,0,0;
     0,0,0,1,0;
     -a0,-a1,-a2,-a3,1]

theorem inverse_shears (a0 a1 a2 a3 : ℚ) :
    shift a0 a1 a2 a3 * unshift a0 a1 a2 a3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shift, unshift, Matrix.mul_apply,
      Fin.sum_univ_succ]

def pullback (R : Mat5) (a0 a1 a2 a3 : ℚ) : Mat5 :=
  (shift a0 a1 a2 a3).transpose * R * shift a0 a1 a2 a3

theorem vertical_stable (R : Mat5) (a0 a1 a2 a3 : ℚ) :
    pullback R a0 a1 a2 a3 4 4 = R 4 4 := by
  norm_num [pullback, shift, Matrix.mul_apply, Fin.sum_univ_succ]

theorem mixed_0 (R : Mat5) (a0 a1 a2 a3 : ℚ) :
    pullback R a0 a1 a2 a3 0 4 =
      R 0 4 + a0 * R 4 4 := by
  norm_num [pullback, shift, Matrix.mul_apply, Fin.sum_univ_succ]

theorem mixed_1 (R : Mat5) (a0 a1 a2 a3 : ℚ) :
    pullback R a0 a1 a2 a3 1 4 =
      R 1 4 + a1 * R 4 4 := by
  norm_num [pullback, shift, Matrix.mul_apply, Fin.sum_univ_succ]

theorem mixed_2 (R : Mat5) (a0 a1 a2 a3 : ℚ) :
    pullback R a0 a1 a2 a3 2 4 =
      R 2 4 + a2 * R 4 4 := by
  norm_num [pullback, shift, Matrix.mul_apply, Fin.sum_univ_succ]

theorem mixed_3 (R : Mat5) (a0 a1 a2 a3 : ℚ) :
    pullback R a0 a1 a2 a3 3 4 =
      R 3 4 + a3 * R 4 4 := by
  norm_num [pullback, shift, Matrix.mul_apply, Fin.sum_univ_succ]


/-- Embed the four base coordinates into the five-dimensional index. -/
def up (i : Fin 4) : Fin 5 := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

def gaugeComponent (a0 a1 a2 a3 : ℚ) (i : Fin 4) : ℚ :=
  if i=0 then a0 else if i=1 then a1 else if i=2 then a2 else a3

/-- All 16 horizontal covariant tensor entries under a fibre shear.
Together with the 4 mixed and vertical identities this gives the
whole 25-component algebraic coordinate transformation law. -/
theorem horizontal_all (R : Mat5) (a0 a1 a2 a3 : ℚ)
    (i j : Fin 4) :
    pullback R a0 a1 a2 a3 (up i) (up j) =
      R (up i) (up j) +
      gaugeComponent a0 a1 a2 a3 i * R 4 (up j) +
      gaugeComponent a0 a1 a2 a3 j * R (up i) 4 +
      gaugeComponent a0 a1 a2 a3 i *
        gaugeComponent a0 a1 a2 a3 j * R 4 4 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [pullback, shift, up, gaugeComponent,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end KKEMDShear
