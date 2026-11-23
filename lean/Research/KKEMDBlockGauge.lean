import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Universal-gauge 5D Kaluza--Klein block inverse in a 4D normal frame
At any point in a Lorentzian normal frame, q != 0 and all four A_mu
are unrestricted. The scaled 5D covariant and inverse matrices obey
M*N=q^3 I. This is an algebraic slice of the general EMD reduction;
curvature tensors and jet-gauge naturality are not proved here.
-/
namespace KKEMDBlockGauge
abbrev Mat5 := Matrix (Fin 5) (Fin 5) ℚ

def covScaled (q a0 a1 a2 a3 : ℚ) : Mat5 :=
  !![-q^3+a0^2, a0*a1, a0*a2, a0*a3, a0;
     a1*a0, q^3+a1^2, a1*a2, a1*a3, a1;
     a2*a0, a2*a1, q^3+a2^2, a2*a3, a2;
     a3*a0, a3*a1, a3*a2, q^3+a3^2, a3;
     a0, a1, a2, a3, 1]

def contraScaled (q a0 a1 a2 a3 : ℚ) : Mat5 :=
  !![-1, 0, 0, 0, a0;
     0, 1, 0, 0, -a1;
     0, 0, 1, 0, -a2;
     0, 0, 0, 1, -a3;
     a0, -a1, -a2, -a3, q^3-a0^2+a1^2+a2^2+a3^2]

theorem block_inverse_scaled (q a0 a1 a2 a3 : ℚ) :
    covScaled q a0 a1 a2 a3 * contraScaled q a0 a1 a2 a3 =
      !![q^3,0,0,0,0;
         0,q^3,0,0,0;
         0,0,q^3,0,0;
         0,0,0,q^3,0;
         0,0,0,0,q^3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [covScaled, contraScaled, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

def normLorentz (v0 v1 v2 v3 : ℚ) : ℚ :=
  -v0^2+v1^2+v2^2+v3^2

def contraction (a0 a1 a2 a3 v0 v1 v2 v3 : ℚ) : ℚ :=
  a0*v0+a1*v1+a2*v2+a3*v3

def lineElement (q a0 a1 a2 a3 v0 v1 v2 v3 dpsi : ℚ) : ℚ :=
  q*normLorentz v0 v1 v2 v3 +
    (q⁻¹)^2*(dpsi+contraction a0 a1 a2 a3 v0 v1 v2 v3)^2

theorem local_circle_gauge_invariance
    (q a0 a1 a2 a3 b0 b1 b2 b3 v0 v1 v2 v3 dpsi : ℚ) :
    lineElement q (a0-b0) (a1-b1) (a2-b2) (a3-b3)
      v0 v1 v2 v3
      (dpsi+contraction b0 b1 b2 b3 v0 v1 v2 v3) =
    lineElement q a0 a1 a2 a3 v0 v1 v2 v3 dpsi := by
  unfold lineElement contraction normLorentz
  ring

end KKEMDBlockGauge
