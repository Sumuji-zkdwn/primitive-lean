import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Finite-jet Levi-Civita bridge for a local Cartesian KK metric

Coordinates: (t,x,y,z,psi). The exact 5D metric is
  ds5^2=-dt^2+H(dx^2+dy^2+dz^2)+H^-1(dpsi+U dy)^2,
on the affine local patch H=1+a*z, U=a*x, H!=0.

The two finite derivative tables below represent the *first partial
derivatives* of the genuine metric. Their agreement with derivatives of
the original metric is independently checked in
tools/check_kk_cartesian_jet.py; two selected component derivatives are also
formally proved with HasDerivAt below.

Lean verifies the full 5x5 polynomial inverse identity and selected
Levi-Civita connection entries computed by a finite tensor sum.
Second derivatives and the Ricci tensor are not formalized here.
-/

namespace KKCartesianJet

abbrev Mat5 := Matrix (Fin 5) (Fin 5) ℚ

/-- The polynomial matrix H*G5. -/
def scaledMetric (h u : ℚ) : Mat5 :=
  !![-h, 0, 0, 0, 0;
     0, h^2, 0, 0, 0;
     0, 0, h^2+u^2, 0, u;
     0, 0, 0, h^2, 0;
     0, 0, u, 0, 1]

/-- The polynomial matrix H*G5^{-1}. -/
def scaledInverse (h u : ℚ) : Mat5 :=
  !![-h, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, -u;
     0, 0, 0, 1, 0;
     0, 0, -u, 0, h^2+u^2]

/-- All 25 entries of the nontrivial polynomial inverse certificate. -/
theorem scaled_inverse_product (h u : ℚ) :
    scaledMetric h u * scaledInverse h u =
      !![h^2, 0, 0, 0, 0;
         0, h^2, 0, 0, 0;
         0, 0, h^2, 0, 0;
         0, 0, 0, h^2, 0;
         0, 0, 0, 0, h^2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [scaledMetric, scaledInverse,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The original G5 and a candidate inverse. -/
def metric (h u : ℚ) : Mat5 := (h⁻¹) • scaledMetric h u
def inverse (h u : ℚ) : Mat5 := (h⁻¹) • scaledInverse h u


/-- The normalized G5 and its candidate inverse multiply to the identity
when H!=0. This closes the gap between the scaled polynomial relation
and the actual 5x5 rational inverse used by gamma. -/
theorem metric_inverse_product (h u : ℚ) (hh : h ≠ 0) :
    metric h u * inverse h u = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [metric, inverse, scaledMetric, scaledInverse,
      Matrix.mul_apply, Fin.sum_univ_succ, hh] <;>
      field_simp [hh] <;> ring

/-- First metric jet: H is x-independent; ∂x U=a. -/
def dxMetric (h u a : ℚ) : Mat5 :=
  !![0,0,0,0,0;
     0,0,0,0,0;
     0,0,2*u*a/h,0,a/h;
     0,0,0,0,0;
     0,0,a/h,0,0]

/-- First metric jet: ∂z H=a; U is z-independent. -/
def dzMetric (h u a : ℚ) : Mat5 :=
  !![0,0,0,0,0;
     0,a,0,0,0;
     0,0,a-a*u^2/h^2,0,-a*u/h^2;
     0,0,0,a,0;
     0,0,-a*u/h^2,0,-a/h^2]

def partialMetric (h u a : ℚ) (coordinate : Fin 5) : Mat5 :=
  if coordinate = 1 then dxMetric h u a
  else if coordinate = 3 then dzMetric h u a
  else 0

/-- Christoffel contraction Γ^i_jk from the finite first jet:
    (1/2) Σ_m G^im (∂j G_mk + ∂k G_mj - ∂m G_jk). -/
def gamma (h u a : ℚ) (i j k : Fin 5) : ℚ :=
  (∑ m : Fin 5, inverse h u i m *
    (partialMetric h u a j m k +
     partialMetric h u a k m j -
     partialMetric h u a m j k)) / 2

/-- Every prescribed first-derivative matrix is symmetric in its metric indices. -/
theorem partialMetric_symmetric (h u a : ℚ) (direction i j : Fin 5) :
    partialMetric h u a direction i j =
      partialMetric h u a direction j i := by
  fin_cases direction <;> fin_cases i <;> fin_cases j <;>
    norm_num [partialMetric, dxMetric, dzMetric]

/-- The finite-jet connection is torsion-free. -/
theorem gamma_symmetric (h u a : ℚ) (i j k : Fin 5) :
    gamma h u a i j k = gamma h u a i k j := by
  unfold gamma
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [partialMetric_symmetric h u a m j k]
  ring

/-- A fibre-fibre connection component Γ^z_{ψψ}. -/
theorem gamma_z_fibre_fibre (h u a : ℚ) (hh : h ≠ 0) :
    gamma h u a 3 4 4 = a / (2*h^3) := by
  norm_num [gamma, inverse, scaledInverse, partialMetric, dzMetric,
    dxMetric, Fin.sum_univ_succ]
  field_simp [hh]

/-- Mixed x/y/fibre connection component. -/
theorem gamma_x_y_fibre (h u a : ℚ) (hh : h ≠ 0) :
    gamma h u a 1 2 4 = -a / (2*h^2) := by
  norm_num [gamma, inverse, scaledInverse, partialMetric, dzMetric,
    dxMetric, Fin.sum_univ_succ]
  field_simp [hh]

/-- The Γ^z_{yψ} mixed component depends on U. -/
theorem gamma_z_y_fibre (h u a : ℚ) (hh : h ≠ 0) :
    gamma h u a 3 2 4 = a*u / (2*h^3) := by
  norm_num [gamma, inverse, scaledInverse, partialMetric, dzMetric,
    dxMetric, Fin.sum_univ_succ]
  field_simp [hh]

theorem gamma_z_x_x (h u a : ℚ) (hh : h ≠ 0) :
    gamma h u a 3 1 1 = -a / (2*h) := by
  norm_num [gamma, inverse, scaledInverse, partialMetric, dzMetric,
    dxMetric, Fin.sum_univ_succ]
  field_simp [hh]

theorem gamma_z_z_z (h u a : ℚ) (hh : h ≠ 0) :
    gamma h u a 3 3 3 = a / (2*h) := by
  norm_num [gamma, inverse, scaledInverse, partialMetric, dzMetric,
    dxMetric, Fin.sum_univ_succ]
  field_simp [hh]



/-!
## Actual one-variable calculus for two first-jet entries

Unlike the rational first-jet tables, the next three theorems are about
real differentiable functions and use Mathlib's HasDerivAt calculus.
They verify the affine potential, the fibre metric G[psi,psi] = H^-1
as a function of z, and the mixed metric G[y,psi]=U/H as a function
of x at a fixed z. This is *not* yet a full 5D fderiv proof.
-/

/-- H(z)=1+a*z has actual derivative a. -/
theorem affine_H_hasDerivAt (a z : ℝ) :
    HasDerivAt (fun w : ℝ => 1 + a*w) a z := by
  have hmul : HasDerivAt (fun w : ℝ => a*w) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  simpa using (HasDerivAt.const_add (1 : ℝ) hmul)

/-- The fifth-dimensional circle metric G[psi,psi]=H^-1 is genuinely
differentiable with the exact dz jet from the metric. -/
theorem fibre_metric_dz_hasDerivAt (a z : ℝ) (hh : 1+a*z ≠ 0) :
    HasDerivAt (fun w : ℝ => (1+a*w)⁻¹)
      (-a/(1+a*z)^2) z := by
  exact (affine_H_hasDerivAt a z).fun_inv hh

/-- At fixed z, the mixed G[y,psi] = a*x/H has actual x-derivative a/H. -/
theorem mixed_metric_dx_hasDerivAt (a x z : ℝ) :
    HasDerivAt (fun w : ℝ => a*w/(1+a*z))
      (a/(1+a*z)) x := by
  have hm : HasDerivAt (fun w : ℝ => a*w) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  simpa [div_eq_mul_inv] using (hm.mul_const ((1+a*z)⁻¹))

end KKCartesianJet
