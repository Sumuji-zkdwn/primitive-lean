import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Reusable coordinate curvature of a finite-rank connection

This is a **coordinate/frame algebra** layer, not a global differential
geometric curvature theorem. A connection is given by its coefficients
Γᵃ_{ib} in a finite frame, together with its first partials
∂ᵢ Γᵃ_{jb}. Its curvature is defined by the standard expression

  Rᵃ_{bij} = ∂ᵢ Γᵃ_{jb} - ∂ⱼ Γᵃ_{ib}
           + Σc (Γᵃ_{ic} Γᶜ_{jb} - Γᵃ_{jc} Γᶜ_{ib}).

The result is reusable for Riemannian, Lorentzian, gauge, and
finite-state bundle connections: no metric signature or particular
GH/EMD ansatz is assumed.

The data dΓ are explicitly supplied. A later module must identify
them with actual derivatives of arbitrary smooth connection fields,
and compare this coordinate result with Mathlib's covariant derivative.

Do not interpret this file as a Mathlib Levi-Civita-to-Ricci proof.
-/

namespace FiniteConnectionCurvature

variable {I V R : Type*} [Fintype V] [CommRing R]

/-- Coefficients of a connection on a finite-rank trivial bundle. -/
def Connection (I V R : Type*) := I → V → V → R

/-- The first derivative of each coefficient in the coordinate frame. -/
def FirstJet (I V R : Type*) := I → I → V → V → R

/-- Coordinate curvature: the antisymmetric two-index derivative
and the commutator of connection matrices. -/
def curvature (Γ : Connection I V R) (dΓ : FirstJet I V R)
    (i j : I) (a b : V) : R :=
  dΓ i j a b - dΓ j i a b +
    ∑ c : V, (Γ i a c * Γ j c b - Γ j a c * Γ i c b)

/-- Curvature is antisymmetric in its two base directions. -/
theorem curvature_skew (Γ : Connection I V R)
    (dΓ : FirstJet I V R) (i j : I) (a b : V) :
    curvature Γ dΓ i j a b = -curvature Γ dΓ j i a b := by
  classical
  simp only [curvature, Finset.sum_sub_distrib]
  ring

/-- Every diagonal direction has zero curvature. -/
theorem curvature_same_direction (Γ : Connection I V R)
    (dΓ : FirstJet I V R) (i : I) (a b : V) :
    curvature Γ dΓ i i a b = 0 := by
  simp [curvature]

/-- The zero connection has only the antisymmetric derivative term. -/
theorem curvature_zero_connection (dΓ : FirstJet I V R)
    (i j : I) (a b : V) :
    curvature (fun _ _ _ => 0) dΓ i j a b =
      dΓ i j a b - dΓ j i a b := by
  simp [curvature]

/-- A symmetric first-jet table and zero coefficients are flat. -/
theorem curvature_zero_of_symmetric_jet (dΓ : FirstJet I V R)
    (h : ∀ i j a b, dΓ i j a b = dΓ j i a b)
    (i j : I) (a b : V) :
    curvature (fun _ _ _ => 0) dΓ i j a b = 0 := by
  rw [curvature_zero_connection, h]
  ring

/-- Extract a connection's matrix in a chosen base direction. -/
def connectionMatrix (Γ : Connection I V R) (i : I) : Matrix V V R :=
  fun a b => Γ i a b

/-- The curvature of a connection whose coefficients are constant
in the coordinate directions is exactly the matrix commutator. -/
theorem curvature_constant_eq_commutator (Γ : Connection I V R)
    (i j : I) (a b : V) :
    curvature Γ (fun _ _ _ _ => 0) i j a b =
      (connectionMatrix Γ i * connectionMatrix Γ j -
       connectionMatrix Γ j * connectionMatrix Γ i) a b := by
  classical
  simp [curvature, connectionMatrix, Matrix.mul_apply,
    Finset.sum_sub_distrib]

/-- A Lie bracket for matrices; no metric or coordinate choice needed. -/
def bracket (A B : Matrix V V R) : Matrix V V R := A*B-B*A

theorem bracket_skew (A B : Matrix V V R) : bracket A B = -bracket B A := by
  unfold bracket
  abel

/-- The matrix Jacobi identity: its algebraic version is the
foundation for the covariant Bianchi identity. -/
theorem bracket_jacobi (A B C : Matrix V V R) :
    bracket A (bracket B C) +
    bracket B (bracket C A) +
    bracket C (bracket A B) = 0 := by
  unfold bracket
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

/-- Contract the Riemann curvature to the Ricci tensor when
the base dimension and fibre rank are the same. In the index
convention of this file, Ric_{jl}=Σa Rᵃ_{laj}. -/
def ricci (Γ : Connection V V R) (dΓ : FirstJet V V R)
    (j l : V) : R :=
  ∑ a : V, curvature Γ dΓ a j a l

/-- A flat connection has vanishing Ricci contraction. -/
theorem ricci_zero_of_flat (Γ : Connection V V R)
    (dΓ : FirstJet V V R)
    (h : ∀ i j a b, curvature Γ dΓ i j a b = 0)
    (j l : V) : ricci Γ dΓ j l = 0 := by
  simp [ricci, h]

/-- Two simple constant 2×2 connection matrices have nonzero
commutator curvature. This prevents 'curvature=0' from being a
tautology of the definitions. -/
def exampleConnection (i a b : Fin 2) : ℚ :=
  if i = 0 then if a = 0 ∧ b = 1 then 1 else 0
  else if a = 1 ∧ b = 0 then 1 else 0

theorem example_curvature_nonzero :
    curvature exampleConnection (fun _ _ _ _ => 0)
      0 1 0 0 = (1 : ℚ) := by
  norm_num [curvature, exampleConnection, Fin.sum_univ_succ]

end FiniteConnectionCurvature
