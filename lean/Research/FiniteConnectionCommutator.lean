import Mathlib.Tactic
import Research.FiniteConnectionDerivation

/-!
# General finite-rank curvature from commutators of covariant derivatives

Let Dᵢ be commuting scalar derivations on a commutative ring R, and let
Γᵢ be an arbitrary square matrix of R-valued connection coefficients.
For a section s : V → R define ∇ᵢs = Dᵢs + Γᵢ *ᵥ s.

This file proves, for *arbitrary finite fibre V*,

  [∇ᵢ, ∇ⱼ] s = (Dᵢ Γⱼ - Dⱼ Γᵢ + ΓᵢΓⱼ - ΓⱼΓᵢ) *ᵥ s.

Crucially, Dᵢ Γⱼ is the entrywise action of actual Leibniz
derivations, not an independently stipulated jet table.
The final theorem identifies every entry with the generic finite
connection curvature from FiniteConnectionCurvature.

This establishes coordinate-free *rank* generality, but still works
in a chosen coordinate frame whose scalar derivations commute.
Connecting it to Mathlib's manifold CovariantDerivative, and proving
the metric's Levi-Civita symbols agree with Γ, remain separate tasks.
-/

namespace FiniteConnectionCommutator

open scoped Matrix
open FiniteConnectionDerivation
open FiniteConnectionCurvature

variable {I V R : Type*} [Fintype V] [CommRing R]

/-- Apply a scalar derivation to every component of a section. -/
def derivativeVec (P : CommutingPartials I R)
    (i : I) (s : V → R) : V → R := fun a => P.d i (s a)

/-- Apply a scalar derivation to every entry of a connection matrix. -/
def derivativeMatrix (P : CommutingPartials I R)
    (i : I) (A : Matrix V V R) : Matrix V V R :=
  fun a b => P.d i (A a b)

/-- Componentwise derivations preserve vector addition. -/
omit [Fintype V] in
theorem derivativeVec_add (P : CommutingPartials I R)
    (i : I) (s t : V → R) :
    derivativeVec P i (s+t) = derivativeVec P i s + derivativeVec P i t := by
  funext a
  simp [derivativeVec]

/-- The coordinate partials commute when applied to sections. -/
omit [Fintype V] in
theorem derivativeVec_commute (P : CommutingPartials I R)
    (i j : I) (s : V → R) :
    derivativeVec P i (derivativeVec P j s) =
      derivativeVec P j (derivativeVec P i s) := by
  funext a
  exact P.commute i j (s a)

/-- Entrywise derivative of matrix-vector multiplication, proved
from finite sums and the scalar Leibniz rule. -/
theorem derivativeVec_mulVec (P : CommutingPartials I R)
    (i : I) (A : Matrix V V R) (s : V → R) :
    derivativeVec P i (A *ᵥ s) =
      derivativeMatrix P i A *ᵥ s +
        A *ᵥ derivativeVec P i s := by
  classical
  funext a
  change P.d i (∑ b : V, A a b * s b) =
    (∑ b : V, P.d i (A a b) * s b) +
      (∑ b : V, A a b * P.d i (s b))
  rw [map_sum]
  simp_rw [P.leibniz]
  rw [Finset.sum_add_distrib]

/-- Connection acting on a section of a trivial finite-rank module. -/
def covariant (P : CommutingPartials I R)
    (Γ : I → Matrix V V R) (i : I) (s : V → R) : V → R :=
  derivativeVec P i s + Γ i *ᵥ s

/-- The actual matrix-valued field strength of this connection. -/
def matrixCurvature (P : CommutingPartials I R)
    (Γ : I → Matrix V V R) (i j : I) : Matrix V V R :=
  derivativeMatrix P i (Γ j) - derivativeMatrix P j (Γ i) +
    Γ i * Γ j - Γ j * Γ i

/-- Universal finite-rank covariant commutator, with actual scalar
Leibniz differentiation rather than a supplied derivative jet. -/
theorem covariant_commutator (P : CommutingPartials I R)
    (Γ : I → Matrix V V R) (i j : I) (s : V → R) :
    covariant P Γ i (covariant P Γ j s) -
      covariant P Γ j (covariant P Γ i s) =
        matrixCurvature P Γ i j *ᵥ s := by
  simp only [covariant, derivativeVec_add, derivativeVec_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_mulVec, matrixCurvature,
    Matrix.add_mulVec, Matrix.sub_mulVec]
  rw [derivativeVec_commute]
  abel

/-- Every matrix entry equals the generic coordinate curvature,
when its jet comes from the actual commuting derivations. -/
theorem matrix_curvature_eq_generic (P : CommutingPartials I R)
    (Γ : I → Matrix V V R) (i j : I) (a b : V) :
    matrixCurvature P Γ i j a b =
      curvature (fun k c d => Γ k c d)
        (fun k l c d => P.d k (Γ l c d)) i j a b := by
  classical
  simp only [matrixCurvature, curvature, derivativeMatrix,
    Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
    Finset.sum_sub_distrib]
  ring

/-- Final coordinate-free-in-rank bridge: the true commutator acts on
the section by the entries of the generic Riemann curvature formula. -/
theorem covariant_commutator_eq_curvature (P : CommutingPartials I R)
    (Γ : I → Matrix V V R) (i j : I) (s : V → R) (a : V) :
    (covariant P Γ i (covariant P Γ j s) -
      covariant P Γ j (covariant P Γ i s)) a =
      ∑ b : V, curvature (fun k c d => Γ k c d)
        (fun k l c d => P.d k (Γ l c d)) i j a b * s b := by
  rw [covariant_commutator]
  classical
  simp only [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [matrix_curvature_eq_generic]

end FiniteConnectionCommutator
