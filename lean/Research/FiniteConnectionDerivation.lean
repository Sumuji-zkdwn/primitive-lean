import Mathlib.Tactic
import Research.FiniteConnectionCurvature

/-!
# Rank-one curvature as a commutator of genuine derivation operators

Unlike the previous finite coefficient-jet file, this module *does not*
treat derivatives of connection coefficients as independent symbols.
It accepts a family of commuting derivations of a commutative ring,
expressed as AddMonoidHom maps satisfying the Leibniz rule.

For ∇ᵢ s := Dᵢ s + Γᵢ s, the operator commutator is

  (∇ᵢ∇ⱼ - ∇ⱼ∇ᵢ)s = (Dᵢ Γⱼ - Dⱼ Γᵢ)s,

and that coefficient is exactly the rank-one specialization of
FiniteConnectionCurvature.curvature. These are universal algebraic
statements for commuting derivations, not axioms asserting a
particular manifold has such coordinate derivatives.

The higher-rank covariant commutator and the bridge to Mathlib's
manifold CovariantDerivative remain separate goals.
-/

namespace FiniteConnectionDerivation

variable {I R : Type*} [CommRing R]

/-- A commuting family of scalar derivations, with its differential
properties in the structure rather than added as global axioms. -/
structure CommutingPartials (I R : Type*) [CommRing R] where
  d : I → R →+ R
  leibniz : ∀ i (x y : R),
    d i (x*y) = d i x*y + x*d i y
  commute : ∀ i j (x : R), d i (d j x) = d j (d i x)

/-- Covariant derivative of a section of a rank-one trivial bundle. -/
def rankOneCovariant (P : CommutingPartials I R)
    (Γ : I → R) (i : I) (s : R) : R :=
  P.d i s + Γ i * s

/-- ∇ᵢ(fs)=Dᵢ(f)s+f∇ᵢ(s), the connection Leibniz law. -/
theorem rankOne_leibniz (P : CommutingPartials I R)
    (Γ : I → R) (i : I) (f s : R) :
    rankOneCovariant P Γ i (f*s) =
      P.d i f*s + f*rankOneCovariant P Γ i s := by
  change P.d i (f*s)+Γ i*(f*s) =
    P.d i f*s+f*(P.d i s+Γ i*s)
  rw [P.leibniz]
  ring

/-- Exact commutator formula from *actual* Leibniz derivations. -/
theorem rankOne_commutator (P : CommutingPartials I R)
    (Γ : I → R) (i j : I) (s : R) :
    rankOneCovariant P Γ i (rankOneCovariant P Γ j s) -
    rankOneCovariant P Γ j (rankOneCovariant P Γ i s) =
      (P.d i (Γ j) - P.d j (Γ i)) * s := by
  change (P.d i (P.d j s + Γ j*s) +
    Γ i*(P.d j s + Γ j*s)) -
    (P.d j (P.d i s + Γ i*s) +
    Γ j*(P.d i s + Γ i*s)) = _
  rw [map_add, map_add]
  rw [P.leibniz i (Γ j) s, P.leibniz j (Γ i) s]
  rw [P.commute i j s]
  ring

/-- The rank-one specialization of the general Riemann curvature
formula equals the coefficient from the operator commutator. -/
theorem rankOne_generic_curvature (P : CommutingPartials I R)
    (Γ : I → R) (i j : I) :
    FiniteConnectionCurvature.curvature
      (fun k (_ _ : Fin 1) => Γ k)
      (fun k l (_ _ : Fin 1) => P.d k (Γ l))
      i j 0 0 =
      P.d i (Γ j) - P.d j (Γ i) := by
  simp [FiniteConnectionCurvature.curvature, Fin.sum_univ_succ]
  ring

/-- Reusable operator-curvature bridge, with no manually supplied
derivative table and no special physical field ansatz. -/
theorem rankOne_commutator_eq_curvature (P : CommutingPartials I R)
    (Γ : I → R) (i j : I) (s : R) :
    rankOneCovariant P Γ i (rankOneCovariant P Γ j s) -
    rankOneCovariant P Γ j (rankOneCovariant P Γ i s) =
      FiniteConnectionCurvature.curvature
        (fun k (_ _ : Fin 1) => Γ k)
        (fun k l (_ _ : Fin 1) => P.d k (Γ l))
        i j 0 0 * s := by
  rw [rankOne_commutator, rankOne_generic_curvature]

end FiniteConnectionDerivation
