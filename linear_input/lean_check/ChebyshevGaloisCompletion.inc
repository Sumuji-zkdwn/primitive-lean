/-!
# Full dihedral Galois group of the generic ternary Chebyshev polynomial

For k ≥ 1, the preceding supplements identify RatFunc ℂ with the genuine
splitting field of T_(3^k)(X)-t over ℂ(t), construct a faithful action of
DihedralGroup (3^k) by field automorphisms, and compute the extension degree
as 2 * 3^k.

The cardinal bound for algebra homomorphisms shows that this faithful
representation exhausts *all* field automorphisms. We transport the result
to Mathlib's actual SplittingField and obtain an unconditional (in k ≥ 1)
Galois group equivalence; the primitive root ζ exists in ℂ and is supplied
as a parameter here to keep the particular generator explicit.
-/

noncomputable section

namespace LinearInputChebyshevGaloisCompletion

open Polynomial
open LinearInputChebyshevAutomorphisms

/-- A faithful dihedral subgroup of order 2*3^k already fills the
entire automorphism group: each automorphism is an algebra homomorphism,
and there are at most [C(X):C(t)] = 2*3^k of these. -/
theorem dihedralRepresentation_surjective (k : ℕ) (hk : 0 < k)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    Function.Surjective (dihedralRepresentation k ζ hζ) := by
  classical
  letI : Polynomial.IsSplittingField (Base k) E (LinearInputChebyshevSplitting.basePolynomial k) :=
    LinearInputChebyshevSplitting.rationalFunction_isSplittingField k hk ζ hζ
  letI : FiniteDimensional (Base k) E :=
    Polynomial.IsSplittingField.finiteDimensional E (LinearInputChebyshevSplitting.basePolynomial k)
  letI : Finite (E →ₐ[Base k] E) := inferInstance
  letI : Finite (Aut k) :=
    Finite.of_injective
      (fun σ : Aut k => (σ : E →ₐ[Base k] E))
      AlgEquiv.coe_algHom_injective
  have h_bound : Nat.card (Aut k) ≤ 2 * (3 ^ k) := by
    calc
      Nat.card (Aut k) ≤ Nat.card (E →ₐ[Base k] E) :=
        Nat.card_le_card_of_injective
          (fun σ : Aut k => (σ : E →ₐ[Base k] E))
          AlgEquiv.coe_algHom_injective
      _ ≤ Module.finrank (Base k) E :=
        card_algHom_le_finrank (Base k) E E
      _ = 2 * (3 ^ k) := LinearInputChebyshevSplitting.parameterField_finrank k
  have h_card : Nat.card (Aut k) ≤ Nat.card (DihedralGroup (3 ^ k)) := by
    simpa only [DihedralGroup.nat_card] using h_bound
  exact (Function.Injective.bijective_of_nat_card_le
    (dihedralRepresentation_injective k ζ hζ) h_card).2

/-- The faithful dihedral representation is a group *isomorphism*. -/
noncomputable def dihedralModelEquiv (k : ℕ) (hk : 0 < k)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    DihedralGroup (3 ^ k) ≃* Aut k :=
  MulEquiv.ofBijective (dihedralRepresentation k ζ hζ)
    ⟨dihedralRepresentation_injective k ζ hζ,
      dihedralRepresentation_surjective k hk ζ hζ⟩

/-- Genuine Galois group equivalence for the actual splitting-field object
of T_(3^k)(X)-t over the intermediate field C(t), k≥1. -/
noncomputable def dihedralSplittingFieldEquiv (k : ℕ) (hk : 0 < k)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    DihedralGroup (3 ^ k) ≃*
      ((LinearInputChebyshevSplitting.basePolynomial k).SplittingField ≃ₐ[Base k]
        (LinearInputChebyshevSplitting.basePolynomial k).SplittingField) :=
  (dihedralModelEquiv k hk ζ hζ).trans
    (LinearInputChebyshevSplitting.actualSplittingFieldEquiv k hk ζ hζ).autCongr

end LinearInputChebyshevGaloisCompletion
