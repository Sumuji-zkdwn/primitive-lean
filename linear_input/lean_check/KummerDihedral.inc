/-!
# Kummer splitting fields and the dihedral label action

This is a second, additive bridge after GaloisChebyshev.inc.
Unlike the earlier root-candidate calculation, the Kummer part below uses actual
extension fields and their algebra automorphism groups.

Important distinction: Gal(Split(X^n-a)/K) is cyclic when K already contains
a primitive n-th root of unity.  The *dihedral* Galois group relevant to
generic Chebyshev polynomials is a different extension, namely the quadratic
descent from K(z) over K(z^n + z^(-n)), with its normal cyclic Kummer subgroup.
The following dihedral label action does not, by itself, prove that descent.

Everything here is explicit; no general dihedral Galois isomorphism is claimed.
-/

noncomputable section
open Polynomial

namespace LinearInputKummerDihedral

/-- The binomial that generates the Kummer splitting extension. -/
def kummerPoly {K : Type*} [Field K] (n : ℕ) (a : K) : Polynomial K :=
  X ^ n - C a

/-- The actual splitting field of X^n-a. -/
abbrev kummerField {K : Type*} [Field K] (n : ℕ) (a : K) : Type _ :=
  (kummerPoly n a).SplittingField

/-- A concrete adjoining-root algebra (a field once the binomial is irreducible). -/
abbrev kummerAdjoinRoot {K : Type*} [Field K] (n : ℕ) (a : K) : Type _ :=
  AdjoinRoot (kummerPoly n a)

/-- The field of the Kummer root and the splitting field agree as splitting
extensions when the binomial is irreducible and primitive roots exist. -/
theorem kummerAdjoinRoot_isSplittingField {K : Type*} [Field K]
    {n : ℕ} {a : K} [Fact (Irreducible (kummerPoly n a))]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    Polynomial.IsSplittingField K (kummerAdjoinRoot n a) (kummerPoly n a) := by
  exact isSplittingField_AdjoinRoot_X_pow_sub_C
    (show (primitiveRoots n K).Nonempty from ⟨ζ, hζ⟩) (Fact.out : Irreducible (kummerPoly n a))

/-- Genuine field-automorphism group: Gal(Split(X^n-a)/K) ≃ Z/nZ,
given an irreducible binomial and a primitive root in K. -/
noncomputable def kummerGaloisEquiv {K : Type*} [Field K]
    {n : ℕ} [NeZero n] {a ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (hirr : Irreducible (kummerPoly n a)) :
    (kummerPoly n a).Gal ≃* Multiplicative (ZMod n) := by
  exact autEquivZmod hirr (kummerField n a) hζ

/-- A Kummer extension with primitive roots in the base is Galois. -/
theorem kummer_isGalois {K : Type*} [Field K]
    {n : ℕ} {a ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (hirr : Irreducible (kummerPoly n a)) :
    IsGalois K (kummerField n a) := by
  exact isGalois_of_isSplittingField_X_pow_sub_C
    (show (primitiveRoots n K).Nonempty from ⟨ζ, hζ⟩) hirr (kummerField n a)

/-- The degree of this actual extension equals n. -/
theorem kummer_finrank {K : Type*} [Field K]
    {n : ℕ} {a ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (hirr : Irreducible (kummerPoly n a)) :
    Module.finrank K (kummerField n a) = n := by
  exact finrank_of_isSplittingField_X_pow_sub_C
    (show (primitiveRoots n K).Nonempty from ⟨ζ, hζ⟩) hirr (kummerField n a)

/-- The action on root indices by rotations and reflections. The sign
convention matches mathlib's DihedralGroup.r/sr multiplication rules. -/
def labelAction (n : ℕ) : DihedralGroup n → ZMod n → ZMod n
  | .r a, j => j + a
  | .sr a, j => -j - a

theorem labelAction_rotation (n : ℕ) (a j : ZMod n) :
    labelAction n (.r a) j = j + a := rfl

theorem labelAction_reflection (n : ℕ) (a j : ZMod n) :
    labelAction n (.sr a) j = -j - a := rfl

theorem labelAction_one (n : ℕ) (j : ZMod n) :
    labelAction n 1 j = j := by
  simp [DihedralGroup.one_def, labelAction]

theorem labelAction_mul (n : ℕ) (g h : DihedralGroup n) (j : ZMod n) :
    labelAction n (g * h) j = labelAction n g (labelAction n h j) := by
  cases g with
  | r a =>
    cases h with
    | r b => simp [labelAction]; ring
    | sr b => simp [labelAction]; ring
  | sr a =>
    cases h with
    | r b => simp [labelAction]; ring
    | sr b => simp [labelAction]; ring

/-- The reflection has period two as a permutation of Kummer labels. -/
theorem labelAction_reflection_involutive (n : ℕ) (a j : ZMod n) :
    labelAction n (.sr a) (labelAction n (.sr a) j) = j := by
  simp [labelAction]
  ring

/-- The rotation subgroup is the cyclic group of size n; the dihedral
permutation structure has exactly 2n group elements for finite n. -/
theorem dihedral_nat_card (n : ℕ) :
    Nat.card (DihedralGroup n) = 2 * n :=
  DihedralGroup.nat_card

end LinearInputKummerDihedral
