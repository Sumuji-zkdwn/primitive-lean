/-!
# The generic ternary Chebyshev splitting field

For k ≥ 1, the roots of T_(3^k)(X) - t are the Joukowski images of the
3^k multiplicative radical labels. Existing files prove that these are roots,
are pairwise distinct, and that the first two recover the radical. This file
connects those facts to the actual splitting-field predicate over the
intermediate field C(t).

The case k = 0 is excluded: the polynomial then has degree one, while the
ambient rational-function extension has degree two, so C(X) is not its
splitting field.
-/

noncomputable section

namespace LinearInputChebyshevSplitting

open Polynomial
open IntermediateField

abbrev E := RatFunc ℂ

/-- The realized copy of C(t) inside C(X), with t = J(X^(3^k)). -/
def parameterField (k : ℕ) : IntermediateField ℂ E :=
  IntermediateField.adjoin ℂ
    ({LinearInputChebyshevTower.genericParameter (3 ^ k)} : Set E)

/-- The degree of C(X)/C(t), reusing the established 2m theorem. -/
theorem parameterField_finrank (k : ℕ) :
    Module.finrank (parameterField k) E = 2 * (3 ^ k) := by
  exact LinearInputChebyshevTower.finrank_genericParameter (3 ^ k)

/-- The element t, viewed as an element of the base intermediate field. -/
def parameter (k : ℕ) : parameterField k :=
  ⟨LinearInputChebyshevTower.genericParameter (3 ^ k),
    IntermediateField.subset_adjoin ℂ _ (by simp)⟩

/-- T_(3^k)(X) - t, now genuinely a polynomial over C(t). -/
def basePolynomial (k : ℕ) : Polynomial (parameterField k) :=
  LinearInputChebyshevDescent.chebyPoly (K := parameterField k) k -
    C (parameter k)

/-- The same polynomial after mapping its coefficients into C(X). -/
def targetPolynomial (k : ℕ) : Polynomial E :=
  LinearInputChebyshevDescent.chebyPoly (K := E) k -
    C (LinearInputChebyshevTower.genericParameter (3 ^ k))

/-- The ternary Chebyshev iterate commutes with coefficient embeddings. -/
theorem chebyPoly_map
    {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
    (f : K →+* L) (k : ℕ) :
    (LinearInputChebyshevDescent.chebyPoly (K := K) k).map f =
      LinearInputChebyshevDescent.chebyPoly (K := L) k := by
  induction k with
  | zero => simp [LinearInputChebyshevDescent.chebyPoly]
  | succ k ih =>
      simp [LinearInputChebyshevDescent.chebyPoly,
        LinearInputChebyshevDescent.cubicPoly, ih, map_ofNat]

/-- The field polynomial maps to the explicit polynomial in C(X). -/
theorem map_basePolynomial (k : ℕ) :
    (basePolynomial k).map (algebraMap (parameterField k) E) =
      targetPolynomial k := by
  rw [basePolynomial, Polynomial.map_sub,
    chebyPoly_map (algebraMap (parameterField k) E) k]
  simp [targetPolynomial, parameter]

/-- The established degree formula over ℂ transports through the injective
coefficient map ℂ → C(X). -/
theorem chebyPoly_natDegree_E (k : ℕ) :
    (LinearInputChebyshevDescent.chebyPoly (K := E) k).natDegree = 3 ^ k := by
  have hmap := Polynomial.natDegree_map_eq_of_injective
    (FaithfulSMul.algebraMap_injective ℂ E)
    (LinearInputChebyshevDescent.chebyPoly (K := ℂ) k)
  rw [chebyPoly_map (algebraMap ℂ E) k] at hmap
  exact hmap.trans (LinearInputChebyshevNext.chebyPoly_natDegree k)

/-- For k ≥ 1, the polynomial has degree 3^k. -/
theorem targetPolynomial_natDegree (k : ℕ) :
    (targetPolynomial k).natDegree = 3 ^ k := by
  unfold targetPolynomial
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by
    rw [Polynomial.natDegree_C, chebyPoly_natDegree_E]
    exact pow_pos (by norm_num : (0 : ℕ) < 3) k)]
  exact chebyPoly_natDegree_E k

/-- The base polynomial has the same degree, by injectivity of the field map. -/
theorem basePolynomial_natDegree (k : ℕ) :
    (basePolynomial k).natDegree = 3 ^ k := by
  have hdegree := Polynomial.natDegree_map_eq_of_injective
    (FaithfulSMul.algebraMap_injective (parameterField k) E) (basePolynomial k)
  rw [map_basePolynomial k] at hdegree
  rw [targetPolynomial_natDegree k] at hdegree
  exact hdegree.symm

theorem targetPolynomial_ne_zero (k : ℕ) :
    targetPolynomial k ≠ 0 := by
  intro h
  have hdegree := targetPolynomial_natDegree k
  rw [h] at hdegree
  have hpos : 0 < 3 ^ k := pow_pos (by norm_num : (0 : ℕ) < 3) k
  simp at hdegree
  omega

/-- Candidate root j in the ambient rational-function field. -/
def candidate (ζ : ℂ) (j : ℕ) : E :=
  LinearInputChebyshevDescent.rootCandidate (RatFunc.C ζ) RatFunc.X j

/-- A primitive root remains primitive under the injective constant embedding. -/
theorem primitiveRoot_C (m : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ m) :
    IsPrimitiveRoot (RatFunc.C ζ) m := by
  refine ⟨?_, ?_⟩
  · simpa only [map_pow, map_one] using
      congrArg (RatFunc.C : ℂ →+* E) hζ.pow_eq_one
  · intro l hl
    have hpow : RatFunc.C (ζ ^ l) = RatFunc.C (1 : ℂ) := by
      simpa only [map_pow, map_one] using hl
    apply hζ.dvd_of_pow_eq_one l
    exact RatFunc.C_injective hpow

/-- The already-proved Joukowski root identity, expressed for T_(3^k)-t. -/
theorem target_candidate_isRoot (k : ℕ) (ζ : ℂ) (j : ℕ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    IsRoot (targetPolynomial k) (candidate ζ j) := by
  have hζE : IsPrimitiveRoot (RatFunc.C ζ) (3 ^ k) :=
    primitiveRoot_C (3 ^ k) ζ hζ
  have hroot := LinearInputChebyshevDescent.candidate_isRoot
    k j (RatFunc.C ζ) RatFunc.X hζE RatFunc.X_ne_zero
  simpa [targetPolynomial, candidate,
    LinearInputChebyshevTower.genericParameter_eq_joukowski] using hroot

/-- The finite set of the m explicit radical-labelled roots. -/
noncomputable def candidateSet (m : ℕ) (ζ : ℂ) : Finset E := by
  classical
  exact (Finset.range m).image (candidate ζ)

/-- Existing pairwise-distinctness theorem gives exactly m candidates. -/
theorem candidateSet_card (m : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0) :
    (candidateSet m ζ).card = m := by
  classical
  unfold candidateSet
  calc
    ((Finset.range m).image (candidate ζ)).card = (Finset.range m).card :=
      Finset.card_image_iff.mpr (by
        intro j hj l hl heq
        by_contra hne
        exact (LinearInputChebyshevNext.generic_candidate_injective
          m ζ hζ hm j l (Finset.mem_range.mp hj) (Finset.mem_range.mp hl) hne) heq)
    _ = m := Finset.card_range m

/-- The mapped polynomial splits in C(X): m distinct candidates are roots of
a degree-m polynomial. -/
theorem targetPolynomial_splits (k : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    (targetPolynomial k).Splits := by
  classical
  let m := 3 ^ k
  have hm : m ≠ 0 := by positivity
  have hnonzero : targetPolynomial k ≠ 0 :=
    targetPolynomial_ne_zero k
  have hsubset : (candidateSet m ζ).val ⊆ (targetPolynomial k).roots := by
    intro x hx
    have hx' : x ∈ candidateSet m ζ := by simpa using hx
    rcases Finset.mem_image.mp hx' with ⟨j, hj, rfl⟩
    exact (Polynomial.mem_roots hnonzero).2 (target_candidate_isRoot k ζ j hζ)
  have hcardle : (candidateSet m ζ).card ≤ (targetPolynomial k).roots.card :=
    Multiset.card_le_card (Finset.val_le_iff_val_subset.mpr hsubset)
  have hrootsle := (targetPolynomial k).card_roots'
  rw [targetPolynomial_natDegree k] at hrootsle
  have hcandidates := candidateSet_card m ζ hζ hm
  have hrootcount : (targetPolynomial k).roots.card = m := by omega
  apply (Polynomial.splits_iff_card_roots).2
  rw [targetPolynomial_natDegree k]
  exact hrootcount

/-- Each explicit candidate belongs to the root set of the polynomial over C(t). -/
theorem candidate_mem_rootSet (k : ℕ) (ζ : ℂ) (j : ℕ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    candidate ζ j ∈ (basePolynomial k).rootSet E := by
  rw [Polynomial.mem_rootSet']
  constructor
  · rw [map_basePolynomial k]
    exact targetPolynomial_ne_zero k
  · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, map_basePolynomial k]
    exact target_candidate_isRoot k ζ j hζ

/-- The actual root set generates all of C(X): two adjacent roots recover X,
and C(X) is generated over any intermediate field containing C by X. -/
theorem rootSet_adjoin_eq_top (k : ℕ) (hk : 0 < k) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    IntermediateField.adjoin (parameterField k)
      ((basePolynomial k).rootSet E) = ⊤ := by
  let F := parameterField k
  let ζF : F := algebraMap ℂ F ζ
  have hζmap : algebraMap F E ζF = RatFunc.C ζ := by
    change algebraMap F E (algebraMap ℂ F ζ) = algebraMap ℂ E ζ
    rw [IsScalarTower.algebraMap_apply ℂ F E]
  have hζE : IsPrimitiveRoot (RatFunc.C ζ) (3 ^ k) :=
    primitiveRoot_C (3 ^ k) ζ hζ
  have hm2 : 2 < 3 ^ k := by
    cases k with
    | zero => omega
    | succ n =>
        rw [pow_succ]
        have hp : 0 < (3 : ℕ) ^ n := by positivity
        omega
  have hdiff : algebraMap F E ζF - (algebraMap F E ζF)⁻¹ ≠ 0 := by
    rw [hζmap]
    exact LinearInputChebyshevDescent.primitive_denom_ne_zero hζE hm2
  have hgen := LinearInputChebyshevDescent.two_candidates_generate
    ζF (RatFunc.X : E) RatFunc.X_ne_zero hdiff
  have hpair :
      IntermediateField.adjoin F
          ({candidate ζ 0, candidate ζ 1} : Set E) =
        IntermediateField.adjoin F ({(RatFunc.X : E)} : Set E) := by
    simpa only [candidate, hζmap] using hgen
  have hroot0 : candidate ζ 0 ∈ (basePolynomial k).rootSet E :=
    candidate_mem_rootSet k ζ 0 hζ
  have hroot1 : candidate ζ 1 ∈ (basePolynomial k).rootSet E :=
    candidate_mem_rootSet k ζ 1 hζ
  have hpair_le :
      IntermediateField.adjoin F
          ({candidate ζ 0, candidate ζ 1} : Set E) ≤
        IntermediateField.adjoin F ((basePolynomial k).rootSet E) := by
    refine (IntermediateField.adjoin_le_iff).2 ?_
    intro x hx
    have hx' : x = candidate ζ 0 ∨ x = candidate ζ 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    rcases hx' with h | h
    · subst x
      exact IntermediateField.subset_adjoin F _ hroot0
    · subst x
      exact IntermediateField.subset_adjoin F _ hroot1
  have hadjoinX :
      IntermediateField.adjoin F ({(RatFunc.X : E)} : Set E) = ⊤ := by
    simpa using RatFunc.IntermediateField.adjoin_X F
  apply le_antisymm
  · exact le_top
  · calc
      ⊤ = IntermediateField.adjoin F ({(RatFunc.X : E)} : Set E) :=
        hadjoinX.symm
      _ = IntermediateField.adjoin F
            ({candidate ζ 0, candidate ζ 1} : Set E) := hpair.symm
      _ ≤ IntermediateField.adjoin F ((basePolynomial k).rootSet E) :=
        hpair_le

/-- C(X), with its natural embedding of C(t), realizes the actual splitting
field of T_(3^k)(X)-t for k ≥ 1. -/
theorem rationalFunction_isSplittingField (k : ℕ) (hk : 0 < k) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    Polynomial.IsSplittingField (parameterField k) E (basePolynomial k) := by
  rw [isSplittingField_iff_intermediateField]
  constructor
  · rw [map_basePolynomial k]
    exact targetPolynomial_splits k ζ hζ
  · exact rootSet_adjoin_eq_top k hk ζ hζ

/-- Canonical algebra equivalence from the constructed model to Mathlib's
splitting-field object. -/
noncomputable def actualSplittingFieldEquiv (k : ℕ) (hk : 0 < k) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) :
    E ≃ₐ[parameterField k] (basePolynomial k).SplittingField := by
  letI : Polynomial.IsSplittingField (parameterField k) E (basePolynomial k) :=
    rationalFunction_isSplittingField k hk ζ hζ
  exact Polynomial.IsSplittingField.algEquiv E (basePolynomial k)

end LinearInputChebyshevSplitting
