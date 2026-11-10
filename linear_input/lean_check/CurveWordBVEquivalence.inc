/-!
Equality of actual continuous-BV signatures and geometric tree equivalence.
The geometric criterion uses the explicitly joined forward/reversed curve.
-/

noncomputable section
namespace LinearInputCurveWordBVEquivalence

open Set
open LinearInputCurveWordFormalSeries LinearInputCurveWordBVCanonical
open LinearInputCurveWordBVSubinterval LinearInputCurveWordBVPathOperations
open LinearInputCurveWordTreeLike LinearInputCurveWordTreeLimit

theorem pathSignature_eq_unit_iff_nonempty_zero {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    pathSignature γ hab hγ hc = unitSeries ↔
      ∀ w : List ι, w ≠ [] → pathSignature γ hab hγ hc w = 0 := by
  constructor
  · intro he w hw
    rw [he]
    cases w <;> simp_all [unitSeries]
  · intro hz
    funext w
    cases w with
    | nil => rfl
    | cons i w => exact hz (i :: w) (by simp)

/-- First-level coefficients retain the complete displacement. -/
theorem displacement_eq_of_pathSignature_eq {ι : Type*} [Fintype ι]
    (γ η : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hcγ : ContinuousOn γ (Icc a b))
    (hη : BoundedVariationOn η (Icc a b)) (hcη : ContinuousOn η (Icc a b))
    (hsig : pathSignature γ hab hγ hcγ = pathSignature η hab hη hcη) :
    γ b - γ a = η b - η a := by
  funext i
  have he := congrFun hsig [i]
  rw [show pathSignature γ hab hγ hcγ [i] = γ b i - γ a i from
      curveSignature_singleton _ _ _ _ i,
    show pathSignature η hab hη hcη [i] = η b i - η a i from
      curveSignature_singleton _ _ _ _ i] at he
  exact he

theorem endpoint_eq_of_pathSignature_eq {ι : Type*} [Fintype ι]
    (γ η : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hcγ : ContinuousOn γ (Icc a b))
    (hη : BoundedVariationOn η (Icc a b)) (hcη : ContinuousOn η (Icc a b))
    (hstart : γ a = η a)
    (hsig : pathSignature γ hab hγ hcγ = pathSignature η hab hη hcη) : γ b = η b := by
  have he := displacement_eq_of_pathSignature_eq γ η hab hγ hcγ hη hcη hsig
  rw [hstart] at he
  funext i
  have hi := congrFun he i
  change γ b i - η a i = η b i - η a i at hi
  linarith

open LinearInputCurveWordBVHamblyLyons

/-- The full geometric kernel theorem for actual continuous-BV signatures,
including degenerate compact intervals. -/
theorem pathSignature_eq_unit_iff_treeLike {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    pathSignature γ hab hγ hc = unitSeries ↔ TreeLike γ a b :=
  ⟨treeLike_of_pathSignature_eq_unit γ hab hγ hc,
    fun htree => treeLike_pathSignature_eq_unit γ hab hγ htree⟩

theorem nonempty_signature_zero_iff_treeLike {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    (∀ w : List ι, w ≠ [] → pathSignature γ hab hγ hc w = 0) ↔ TreeLike γ a b :=
  (pathSignature_eq_unit_iff_nonempty_zero γ hab hγ hc).symm.trans
    (pathSignature_eq_unit_iff_treeLike γ hab hγ hc)

/-- Two curves ending at the same physical point have equal actual
signatures exactly when their forward/reverse concatenation is tree-like. -/
theorem pathSignature_eq_iff_join_reverse_treeLike {ι : Type*} [Fintype ι]
    (γ η : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b) (hend : γ b = η b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hcγ : ContinuousOn γ (Icc a b))
    (hη : BoundedVariationOn η (Icc a b)) (hcη : ContinuousOn η (Icc a b)) :
    pathSignature γ hab hγ hcγ = pathSignature η hab hη hcη ↔
      TreeLike (joinCurve b γ (mirrorPath η b)) a (2 * b - a) :=
  (pathSignature_eq_iff_join_reverse_unit γ η hab hend hγ hcγ hη hcη).trans
    (pathSignature_eq_unit_iff_treeLike (joinCurve b γ (mirrorPath η b)) (by linarith)
      (joinCurve_boundedVariation hab (by linarith) (hend.trans (mirrorPath_matches η b))
        hγ (mirrorPath_boundedVariation hη))
      (joinCurve_continuousOn hab (by linarith) (hend.trans (mirrorPath_matches η b))
        hcγ (mirrorPath_continuousOn hcη)))

/-- For curves sharing a starting point, endpoint matching follows from
signature equality and is not an additional assumption in this criterion. -/
theorem based_pathSignature_eq_iff_tree_equivalent {ι : Type*} [Fintype ι]
    (γ η : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hcγ : ContinuousOn γ (Icc a b))
    (hη : BoundedVariationOn η (Icc a b)) (hcη : ContinuousOn η (Icc a b))
    (hstart : γ a = η a) :
    pathSignature γ hab hγ hcγ = pathSignature η hab hη hcη ↔
      γ b = η b ∧ TreeLike (joinCurve b γ (mirrorPath η b)) a (2 * b - a) := by
  constructor
  · intro hsig
    have hend := endpoint_eq_of_pathSignature_eq γ η hab hγ hcγ hη hcη hstart hsig
    exact ⟨hend, (pathSignature_eq_iff_join_reverse_treeLike γ η hab hend hγ hcγ hη hcη).mp hsig⟩
  · rintro ⟨hend, htree⟩
    exact (pathSignature_eq_iff_join_reverse_treeLike γ η hab hend hγ hcγ hη hcη).mpr htree

end LinearInputCurveWordBVEquivalence
