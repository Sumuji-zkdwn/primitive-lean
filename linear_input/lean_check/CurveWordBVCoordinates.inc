/-!
Transfer of the geometric height condition between normed coordinates.
The independent tree-like predicate is preserved by a continuous linear
equivalence, with the height rescaled by its actual operator norm.
-/

noncomputable section
namespace LinearInputCurveWordBVCoordinates

open Set
open LinearInputCurveWordTreeLike

theorem treeLike_linearEquiv_iff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (γ : ℝ → E) (a b : ℝ) :
    TreeLike (e ∘ γ) a b ↔ TreeLike γ a b := by
  constructor
  · intro h
    have he := h.lipschitz_map e.symm.toContinuousLinearMap.lipschitzWith
    change TreeLike (fun x => e.symm (e (γ x))) a b at he
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using! he
  · intro h
    exact h.lipschitz_map e.toContinuousLinearMap.lipschitzWith

theorem coordinate_boundedVariation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (e : E ≃L[ℝ] (ι → ℝ))
    {γ : ℝ → E} {a b : ℝ} (hγ : BoundedVariationOn γ (Icc a b)) :
    BoundedVariationOn (e ∘ γ) (Icc a b) := e.toContinuousLinearMap.lipschitzWith.comp_boundedVariationOn hγ

theorem coordinate_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (e : E ≃L[ℝ] (ι → ℝ))
    {γ : ℝ → E} {a b : ℝ} (hc : ContinuousOn γ (Icc a b)) :
    ContinuousOn (e ∘ γ) (Icc a b) := e.continuous.comp_continuousOn hc

open LinearInputCurveWordBVCanonical LinearInputCurveWordFormalSeries

/-- The actual canonical Stieltjes signature in the specified normed
coordinates. The coordinate map is explicit in the definition. -/
def signatureInCoordinates {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (e : E ≃L[ℝ] (ι → ℝ))
    (γ : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) : Series ι :=
  pathSignature (e ∘ γ) hab (coordinate_boundedVariation e hγ) (coordinate_continuousOn e hc)

theorem signatureInCoordinates_eq_unit_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (e : E ≃L[ℝ] (ι → ℝ))
    (γ : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    signatureInCoordinates e γ hab hγ hc = unitSeries ↔ TreeLike γ a b := by
  constructor
  · intro hzero
    exact (treeLike_linearEquiv_iff e γ a b).mp
      (LinearInputCurveWordBVHamblyLyons.treeLike_of_pathSignature_eq_unit (e ∘ γ) hab
        (coordinate_boundedVariation e hγ) (coordinate_continuousOn e hc) hzero)
  · intro htree
    exact LinearInputCurveWordTreeLimit.treeLike_pathSignature_eq_unit (e ∘ γ) hab
      (coordinate_boundedVariation e hγ) ((treeLike_linearEquiv_iff e γ a b).mpr htree)

/-- Triviality of the full signature is independent of the finite normed
coordinate equivalence, even though its individual tensor coordinates change. -/
theorem signature_triviality_coordinate_independent {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : E ≃L[ℝ] (ι → ℝ)) (f : E ≃L[ℝ] (κ → ℝ))
    (γ : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    signatureInCoordinates e γ hab hγ hc = unitSeries ↔
      signatureInCoordinates f γ hab hγ hc = unitSeries :=
  (signatureInCoordinates_eq_unit_iff e γ hab hγ hc).trans
    (signatureInCoordinates_eq_unit_iff f γ hab hγ hc).symm

def finiteDimensionalSignature {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (γ : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    Series (Fin (Module.finrank ℝ E)) :=
  signatureInCoordinates (Module.finBasis ℝ E).equivFunL γ hab hγ hc

/-- The theorem for every finite-dimensional real normed space, obtained
from an actual finite basis and explicit operator-norm height transport. -/
theorem finiteDimensionalSignature_eq_unit_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (γ : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    finiteDimensionalSignature γ hab hγ hc = unitSeries ↔ TreeLike γ a b :=
  signatureInCoordinates_eq_unit_iff (Module.finBasis ℝ E).equivFunL γ hab hγ hc

end LinearInputCurveWordBVCoordinates
