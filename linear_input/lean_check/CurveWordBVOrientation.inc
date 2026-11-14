/-! Actual canonical signature transport under increasing or decreasing time changes. -/

noncomputable section
namespace LinearInputCurveWordBVOrientation
open Set Real MeasureTheory

open LinearInputCurveWordBVCanonical LinearInputCurveWordBVPathOperations
open LinearInputCurveWordStieltjes LinearInputCurveWordFormalSeries

theorem oriented_comp_boundedVariation {E : Type*} [PseudoEMetricSpace E]
    {γ : ℝ → E} {φ : ℝ → ℝ} {a b c d : ℝ}
    (hγ : BoundedVariationOn γ (Icc a b))
    (ho : MonotoneOn φ (Icc c d) ∨ AntitoneOn φ (Icc c d))
    (hmap : MapsTo φ (Icc c d) (Icc a b)) :
    BoundedVariationOn (γ ∘ φ) (Icc c d) := by
  apply ne_top_of_le_ne_top hγ
  rcases ho with hm | hm
  · exact eVariationOn.comp_le_of_monotoneOn γ φ hm hmap
  · exact eVariationOn.comp_le_of_antitoneOn γ φ hm hmap

/-- The actual canonical signature respects a time change in either direction.
The decreasing case is proved from actual time reversal and Chen inverses. -/
theorem pathSignature_oriented_reparametrize {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    {φ : ℝ → ℝ} {a b c d : ℝ} (hcd : c ≤ d)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hrep : ∀ i, RepresentsOn (p i) (m i) (fun t => γ t i) a b)
    (ho : MonotoneOn φ (Icc c d) ∨ AntitoneOn φ (Icc c d))
    (hφ : ContinuousOn φ (Icc c d)) (hmap : MapsTo φ (Icc c d) (Icc a b)) :
    pathSignature (γ ∘ φ) hcd (oriented_comp_boundedVariation hγ ho hmap)
      (hc.comp hφ hmap) = stieltjesSignature p m (φ c) (φ d) := by
  have hmono : ∀ {ψ : ℝ → ℝ}, ∀ hψmono : MonotoneOn ψ (Icc c d),
      ∀ hψcont : ContinuousOn ψ (Icc c d), ∀ hmaps : MapsTo ψ (Icc c d) (Icc a b),
      pathSignature (γ ∘ ψ) hcd
        (oriented_comp_boundedVariation hγ (Or.inl hψmono) hmaps) (hc.comp hψcont hmaps) =
          stieltjesSignature p m (ψ c) (ψ d) := by
    intro ψ hψmono hψcont hψmap
    have hψc := hψmap (left_mem_Icc.mpr hcd)
    have hψd := hψmap (right_mem_Icc.mpr hcd)
    have hψcd := hψmono (left_mem_Icc.mpr hcd) (right_mem_Icc.mpr hcd) hcd
    have hsub : Icc (ψ c) (ψ d) ⊆ Icc a b := Icc_subset_Icc hψc.1 hψd.2
    rw [pathSignature_reparametrize_endpoints γ hψcd hcd hψmono hψcont rfl rfl
      (hγ.mono hsub) (hc.mono hsub)]
    funext w
    exact pathSignature_eq_representation γ hψcd _ _ p m hp hm
      (fun i x hx y hy => hrep i x (hsub hx) y (hsub hy)) w
  rcases ho with ho | ho
  · exact hmono ho hφ hmap
  · let ψ : ℝ → ℝ := fun t => φ (c + d - t)
    have hrmap : MapsTo (fun t : ℝ => c + d - t) (Icc c d) (Icc c d) := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have hψmono : MonotoneOn ψ (Icc c d) := by
      intro x hx y hy hxy
      exact ho (hrmap hy) (hrmap hx) (sub_le_sub_left hxy _)
    have hψcont : ContinuousOn ψ (Icc c d) :=
      hφ.comp (continuous_const.sub continuous_id).continuousOn hrmap
    have hψmap : MapsTo ψ (Icc c d) (Icc a b) := fun _ ht => hmap (hrmap ht)
    have heψ := hmono hψmono hψcont hψmap
    have hec : ψ c = φ d := by dsimp [ψ]; congr 1; ring
    have hed : ψ d = φ c := by dsimp [ψ]; congr 1; ring
    have hreverse : pathSignature (reversePath (γ ∘ φ) c d) hcd
        (reversePath_boundedVariation (oriented_comp_boundedVariation hγ (Or.inr ho) hmap))
        (reversePath_continuousOn (hc.comp hφ hmap)) = stieltjesSignature p m (φ d) (φ c) := by
      simpa only [hec, hed] using! heψ
    have hXY := pathSignature_product_reverse (γ ∘ φ) hcd
      (oriented_comp_boundedVariation hγ (Or.inr ho) hmap) (hc.comp hφ hmap)
    rw [hreverse] at hXY
    have hYZ := (stieltjesSignature_inverse p m hp hm (φ d) (φ c)).1
    calc
      _ = product (pathSignature (γ ∘ φ) hcd _ _) unitSeries := (product_unit_right _).symm
      _ = product (pathSignature (γ ∘ φ) hcd _ _)
          (product (stieltjesSignature p m (φ d) (φ c)) (stieltjesSignature p m (φ c) (φ d))) := by rw [hYZ]
      _ = product (product (pathSignature (γ ∘ φ) hcd _ _) (stieltjesSignature p m (φ d) (φ c)))
          (stieltjesSignature p m (φ c) (φ d)) := (product_assoc _ _ _).symm
      _ = _ := by rw [hXY, product_unit_left]

end LinearInputCurveWordBVOrientation
