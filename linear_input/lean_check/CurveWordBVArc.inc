/-!
Actual arc-length signature lifts of reduced BV representatives. Every
constructed arc is the signature lift of a constructed coordinate curve;
no arbitrary topological arc is treated as an original time subinterval.
-/

noncomputable section
namespace LinearInputCurveWordBVArc
open Set MeasureTheory
open scoped Topology BoundedContinuousFunction
open LinearInputCurveWordBoundedVariation LinearInputCurveWordBVCanonical
open LinearInputCurveWordBVCompactness LinearInputCurveWordBVReduced
open LinearInputCurveWordBVLoopErase LinearInputCurveWordBVPathOperations
open LinearInputCurveWordFormalSeries

theorem variationClock_eq_of_constant {E : Type*} [MetricSpace E]
    {γ : ℝ → E} {L s t : ℝ} (hL : 0 ≤ L)
    (hγ : BoundedVariationOn γ (Icc 0 L)) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L)
    (hc : ∀ u ∈ Icc s t, γ u = γ s) :
    variationClock γ 0 L s = variationClock γ 0 L t := by
  have hv : eVariationOn γ (Icc s t) = 0 := by
    apply (eVariationOn.eq_zero_iff γ).mpr
    intro u hu v hv
    rw [hc u hu, hc v hv, edist_self]
  have hadd := variationOnFromTo.add hγ.locallyBoundedVariationOn
    (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL⟩)
    (show s ∈ Icc 0 L from ⟨hs, hst.trans ht⟩)
    (show t ∈ Icc 0 L from ⟨hs.trans hst, ht⟩)
  rw [variationOnFromTo.eq_of_le _ _ hst,
    inter_eq_right.mpr (Icc_subset_Icc hs ht), hv, ENNReal.toReal_zero, add_zero] at hadd
  exact hadd

/-- The arc-length factorization preserves every actual prefix signature,
not only the signature at the terminal time. -/
theorem lipSignature_arcLength_prefix {ι : Type*} [Fintype ι]
    (γ G : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) (hG : LipschitzWith 1 G)
    {L : ℝ} (hL : 0 ≤ L)
    (hfac : EqOn γ (G ∘ variationClock γ 0 L) (Icc 0 L))
    {t : ℝ} (ht : t ∈ Icc 0 L) :
    lipSignature γ hγ 0 t ht.1 =
      lipSignature G hG 0 (variationClock γ 0 L t)
        (variationClock_mem hL (lipschitz_boundedVariation γ hγ 0 L) ht).1 := by
  have hBV := lipschitz_boundedVariation γ hγ 0 L
  have hsub : Icc 0 t ⊆ Icc 0 L := Icc_subset_Icc le_rfl ht.2
  have hm := (variationClock_monotoneOn hL hBV).mono hsub
  have hc := (variation_clock_continuousOn hBV hγ.continuous.continuousOn
    (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL⟩)).mono hsub
  have hr := (variationClock_mem hL hBV ht).1
  have he := pathSignature_reparametrize_endpoints G hr ht.1 hm hc
    (variationClock_initial γ 0 L) rfl
    (lipschitz_boundedVariation G hG 0 (variationClock γ 0 L t)) hG.continuous.continuousOn
  funext w
  calc
    _ = pathSignature (G ∘ variationClock γ 0 L) ht.1 _ _ w :=
      pathSignature_congr ht.1 _ _ _ _ (hfac.mono hsub) w
    _ = _ := congrArg (fun S : List ι → ℝ => S w) he

/-- If the actual reduced curve is constant on each signature-fiber interval,
then the actual arc-length curve has an injective based signature lift. -/
theorem arcLength_based_lift_injective {ι : Type*} [Fintype ι]
    (γ G : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) (hG : LipschitzWith 1 G)
    {L : ℝ} (hL : 0 ≤ L) (P : Series ι)
    (hfac : EqOn γ (G ∘ variationClock γ 0 L) (Icc 0 L))
    (hfiber : ∀ s t : ℝ, (hs : 0 ≤ s) → (hst : s ≤ t) → (ht : t ≤ L) →
      product P (lipSignature γ hγ 0 s hs) =
        product P (lipSignature γ hγ 0 t (hs.trans hst)) →
      ∀ u ∈ Icc s t, γ u = γ s) :
    Function.Injective (fun r : Icc 0 (variationLength γ 0 L) =>
      product P (lipSignature G hG 0 r.val r.property.1)) := by
  intro r q he
  have hBV := lipschitz_boundedVariation γ hγ 0 L
  have hsur := variationParameter_surjective hL hBV hγ.continuous.continuousOn
  obtain ⟨s, hs⟩ := hsur r
  obtain ⟨t, ht⟩ := hsur q
  have hsr : variationClock γ 0 L s.val = r.val := congrArg Subtype.val hs
  have htq : variationClock γ 0 L t.val = q.val := congrArg Subtype.val ht
  have hsSig := lipSignature_arcLength_prefix γ G hγ hG hL hfac s.property
  have htSig := lipSignature_arcLength_prefix γ G hγ hG hL hfac t.property
  have hstSig : product P (lipSignature γ hγ 0 s.val s.property.1) =
      product P (lipSignature γ hγ 0 t.val t.property.1) := by
    have hs' := hsSig.trans (lipSignature_endpoint_congr G hG _ r.property.1 hsr)
    have ht' := htSig.trans (lipSignature_endpoint_congr G hG _ q.property.1 htq)
    rw [hs', ht']
    exact he
  have hclock : variationClock γ 0 L s.val = variationClock γ 0 L t.val := by
    rcases le_total s.val t.val with hst | hts
    · exact variationClock_eq_of_constant hL hBV s.property.1 hst t.property.2
        (hfiber s.val t.val s.property.1 hst t.property.2 hstSig)
    · exact (variationClock_eq_of_constant hL hBV t.property.1 hts s.property.2
        (hfiber t.val s.val t.property.1 hts s.property.2 hstSig.symm)).symm
  exact Subtype.ext (hsr.symm.trans (hclock.trans htq))

/-- Every bounded-speed actual curve has an actual arc-length representative
with exactly the same based signature image and final signature. This does
not require any reducedness or injectivity hypothesis. -/
theorem arcLength_signature_range_factorization {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (P : Series ι) (f : speedControlledPaths L hL x) :
    ∃ (G : ℝ → ι → ℝ) (hG : LipschitzWith 1 G),
      G 0 = x ∧
      (eVariationOn G (Icc 0 (variationLength (pathExtension hL f.val) 0 L))).toReal =
        variationLength (pathExtension hL f.val) 0 L ∧
      EqOn (pathExtension hL f.val)
        (G ∘ variationClock (pathExtension hL f.val) 0 L) (Icc 0 L) ∧
      Set.range (fun r : Icc 0 (variationLength (pathExtension hL f.val) 0 L) =>
        product P (lipSignature G hG 0 r.val r.property.1)) = basedSignatureRange hL x P f ∧
      product P (lipSignature G hG 0 (variationLength (pathExtension hL f.val) 0 L)
        ENNReal.toReal_nonneg) = basedPrefixSignature hL x P f L := by
  let γ := pathExtension hL f.val
  have hγ : LipschitzWith 1 γ := pathExtension_lipschitz hL f.val f.property.1
  have hBV := lipschitz_boundedVariation γ hγ 0 L
  obtain ⟨G, _, _, hG, hfac, hvar, _⟩ :=
    arcLength_signature_factorization hL hBV hγ.continuous.continuousOn
  have hrel (u : ℝ) (hu : u ∈ Icc 0 L) :
      product P (lipSignature G hG 0 (variationClock γ 0 L u)
        (variationClock_mem hL hBV hu).1) = basedPrefixSignature hL x P f u := by
    change product P (lipSignature G hG 0 (variationClock γ 0 L u) _) =
      product P (prefixSignature hL x f u)
    rw [prefixSignature_eq_lipSignature hL x f hu.1]
    exact congrArg (product P) (lipSignature_arcLength_prefix γ G hγ hG hL hfac hu).symm
  have hstart : G 0 = x := by
    have he := hfac (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL⟩)
    simp only [Function.comp_apply, variationClock_initial] at he
    rw [← he]
    change f.val (projIcc 0 L hL 0) = x
    rw [projIcc_of_mem hL (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL⟩)]
    exact f.property.2
  refine ⟨G, hG, hstart, hvar, hfac, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨r, rfl⟩
      obtain ⟨s, hs⟩ := variationParameter_surjective hL hBV hγ.continuous.continuousOn r
      have hsr : variationClock γ 0 L s.val = r.val := congrArg Subtype.val hs
      refine ⟨s, ?_⟩
      exact (hrel s.val s.property).symm.trans
        (congrArg (product P) (lipSignature_endpoint_congr G hG _ r.property.1 hsr))
    · rintro ⟨s, rfl⟩
      exact ⟨⟨variationClock γ 0 L s.val, variationClock_mem hL hBV s.property⟩,
        hrel s.val s.property⟩
  · exact (congrArg (product P) (lipSignature_endpoint_congr G hG _ ENNReal.toReal_nonneg
      (variationClock_terminal γ hL))).symm.trans (hrel L ⟨hL, le_rfl⟩)

/-- Removing only the stationary parts of a reduced actual representative
produces an actual injective signature arc, with its exact signature image. -/
theorem exists_arcLength_injective_lift {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (P : Series ι) (f : speedControlledPaths L hL x)
    (hfiber : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ L →
      basedPrefixSignature hL x P f s = basedPrefixSignature hL x P f t →
      ∀ u ∈ Icc s t, pathExtension hL f.val u = pathExtension hL f.val s) :
    ∃ (G : ℝ → ι → ℝ) (hG : LipschitzWith 1 G),
      G 0 = x ∧
      (eVariationOn G (Icc 0 (variationLength (pathExtension hL f.val) 0 L))).toReal =
        variationLength (pathExtension hL f.val) 0 L ∧
      Set.range (fun r : Icc 0 (variationLength (pathExtension hL f.val) 0 L) =>
        product P (lipSignature G hG 0 r.val r.property.1)) = basedSignatureRange hL x P f ∧
      product P (lipSignature G hG 0 (variationLength (pathExtension hL f.val) 0 L)
        ENNReal.toReal_nonneg) = basedPrefixSignature hL x P f L ∧
      Function.Injective (fun r : Icc 0 (variationLength (pathExtension hL f.val) 0 L) =>
        product P (lipSignature G hG 0 r.val r.property.1)) := by
  obtain ⟨G, hG, hstart, hvar, hfac, hrange, hend⟩ :=
    arcLength_signature_range_factorization hL x P f
  refine ⟨G, hG, hstart, hvar, hrange, hend, ?_⟩
  apply arcLength_based_lift_injective (pathExtension hL f.val) G
    (pathExtension_lipschitz hL f.val f.property.1) hG hL P hfac
  intro s t hs hst ht he
  apply hfiber s t hs hst ht
  change product P (prefixSignature hL x f s) = product P (prefixSignature hL x f t)
  rwa [prefixSignature_eq_lipSignature hL x f hs,
    prefixSignature_eq_lipSignature hL x f (hs.trans hst)]

/-- A nonempty class of actual based lifts in a closed signature set has an
actual injective arc-length representative. Its length is least among all
bounded-speed competitors on the supplied time budget. Every existence,
compactness, loop deletion, and reparameterization step is constructed. -/
theorem exists_injective_signature_lift_in_closed_range {ι : Type*} [Fintype ι]
    {L : ℝ} (hL : 0 ≤ L) (x : ι → ℝ) (P Q : Series ι) (hP : P [] = 1)
    {K : Set (Series ι)} (hK : IsClosed K)
    (f : speedControlledPaths L hL x) (hf : f ∈ signatureRangeClass hL x P Q K) :
    ∃ (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (G : ℝ → ι → ℝ) (hG : LipschitzWith 1 G),
      G 0 = x ∧ (eVariationOn G (Icc 0 ℓ)).toReal = ℓ ∧
      product P (lipSignature G hG 0 ℓ hℓ) = Q ∧
      (∀ r : Icc 0 ℓ, product P (lipSignature G hG 0 r.val r.property.1) ∈ K) ∧
      Function.Injective (fun r : Icc 0 ℓ => product P (lipSignature G hG 0 r.val r.property.1)) ∧
      ∀ h : speedControlledPaths L hL x, h ∈ signatureRangeClass hL x P Q K →
        ℓ ≤ (eVariationOn (pathExtension hL h.val) (Icc 0 L)).toReal := by
  obtain ⟨g, hg, hmin⟩ := exists_minimal_signature_range_representative hL x P Q hK f hf
  obtain ⟨G, hG, hstart, hvar, hrange, hend, hinj⟩ :=
    exists_arcLength_injective_lift hL x P g (by
      intro s t hs hst ht he
      exact minimal_representative_constant_on_signature_fiber hL x P Q hP K g hg hmin hs hst ht he)
  refine ⟨variationLength (pathExtension hL g.val) 0 L, ENNReal.toReal_nonneg,
    G, hG, hstart, hvar, hend.trans hg.1, ?_, hinj, ?_⟩
  · intro r
    have hr : product P (lipSignature G hG 0 r.val r.property.1) ∈ basedSignatureRange hL x P g := by
      rw [← hrange]
      exact ⟨r, rfl⟩
    obtain ⟨u, hu⟩ := hr
    rw [← hu]
    exact hg.2 u
  · intro h hh
    exact ENNReal.toReal_mono
      (unitLipschitz_variation_ne_top (pathExtension_lipschitz hL h.val h.property.1) 0 L)
      (hmin h hh)

end LinearInputCurveWordBVArc
