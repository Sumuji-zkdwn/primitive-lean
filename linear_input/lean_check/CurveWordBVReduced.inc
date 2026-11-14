/-!
Variation and cancellation lemmas for constructing reduced actual signature
lifts. These lemmas do not assert that arbitrary image arcs are subintervals.
-/

noncomputable section
namespace LinearInputCurveWordBVReduced
open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
open LinearInputCurveWordBoundedVariation LinearInputCurveWordBVCanonical
open LinearInputCurveWordBVCompactness
open LinearInputCurveWordBVLoopErase LinearInputCurveWordFormalSeries
open LinearInputCurveWordBVSubinterval LinearInputCurveWordStieltjes

theorem unitLipschitz_variation_le {E : Type*} [MetricSpace E] {γ : ℝ → E}
    (hγ : LipschitzWith 1 γ) (a b : ℝ) :
    eVariationOn γ (Icc a b) ≤ ENNReal.ofReal (b - a) := by
  have hi : eVariationOn (id : ℝ → ℝ) (Icc a b) ≤ ENNReal.ofReal (b - a) := by
    simpa only [univ_inter, id_eq] using
      ((monotone_id.monotoneOn univ).eVariationOn_eq (a := a) (b := b) (mem_univ _) (mem_univ _)).le
  have he := hγ.lipschitzOnWith.comp_eVariationOn_le (g := id)
    (s := Icc a b) (mapsTo_univ id (Icc a b))
  simp only [Function.comp_id, ENNReal.coe_one, one_mul] at he
  exact he.trans hi

theorem unitLipschitz_variation_ne_top {E : Type*} [MetricSpace E] {γ : ℝ → E}
    (hγ : LipschitzWith 1 γ) (a b : ℝ) : eVariationOn γ (Icc a b) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (unitLipschitz_variation_le hγ a b)

theorem unitLipschitz_variation_toReal_le {E : Type*} [MetricSpace E] {γ : ℝ → E}
    (hγ : LipschitzWith 1 γ) {a b : ℝ} (hab : a ≤ b) :
    (eVariationOn γ (Icc a b)).toReal ≤ b - a := by
  simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (unitLipschitz_variation_le hγ a b)

theorem unitLipschitz_variation_add {E : Type*} [MetricSpace E] {γ : ℝ → E}
    (hγ : LipschitzWith 1 γ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (eVariationOn γ (Icc a b)).toReal + (eVariationOn γ (Icc b c)).toReal =
      (eVariationOn γ (Icc a c)).toReal := by
  rw [← ENNReal.toReal_add (unitLipschitz_variation_ne_top hγ a b)
    (unitLipschitz_variation_ne_top hγ b c)]
  congr 1
  simpa only [univ_inter] using eVariationOn.Icc_add_Icc γ (s := univ) hab hbc (mem_univ b)

/-- A 1-Lipschitz curve attaining its available total length has unit
variation speed on every subinterval. Thus its arc-length representative
cannot hide a nondegenerate constant interval. -/
theorem arcLength_variation_subinterval {E : Type*} [MetricSpace E] {γ : ℝ → E}
    (hγ : LipschitzWith 1 γ) {L s t : ℝ}
    (hfull : (eVariationOn γ (Icc 0 L)).toReal = L)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L) :
    (eVariationOn γ (Icc s t)).toReal = t - s := by
  have hsum1 := unitLipschitz_variation_add hγ hs (hst.trans ht)
  have hsum2 := unitLipschitz_variation_add hγ hst ht
  have hbound1 := unitLipschitz_variation_toReal_le hγ hs
  have hbound2 := unitLipschitz_variation_toReal_le hγ hst
  have hbound3 := unitLipschitz_variation_toReal_le hγ ht
  rw [hfull] at hsum1
  linarith

/-- Left multiplication by a series with constant coefficient one is
injective. This is proved directly by finite word-length induction. -/
theorem basedPrefix_eq_imp_prefix_eq {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (P : List ι → ℝ) (hP : P [] = 1)
    (f g : speedControlledPaths L hL x) (s t : ℝ)
    (he : basedPrefixSignature hL x P f s = basedPrefixSignature hL x P g t) :
    prefixSignature hL x f s = prefixSignature hL x g t := by
  have hw : ∀ n : ℕ, ∀ w : List ι, w.length = n →
      prefixSignature hL x f s w = prefixSignature hL x g t w := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro w hlen
      have hew := congrArg (fun S : List ι → ℝ => S w) he
      change (∑ k ∈ Finset.range (w.length + 1),
          P (w.take k) * prefixSignature hL x f s (w.drop k)) =
        ∑ k ∈ Finset.range (w.length + 1),
          P (w.take k) * prefixSignature hL x g t (w.drop k) at hew
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hew
      simp only [List.take_zero, List.drop_zero, hP, one_mul] at hew
      have hrest : (∑ k ∈ Finset.range w.length,
          P (w.take (k + 1)) * prefixSignature hL x f s (w.drop (k + 1))) =
        ∑ k ∈ Finset.range w.length,
          P (w.take (k + 1)) * prefixSignature hL x g t (w.drop (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hlt : (w.drop (k + 1)).length < n := by
          simp only [List.length_drop]
          have hk' := Finset.mem_range.mp hk
          omega
        rw [ih _ hlt _ rfl]
      linarith
  funext w
  exact hw w.length w rfl

theorem prefixSignature_continuous_time {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (f : speedControlledPaths L hL x) :
    Continuous (prefixSignature hL x f) := by
  apply LinearInputCurveWordBVTopology.signature_lift_continuous
  · intro i
    exact (LinearInputCurveWordStieltjes.jordan_continuous
      (coordinateExtension_boundedVariation hL f.val f.property.1 i)
      (coordinateExtension_continuous hL f.val i) 0).1
  · intro i
    exact (LinearInputCurveWordStieltjes.jordan_continuous
      (coordinateExtension_boundedVariation hL f.val f.property.1 i)
      (coordinateExtension_continuous hL f.val i) 0).2

theorem basedPrefixSignature_continuous_time {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (P : List ι → ℝ) (f : speedControlledPaths L hL x) :
    Continuous (basedPrefixSignature hL x P f) := by
  apply continuous_pi
  intro w
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul
    ((continuous_apply (w.drop k)).comp (prefixSignature_continuous_time hL x f))

def basedSignatureRange {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (P : List ι → ℝ) (f : speedControlledPaths L hL x) :
    Set (List ι → ℝ) :=
  Set.range (fun r : Icc (0 : ℝ) L => basedPrefixSignature hL x P f r.val)

theorem basedSignatureRange_isCompact {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (P : List ι → ℝ) (f : speedControlledPaths L hL x) :
    IsCompact (basedSignatureRange hL x P f) :=
  isCompact_range ((basedPrefixSignature_continuous_time hL x P f).comp continuous_subtype_val)

/-- Starting from a given actual bounded-speed curve, one obtains a genuine
least-variation curve with the same endpoint signature whose entire based
signature lift stays in the original signature image. Nonemptiness and the
image's closedness are both derived here, not assumed. -/
theorem exists_minimal_in_actual_signature_image {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (P : List ι → ℝ) (f : speedControlledPaths L hL x) :
    ∃ g : speedControlledPaths L hL x,
      basedPrefixSignature hL x P g L = basedPrefixSignature hL x P f L ∧
      basedSignatureRange hL x P g ⊆ basedSignatureRange hL x P f ∧
      ∀ h : speedControlledPaths L hL x,
        basedPrefixSignature hL x P h L = basedPrefixSignature hL x P f L →
        basedSignatureRange hL x P h ⊆ basedSignatureRange hL x P f →
        eVariationOn (pathExtension hL g.val) (Icc 0 L) ≤
          eVariationOn (pathExtension hL h.val) (Icc 0 L) := by
  have hf : f ∈ signatureRangeClass hL x P (basedPrefixSignature hL x P f L)
      (basedSignatureRange hL x P f) := ⟨rfl, fun r => ⟨r, rfl⟩⟩
  obtain ⟨g, hg, hmin⟩ := exists_minimal_signature_range_representative hL x P
    (basedPrefixSignature hL x P f L) (basedSignatureRange_isCompact hL x P f).isClosed f hf
  refine ⟨g, hg.1, ?_, ?_⟩
  · rintro y ⟨r, rfl⟩
    exact hg.2 r
  · intro h he hr
    exact hmin h ⟨he, fun r => hr ⟨r, rfl⟩⟩

theorem prefixSignature_eq_lipSignature {ι : Type*} [Fintype ι] {L r : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (f : speedControlledPaths L hL x) (hr : 0 ≤ r) :
    prefixSignature hL x f r =
      lipSignature (pathExtension hL f.val) (pathExtension_lipschitz hL f.val f.property.1) 0 r hr :=
  prefixSignature_eq_pathSignature hL x f hr

/-- The actual minimal curve is constant on every interval on which its
based signature lift returns to the same point. The competitor used in the
proof is the explicitly constructed loop deletion, with all admissibility
properties proved for that deletion. -/
theorem minimal_representative_constant_on_signature_fiber {ι : Type*} [Fintype ι]
    {L : ℝ} (hL : 0 ≤ L) (x : ι → ℝ) (P Q : List ι → ℝ) (hP : P [] = 1)
    (K : Set (List ι → ℝ)) (f : speedControlledPaths L hL x)
    (hf : f ∈ signatureRangeClass hL x P Q K)
    (hmin : ∀ g : speedControlledPaths L hL x, g ∈ signatureRangeClass hL x P Q K →
      eVariationOn (pathExtension hL f.val) (Icc 0 L) ≤
        eVariationOn (pathExtension hL g.val) (Icc 0 L))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L)
    (he : basedPrefixSignature hL x P f s = basedPrefixSignature hL x P f t) :
    ∀ u ∈ Icc s t, pathExtension hL f.val u = pathExtension hL f.val s := by
  let γ := pathExtension hL f.val
  have hγ : LipschitzWith 1 γ := pathExtension_lipschitz hL f.val f.property.1
  let p := fun i => bvPositive (coordinateExtension_boundedVariation hL f.val f.property.1 i)
    (coordinateExtension_continuous hL f.val i) 0
  let m := fun i => bvNegative (coordinateExtension_boundedVariation hL f.val f.property.1 i)
    (coordinateExtension_continuous hL f.val i) 0
  have hp : ∀ i, Continuous (p i : ℝ → ℝ) := fun i =>
    (jordan_continuous (coordinateExtension_boundedVariation hL f.val f.property.1 i)
      (coordinateExtension_continuous hL f.val i) 0).1
  have hm : ∀ i, Continuous (m i : ℝ → ℝ) := fun i =>
    (jordan_continuous (coordinateExtension_boundedVariation hL f.val f.property.1 i)
      (coordinateExtension_continuous hL f.val i) 0).2
  have hprefix : stieltjesSignature p m 0 s = stieltjesSignature p m 0 t :=
    basedPrefix_eq_imp_prefix_eq hL x P hP f f s t he
  have hreps : ∀ i, RepresentsOn (p i) (m i) (fun u => γ u i) s t := by
    intro i u _ v _
    have hu := jordan_difference (fun z => γ z i) 0 u
    have hv := jordan_difference (fun z => γ z i) 0 v
    change (jordanPositive (fun z => γ z i) 0 v - jordanPositive (fun z => γ z i) 0 u) -
      (jordanNegative (fun z => γ z i) 0 v - jordanNegative (fun z => γ z i) 0 u) = _
    linarith
  have hzero : lipSignature γ hγ s t hst = unitSeries := by
    funext w
    rw [show lipSignature γ hγ s t hst w = stieltjesSignature p m s t w from
      pathSignature_eq_representation γ hst _ _ p m hp hm hreps w]
    cases w with
    | nil => rfl
    | cons i w => exact subinterval_signature_zero_of_prefix_eq p m hp hm hprefix _ (by simp)
  have hloop : γ s = γ t := by
    funext i
    have hz := congrArg (fun S : Series ι => S [i]) hzero
    change curveSignature (fun j u => γ u j) hst _ _ [i] = 0 at hz
    rw [curveSignature_singleton] at hz
    linarith
  by_contra! hne
  have hK : ∀ u (hu : u ∈ Icc 0 L), product P (lipSignature γ hγ 0 u hu.1) ∈ K := by
    intro u hu
    rw [← prefixSignature_eq_lipSignature hL x f hu.1]
    exact hf.2 ⟨u, hu⟩
  obtain ⟨δ, hδ, hδ0, _, hδsig, hδK, hδshort⟩ :=
    exists_shorter_representative γ hγ hs hst ht hloop hzero hne P K hK
  have hγ0 : γ 0 = x := by
    change f.val (projIcc 0 L hL 0) = x
    rw [projIcc_of_mem hL (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL⟩)]
    exact f.property.2
  let d0 := speedControlledOfLipschitz hL δ hδ
  let d : speedControlledPaths L hL x :=
    ⟨d0.val, d0.property.1, d0.property.2.trans (hδ0.trans hγ0)⟩
  have hdEq : EqOn (pathExtension hL d.val) δ (Icc 0 L) :=
    speedControlledOfLipschitz_eq hL δ hδ
  have hdSig (u : ℝ) (hu : u ∈ Icc 0 L) :
      prefixSignature hL x d u = lipSignature δ hδ 0 u hu.1 := by
    rw [prefixSignature_eq_lipSignature hL x d hu.1]
    exact lipSignature_congr _ _ _ _ hu.1
      (fun v hv => hdEq ⟨hv.1, hv.2.trans hu.2⟩)
  have hd : d ∈ signatureRangeClass hL x P Q K := by
    constructor
    · change product P (prefixSignature hL x d L) = Q
      rw [hdSig L ⟨hL, le_rfl⟩, hδsig, ← prefixSignature_eq_lipSignature hL x f hL]
      exact hf.1
    · intro u
      change product P (prefixSignature hL x d u.val) ∈ K
      rw [hdSig u.val u.property]
      exact hδK u.val u.property
  have hle := hmin d hd
  rw [eVariationOn.congr hdEq] at hle
  have hleReal := ENNReal.toReal_mono (unitLipschitz_variation_ne_top hδ 0 L) hle
  exact (not_lt_of_ge hleReal) hδshort

/-- Every actual bounded-speed input has a minimum-variation representative
inside its original based signature image; any repeated lift value on this
representative spans only a constant portion of the actual coordinate curve.
No minimizing representative or loop-erasure limit is assumed as input. -/
theorem exists_reduced_in_actual_signature_image {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (P : List ι → ℝ) (hP : P [] = 1)
    (f : speedControlledPaths L hL x) :
    ∃ g : speedControlledPaths L hL x,
      basedPrefixSignature hL x P g L = basedPrefixSignature hL x P f L ∧
      basedSignatureRange hL x P g ⊆ basedSignatureRange hL x P f ∧
      (∀ h : speedControlledPaths L hL x,
        basedPrefixSignature hL x P h L = basedPrefixSignature hL x P f L →
        basedSignatureRange hL x P h ⊆ basedSignatureRange hL x P f →
        eVariationOn (pathExtension hL g.val) (Icc 0 L) ≤
          eVariationOn (pathExtension hL h.val) (Icc 0 L)) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ L →
        basedPrefixSignature hL x P g s = basedPrefixSignature hL x P g t →
        ∀ u ∈ Icc s t, pathExtension hL g.val u = pathExtension hL g.val s) := by
  obtain ⟨g, hend, hrange, hmin⟩ := exists_minimal_in_actual_signature_image hL x P f
  refine ⟨g, hend, hrange, hmin, ?_⟩
  have hg : g ∈ signatureRangeClass hL x P (basedPrefixSignature hL x P f L)
      (basedSignatureRange hL x P f) := ⟨hend, fun r => hrange ⟨r, rfl⟩⟩
  intro s t hs hst ht he
  apply minimal_representative_constant_on_signature_fiber hL x P
    (basedPrefixSignature hL x P f L) hP (basedSignatureRange hL x P f) g hg ?_ hs hst ht he
  intro h hh
  apply hmin h hh.1
  rintro y ⟨r, rfl⟩
  exact hh.2 r

end LinearInputCurveWordBVReduced
