/-!
Actual continuous-BV normalization and transport of independent geometric
tree-height witnesses. The intrinsic signature metric is connected below;
no signature equality is used as the definition of geometric tree-likeness.
-/

noncomputable section
namespace LinearInputCurveWordBVHamblyLyons
open Set MeasureTheory
open scoped Topology
open LinearInputCurveWordBoundedVariation LinearInputCurveWordBVCanonical
open LinearInputCurveWordBVPathOperations LinearInputCurveWordBVLoopErase
open LinearInputCurveWordBVCompactness LinearInputCurveWordBVReduced LinearInputCurveWordBVArc
open LinearInputCurveWordTreeLike LinearInputCurveWordSignatureTree
open LinearInputCurveWordFormalSeries LinearInputCurveWordStieltjes
open LinearInputCurveWordBVSubinterval LinearInputCurveWordBVTopology
open LinearInputCurveWordBVIntrinsic

def canonicalPrefix {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ) {a b : ℝ}
    (_hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (t : Icc a b) : Series ι :=
  pathSignature γ t.property.1 (hγ.mono (Icc_subset_Icc le_rfl t.property.2))
    (hc.mono (Icc_subset_Icc le_rfl t.property.2))

theorem canonicalPrefix_eq_stieltjes {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) (t : Icc a b) :
    canonicalPrefix γ hab hγ hc t =
      stieltjesSignature
        (fun i => canonicalPositive hab (coordinate_boundedVariation hγ i) (coordinate_continuousOn hc i))
        (fun i => canonicalNegative hab (coordinate_boundedVariation hγ i) (coordinate_continuousOn hc i))
        a t.val := by
  funext w
  exact curveSignature_subinterval_eq (fun i u => γ u i) hab
    (coordinate_boundedVariation hγ) (coordinate_continuousOn hc)
    le_rfl t.property.1 t.property.2 w

theorem canonicalPrefix_continuous {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    Continuous (canonicalPrefix γ hab hγ hc) := by
  have he := funext (canonicalPrefix_eq_stieltjes γ hab hγ hc)
  rw [he]
  exact (signature_lift_continuous
    (fun i => canonicalPositive_continuous hab (coordinate_boundedVariation hγ i) (coordinate_continuousOn hc i))
    (fun i => canonicalNegative_continuous hab (coordinate_boundedVariation hγ i) (coordinate_continuousOn hc i))
    a).comp continuous_subtype_val

theorem canonicalPrefix_nil {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (t : Icc a b) : canonicalPrefix γ hab hγ hc t [] = 1 := rfl

theorem canonicalPrefix_singleton {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (t : Icc a b) (i : ι) : canonicalPrefix γ hab hγ hc t [i] = γ t.val i - γ a i :=
  curveSignature_singleton _ _ _ _ i

theorem canonicalPrefix_initial {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    canonicalPrefix γ hab hγ hc ⟨a, le_rfl, hab⟩ = unitSeries := by
  rw [canonicalPrefix_eq_stieltjes]
  exact LinearInputCurveWordBVPathOperations.stieltjesSignature_same _ _ a

theorem canonicalPrefix_terminal {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    canonicalPrefix γ hab hγ hc ⟨b, hab, le_rfl⟩ = pathSignature γ hab hγ hc := rfl

theorem canonicalPrefix_range_isCompact {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    IsCompact (Set.range (canonicalPrefix γ hab hγ hc)) :=
  isCompact_range (canonicalPrefix_continuous γ hab hγ hc)

theorem treeHeight_congr {E : Type*} [PseudoMetricSpace E] {γ δ : ℝ → E}
    {a b : ℝ} {h : ℝ → ℝ} (hh : HasTreeHeight δ a b h) (he : EqOn γ δ (Icc a b)) :
    HasTreeHeight γ a b h := by
  refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, ?_⟩
  intro s hs t ht
  obtain ⟨r, hr, hb⟩ := hh.2.2.2.2 s hs t ht
  refine ⟨r, hr, ?_⟩
  rw [he hs, he ⟨hs.1.trans ht.1, ht.2⟩]
  exact hb

/-- Continuous monotone time changes transport the independent height
witness. The intermediate minimizing point is pulled back by the actual
intermediate value theorem on the corresponding time subinterval. -/
theorem treeHeight_reparametrize {E : Type*} [PseudoMetricSpace E] {γ : ℝ → E}
    {h φ : ℝ → ℝ} {a b c d : ℝ} (hh : HasTreeHeight γ c d h)
    (hab : a ≤ b) (hm : MonotoneOn φ (Icc a b)) (hφ : ContinuousOn φ (Icc a b))
    (ha : φ a = c) (hb : φ b = d) :
    HasTreeHeight (γ ∘ φ) a b (h ∘ φ) := by
  have hmap := reparam_mapsTo_endpoints hab hm ha hb
  refine ⟨hh.1.comp hφ hmap, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply, ha] using hh.2.1
  · simpa only [Function.comp_apply, hb] using hh.2.2.1
  · intro t ht
    exact hh.2.2.2.1 (φ t) (hmap ht)
  · intro s hs t ht
    have ht' : t ∈ Icc a b := ⟨hs.1.trans ht.1, ht.2⟩
    obtain ⟨r, hr, hbound⟩ := hh.2.2.2.2 (φ s) (hmap hs) (φ t)
      ⟨hm hs ht' ht.1, (hmap ht').2⟩
    obtain ⟨u, hu, he⟩ := intermediate_value_Icc ht.1
      (hφ.mono (Icc_subset_Icc hs.1 ht.2)) hr
    refine ⟨u, hu, ?_⟩
    simpa only [Function.comp_apply, he] using hbound

theorem treeLike_reparametrize {E : Type*} [PseudoMetricSpace E] {γ : ℝ → E}
    {φ : ℝ → ℝ} {a b c d : ℝ} (hγ : TreeLike γ c d)
    (hab : a ≤ b) (hm : MonotoneOn φ (Icc a b)) (hφ : ContinuousOn φ (Icc a b))
    (ha : φ a = c) (hb : φ b = d) : TreeLike (γ ∘ φ) a b := by
  obtain ⟨hc, h, hh⟩ := hγ
  exact ⟨hc.comp hφ (reparam_mapsTo_endpoints hab hm ha hb),
    h ∘ φ, treeHeight_reparametrize hh hab hm hφ ha hb⟩

/-- Arc-length normalization of a general continuous BV curve preserves
every prefix of the actual canonical signature. No Lipschitz hypothesis on
the original time parametrization is imposed. -/
theorem pathSignature_arcLength_prefix {ι : Type*} [Fintype ι]
    (γ G : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hG : LipschitzWith 1 G)
    (hfac : EqOn γ (G ∘ variationClock γ a b) (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    pathSignature γ ht.1 (hγ.mono (Icc_subset_Icc le_rfl ht.2))
      (hc.mono (Icc_subset_Icc le_rfl ht.2)) =
      lipSignature G hG 0 (variationClock γ a b t) (variationClock_mem hab hγ ht).1 := by
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hm := (variationClock_monotoneOn hab hγ).mono hsub
  have hclock := (variation_clock_continuousOn hγ hc ⟨le_rfl, hab⟩).mono hsub
  have he := pathSignature_reparametrize_endpoints G (variationClock_mem hab hγ ht).1 ht.1 hm hclock
    (variationClock_initial γ a b) rfl
    (lipschitz_boundedVariation G hG 0 (variationClock γ a b t)) hG.continuous.continuousOn
  funext w
  calc
    _ = pathSignature (G ∘ variationClock γ a b) ht.1 _ _ w :=
      pathSignature_congr ht.1 _ _ _ _ (hfac.mono hsub) w
    _ = _ := congrArg (fun S : List ι → ℝ => S w) he

/-- A geometric height on the actual arc-length representative pulls back
to a geometric height of the original BV curve through its explicit clock. -/
theorem treeLike_of_arcLength_factor {ι : Type*} [Fintype ι]
    {γ G : ℝ → ι → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hfac : EqOn γ (G ∘ variationClock γ a b) (Icc a b))
    (hTree : TreeLike G 0 (variationLength γ a b)) : TreeLike γ a b := by
  have hr := treeLike_reparametrize hTree hab (variationClock_monotoneOn hab hγ)
    (variation_clock_continuousOn hγ hc ⟨le_rfl, hab⟩)
    (variationClock_initial γ a b) (variationClock_terminal γ hab)
  obtain ⟨_, h, hh⟩ := hr
  exact ⟨hc, h, treeHeight_congr hh hfac⟩

/-- The original finite-dimensional BV curve and its actual 1-Lipschitz
representative have exactly the same full signature image. The original
time variable is related by the explicit continuous variation clock. -/
theorem canonicalPrefix_arcLength_factorization {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    ∃ (G : ℝ → ι → ℝ) (hG : LipschitzWith 1 G),
      G 0 = γ a ∧
      (eVariationOn G (Icc 0 (variationLength γ a b))).toReal = variationLength γ a b ∧
      EqOn γ (G ∘ variationClock γ a b) (Icc a b) ∧
      (∀ t : Icc a b, canonicalPrefix γ hab hγ hc t =
        lipSignature G hG 0 (variationClock γ a b t.val) (variationClock_mem hab hγ t.property).1) ∧
      Set.range (canonicalPrefix γ hab hγ hc) =
        Set.range (fun r : Icc 0 (variationLength γ a b) => lipSignature G hG 0 r.val r.property.1) := by
  obtain ⟨G, _, _, hG, hfac, hvar, _⟩ := arcLength_signature_factorization hab hγ hc
  have hstart : G 0 = γ a := by
    have he := hfac (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
    simpa only [Function.comp_apply, variationClock_initial] using he.symm
  have hprefix (t : Icc a b) := pathSignature_arcLength_prefix γ G hab hγ hc hG hfac t.property
  refine ⟨G, hG, hstart, hvar, hfac, hprefix, ?_⟩
  ext S
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨variationClock γ a b t.val, variationClock_mem hab hγ t.property⟩, (hprefix t).symm⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨t, ht⟩ := variationParameter_surjective hab hγ hc r
    have htr : variationClock γ a b t.val = r.val := congrArg Subtype.val ht
    exact ⟨t, (hprefix t).trans (lipSignature_endpoint_congr G hG _ r.property.1 htr)⟩

/-- Ordered increments of the actual variation clock are exactly the
variation of the corresponding original time subcurve. -/
theorem variationClock_sub {E : Type*} [PseudoEMetricSpace E]
    {γ : ℝ → E} {a b s t : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    variationClock γ a b t - variationClock γ a b s = (eVariationOn γ (Icc s t)).toReal := by
  have hadd := variationOnFromTo.add hγ.locallyBoundedVariationOn
    (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
    (show s ∈ Icc a b from ⟨hs, hst.trans ht⟩)
    (show t ∈ Icc a b from ⟨hs.trans hst, ht⟩)
  rw [variationOnFromTo.eq_of_le _ _ hst, Set.inter_eq_right.mpr (Icc_subset_Icc hs ht)] at hadd
  change variationClock γ a b s + _ = variationClock γ a b t at hadd
  linarith

/-- Pulling a unit-Lipschitz metric lift back through the variation clock
gives the required intrinsic distance bound by actual subcurve variation. -/
theorem arcLength_lift_distance_le_variation {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {γ : ℝ → E} {σ : ℝ → F} (hσ : LipschitzWith 1 σ) {a b s t : ℝ}
    (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    dist (σ (variationClock γ a b s)) (σ (variationClock γ a b t)) ≤
      (eVariationOn γ (Icc s t)).toReal := by
  have hmono := variationClock_monotoneOn hab hγ ⟨hs, hst.trans ht⟩ ⟨hs.trans hst, ht⟩ hst
  have hbound := hσ.dist_le_mul (variationClock γ a b t) (variationClock γ a b s)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hmono)] at hbound
  rw [dist_comm, ← variationClock_sub hab hγ hs hst ht]
  exact hbound

theorem arcLength_lift_continuousOn {E F : Type*} [MetricSpace E] [PseudoMetricSpace F]
    {γ : ℝ → E} {σ : ℝ → F} (hσ : LipschitzWith 1 σ) {a b : ℝ}
    (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    ContinuousOn (σ ∘ variationClock γ a b) (Icc a b) :=
  hσ.continuous.comp_continuousOn (variation_clock_continuousOn hγ hc ⟨le_rfl, hab⟩)

/-- The four-point metric produces an explicit root-distance height for
any continuous closed lift which dominates the original coordinate distance.
The predicate in the conclusion is the independent geometric height
condition defined before signatures were introduced. -/
theorem treeHeight_of_dominated_fourPoint_lift {E F : Type*}
    [PseudoMetricSpace E] [PseudoMetricSpace F] {γ : ℝ → E} {τ : ℝ → F}
    {a b : ℝ} (h4 : @FourPoint F _) (hτ : ContinuousOn τ (Icc a b))
    (hclosed : τ a = τ b)
    (hdom : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (γ s) (γ t) ≤ dist (τ s) (τ t)) :
    HasTreeHeight γ a b (fun t => dist (τ a) (τ t)) := by
  have hh := loop_hasTreeHeight h4 hτ hclosed
  refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, ?_⟩
  intro s hs t ht
  obtain ⟨r, hr, hbound⟩ := hh.2.2.2.2 s hs t ht
  exact ⟨r, hr, (hdom s hs t ⟨hs.1.trans ht.1, ht.2⟩).trans hbound⟩

/-- The final geometric transfer for a realized signature metric. In the
application, the metric, its four-point property, its coordinate projection,
and this continuous lift are supplied by the constructed intrinsic space.
This lemma only converts those concrete data into the independent height. -/
theorem treeLike_of_realized_signature_metric {ι : Type*} [Fintype ι]
    (G : ℝ → ι → ℝ) (hG : LipschitzWith 1 G) {L : ℝ} (hL : 0 ≤ L)
    (hzero : lipSignature G hG 0 L hL = unitSeries)
    {F : Type*} [MetricSpace F] (h4 : @FourPoint F _)
    (value : F → Series ι) (hinj : Function.Injective value)
    (hfirst : LipschitzWith 1 (fun p : F => fun i : ι => value p [i]))
    (σ : ℝ → F) (hσ : ContinuousOn σ (Icc 0 L))
    (hvalue : ∀ t (ht : t ∈ Icc 0 L), value (σ t) = lipSignature G hG 0 t ht.1) :
    TreeLike G 0 L := by
  have hclosed : σ 0 = σ L := by
    apply hinj
    rw [hvalue 0 ⟨le_rfl, hL⟩, hvalue L ⟨hL, le_rfl⟩, hzero]
    exact LinearInputCurveWordBVPathOperations.stieltjesSignature_same _ _ 0
  have hdom : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, dist (G s) (G t) ≤ dist (σ s) (σ t) := by
    intro s hs t ht
    have hcoords (u : ℝ) (hu : u ∈ Icc 0 L) : (fun i => value (σ u) [i]) = G u - G 0 := by
      funext i
      rw [hvalue u hu]
      exact curveSignature_singleton _ _ _ _ i
    have hd := hfirst.dist_le_mul (σ s) (σ t)
    simp only [NNReal.coe_one, one_mul] at hd
    rw [hcoords s hs, hcoords t ht, dist_sub_right] at hd
    exact hd
  exact ⟨hG.continuous.continuousOn, _, treeHeight_of_dominated_fourPoint_lift h4 hσ hclosed hdom⟩

def lipSignatureImage {ι : Type*} [Fintype ι] (G : ℝ → ι → ℝ)
    (hG : LipschitzWith 1 G) (L : ℝ) (_hL : 0 ≤ L) : Set (Series ι) :=
  Set.range (fun t : Icc (0 : ℝ) L => lipSignature G hG 0 t.val t.property.1)

theorem lipSignatureImage_isCompact {ι : Type*} [Fintype ι] (G : ℝ → ι → ℝ)
    (hG : LipschitzWith 1 G) {L : ℝ} (hL : 0 ≤ L) :
    IsCompact (lipSignatureImage G hG L hL) :=
  canonicalPrefix_range_isCompact G hL (lipschitz_boundedVariation G hG 0 L) hG.continuous.continuousOn

theorem lipSignatureImage_isClosed {ι : Type*} [Fintype ι] (G : ℝ → ι → ℝ)
    (hG : LipschitzWith 1 G) {L : ℝ} (hL : 0 ≤ L) :
    IsClosed (lipSignatureImage G hG L hL) := (lipSignatureImage_isCompact G hG hL).isClosed

/-- The actual normalized curve, translated to start at zero, gives a
concrete closed intrinsic route when its full signature is trivial. -/
def normalizedLoopRoute {ι : Type*} [Fintype ι] (G : ℝ → ι → ℝ)
    (hG : LipschitzWith 1 G) {L : ℝ} (hL : 0 ≤ L)
    (hzero : lipSignature G hG 0 L hL = unitSeries) :
    Route (lipSignatureImage G hG L hL) unitSeries unitSeries where
  duration := L
  nonneg := hL
  curve := fun t => G t + -G 0
  lipschitz := translate_lipschitz G hG (-G 0)
  initial := by simp
  terminal := by
    rw [product_unit_left, lipSignature_translate G hG (-G 0) hL]
    exact hzero
  within := by
    intro t ht
    rw [product_unit_left, lipSignature_translate G hG (-G 0) ht.1]
    exact ⟨⟨t, ht⟩, rfl⟩

theorem normalizedLoopRoute_prefix {ι : Type*} [Fintype ι] (G : ℝ → ι → ℝ)
    (hG : LipschitzWith 1 G) {L : ℝ} (hL : 0 ≤ L)
    (hzero : lipSignature G hG 0 L hL = unitSeries) {t : ℝ} (ht : 0 ≤ t) :
    lipSignature (normalizedLoopRoute G hG hL hzero).curve
      (normalizedLoopRoute G hG hL hzero).lipschitz 0 t ht = lipSignature G hG 0 t ht :=
  lipSignature_translate G hG (-G 0) ht

def normalizedLoopLift {ι : Type*} [Fintype ι] (G : ℝ → ι → ℝ)
    (hG : LipschitzWith 1 G) {L : ℝ} (hL : 0 ≤ L)
    (hzero : lipSignature G hG 0 L hL = unitSeries) :
    ℝ → IntrinsicPoint (lipSignatureImage G hG L hL) (lipSignatureImage_isClosed G hG hL) unitSeries :=
  fun t => (normalizedLoopRoute G hG hL hzero).prefixPoint
    (lipSignatureImage_isClosed G hG hL) (projIcc 0 L hL t)

theorem normalizedLoopLift_lipschitz {ι : Type*} [Fintype ι] (G : ℝ → ι → ℝ)
    (hG : LipschitzWith 1 G) {L : ℝ} (hL : 0 ≤ L)
    (hzero : lipSignature G hG 0 L hL = unitSeries) :
    LipschitzWith 1 (normalizedLoopLift G hG hL hzero) := by
  simpa only [one_mul] using!
    ((normalizedLoopRoute G hG hL hzero).prefixPoint_lipschitz (lipSignatureImage_isClosed G hG hL)).comp
      (LipschitzWith.projIcc hL)

theorem normalizedLoopLift_value {ι : Type*} [Fintype ι] (G : ℝ → ι → ℝ)
    (hG : LipschitzWith 1 G) {L : ℝ} (hL : 0 ≤ L)
    (hzero : lipSignature G hG 0 L hL = unitSeries) {t : ℝ} (ht : t ∈ Icc 0 L) :
    (normalizedLoopLift G hG hL hzero t).value = lipSignature G hG 0 t ht.1 := by
  change ((normalizedLoopRoute G hG hL hzero).prefixPoint _ (projIcc 0 L hL t)).value = _
  rw [projIcc_of_mem hL ht]
  change product unitSeries (lipSignature (normalizedLoopRoute G hG hL hzero).curve
    (normalizedLoopRoute G hG hL hzero).lipschitz 0 t ht.1) = _
  rw [product_unit_left, normalizedLoopRoute_prefix G hG hL hzero ht.1]

theorem normalizedLoopLift_closed {ι : Type*} [Fintype ι] (G : ℝ → ι → ℝ)
    (hG : LipschitzWith 1 G) {L : ℝ} (hL : 0 ≤ L)
    (hzero : lipSignature G hG 0 L hL = unitSeries) :
    normalizedLoopLift G hG hL hzero 0 = normalizedLoopLift G hG hL hzero L := by
  apply IntrinsicPoint.ext
  rw [normalizedLoopLift_value G hG hL hzero ⟨le_rfl, hL⟩,
    normalizedLoopLift_value G hG hL hzero ⟨hL, le_rfl⟩, hzero, lipSignature_same]

/-- Trivial full signature gives an independent geometric tree height for
an actual globally 1-Lipschitz coordinate curve. All metric hypotheses are discharged
by the constructed intrinsic signature space and its four-point theorem. -/
theorem treeLike_of_lipSignature_eq_unit {ι : Type*} [Fintype ι]
    (G : ℝ → ι → ℝ) (hG : LipschitzWith 1 G) {L : ℝ} (hL : 0 ≤ L)
    (hzero : lipSignature G hG 0 L hL = unitSeries) : TreeLike G 0 L := by
  exact treeLike_of_realized_signature_metric G hG hL hzero
    (F := IntrinsicPoint (lipSignatureImage G hG L hL) (lipSignatureImage_isClosed G hG hL) unitSeries)
    (LinearInputCurveWordBVIntrinsicTree.intrinsic_fourPoint (lipSignatureImage_isClosed G hG hL) (by rfl))
    IntrinsicPoint.value IntrinsicPoint.value_injective (firstLevel_lipschitz (by rfl))
    (normalizedLoopLift G hG hL hzero)
    (normalizedLoopLift_lipschitz G hG hL hzero).continuous.continuousOn
    (fun _ ht => normalizedLoopLift_value G hG hL hzero ht)

/-- Hambly--Lyons necessity for continuous BV curves in a finite real
coordinate space with its usual Pi sup norm. The signature is the canonical
actual Stieltjes signature; the conclusion is the independent height
definition of tree-likeness. -/
theorem treeLike_of_pathSignature_eq_unit {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hzero : pathSignature γ hab hγ hc = unitSeries) : TreeLike γ a b := by
  obtain ⟨G, hG, _, _, hfac, hprefix, _⟩ := canonicalPrefix_arcLength_factorization γ hab hγ hc
  have he := hprefix ⟨b, hab, le_rfl⟩
  rw [canonicalPrefix_terminal] at he
  have hend := he.trans (lipSignature_endpoint_congr G hG _ ENNReal.toReal_nonneg
    (variationClock_terminal γ hab))
  have hGzero : lipSignature G hG 0 (variationLength γ a b) ENNReal.toReal_nonneg = unitSeries :=
    hend.symm.trans hzero
  exact treeLike_of_arcLength_factor hab hγ hc hfac
    (treeLike_of_lipSignature_eq_unit G hG ENNReal.toReal_nonneg hGzero)

/-- The full equivalence uses independently constructed geometric tree
heights and actual all-degree canonical Stieltjes signatures. -/
theorem treeLike_iff_pathSignature_eq_unit {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    TreeLike γ a b ↔ pathSignature γ hab hγ hc = unitSeries := by
  constructor
  · intro ht
    exact LinearInputCurveWordTreeLimit.treeLike_pathSignature_eq_unit γ hab hγ ht
  · exact treeLike_of_pathSignature_eq_unit γ hab hγ hc

end LinearInputCurveWordBVHamblyLyons
