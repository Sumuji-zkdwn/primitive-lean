/-!
Compactness and variation minimization for actual bounded-speed curves.
This supplies a construction step for reduced signature representatives;
it does not identify arbitrary arcs of a signature image with subintervals.
-/

noncomputable section
namespace LinearInputCurveWordBVCompactness
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
open LinearInputCurveWordBoundedVariation LinearInputCurveWordBVCanonical
open LinearInputCurveWordSignatureUniform

def speedControlledPaths {E : Type*} [MetricSpace E] (L : ℝ) (hL : 0 ≤ L)
    (x : E) : Set (Icc (0 : ℝ) L →ᵇ E) :=
  {f | LipschitzWith 1 f ∧ f ⟨0, le_rfl, hL⟩ = x}

theorem speedControlledPaths_isClosed {E : Type*} [MetricSpace E]
    (L : ℝ) (hL : 0 ≤ L) (x : E) : IsClosed (speedControlledPaths L hL x) := by
  have hlip : IsClosed {f : Icc (0 : ℝ) L →ᵇ E | LipschitzWith 1 f} :=
    (isClosed_setOfPred_lipschitzWith (α := Icc (0 : ℝ) L) (β := E) 1).preimage
      (BoundedContinuousFunction.continuous_coe (α := Icc (0 : ℝ) L) (β := E))
  have hstart : Continuous (fun f : Icc (0 : ℝ) L →ᵇ E => f ⟨0, le_rfl, hL⟩) :=
    continuous_eval_const _
  exact hlip.inter (isClosed_eq hstart continuous_const)

theorem speedControlledPaths_equicontinuous {E : Type*} [MetricSpace E]
    (L : ℝ) (hL : 0 ≤ L) (x : E) :
    Equicontinuous (fun f : speedControlledPaths L hL x => (f.val : Icc (0 : ℝ) L → E)) := by
  apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => r) tendsto_id
  intro s t f
  simpa only [NNReal.coe_one, one_mul] using f.property.1.dist_le_mul s t

theorem speedControlledPaths_isCompact {E : Type*} [MetricSpace E] [ProperSpace E]
    (L : ℝ) (hL : 0 ≤ L) (x : E) : IsCompact (speedControlledPaths L hL x) := by
  apply BoundedContinuousFunction.arzela_ascoli₂ (Metric.closedBall x L)
    (isCompact_closedBall x L) _ (speedControlledPaths_isClosed L hL x)
  · intro f t hf
    rw [Metric.mem_closedBall, ← hf.2]
    have hd := hf.1.dist_le_mul t ⟨0, le_rfl, hL⟩
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq,
      sub_zero, abs_of_nonneg t.property.1] at hd
    exact hd.trans t.property.2
  · exact speedControlledPaths_equicontinuous L hL x

def pathExtension {E : Type*} [MetricSpace E] {L : ℝ} (hL : 0 ≤ L)
    (f : Icc (0 : ℝ) L →ᵇ E) : ℝ → E := fun t => f (projIcc 0 L hL t)

theorem pathExtension_lipschitz {E : Type*} [MetricSpace E] {L : ℝ} (hL : 0 ≤ L)
    (f : Icc (0 : ℝ) L →ᵇ E) (hf : LipschitzWith 1 f) :
    LipschitzWith 1 (pathExtension hL f) := by
  simpa only [one_mul] using! hf.comp (LipschitzWith.projIcc hL)

theorem pathExtension_continuous {E : Type*} [MetricSpace E] {L : ℝ} (hL : 0 ≤ L)
    (f : Icc (0 : ℝ) L →ᵇ E) : Continuous (pathExtension hL f) :=
  f.continuous.comp continuous_projIcc

theorem pathExtension_boundedVariation_interval {E : Type*} [MetricSpace E]
    {L : ℝ} (hL : 0 ≤ L) (f : Icc (0 : ℝ) L →ᵇ E) (hf : LipschitzWith 1 f) :
    BoundedVariationOn (pathExtension hL f) (Icc 0 L) := by
  simpa only [inter_self] using ((pathExtension_lipschitz hL f hf).locallyBoundedVariationOn
    (Icc 0 L)) 0 L ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩

theorem pathExtension_clamp {E : Type*} [MetricSpace E] {L : ℝ} (hL : 0 ≤ L)
    (f : Icc (0 : ℝ) L →ᵇ E) : pathExtension hL f ∘ clamp 0 L = pathExtension hL f := by
  funext t
  exact congrArg f (projIcc_val hL (projIcc 0 L hL t))

theorem pathExtension_boundedVariation {E : Type*} [MetricSpace E] {L : ℝ}
    (hL : 0 ≤ L) (f : Icc (0 : ℝ) L →ᵇ E) (hf : LipschitzWith 1 f) :
    BoundedVariationOn (pathExtension hL f) univ := by
  have he := constantExtension_boundedVariation hL (pathExtension_boundedVariation_interval hL f hf)
  rwa [pathExtension_clamp] at he

theorem pathExtension_variation_lowerSemicontinuous {E : Type*} [MetricSpace E]
    {L : ℝ} (hL : 0 ≤ L) :
    LowerSemicontinuous (fun f : Icc (0 : ℝ) L →ᵇ E =>
      eVariationOn (pathExtension hL f) (Icc 0 L)) := by
  intro f v hv
  apply eVariationOn.lowerSemicontinuous_aux (fun t _ => ?_) hv
  exact (continuous_eval_const (projIcc 0 L hL t)).continuousAt

/-- Every nonempty closed class of bounded-speed paths has an actual
variation-minimizing member. Closedness is later discharged for the concrete
signature and signature-range constraints using signature continuity. -/
theorem exists_minimal_variation_in_closed_class {E : Type*} [MetricSpace E] [ProperSpace E]
    {L : ℝ} (hL : 0 ≤ L) (x : E)
    (A : Set (Icc (0 : ℝ) L →ᵇ E)) (hA : IsClosed A)
    (hsub : A ⊆ speedControlledPaths L hL x) (hne : A.Nonempty) :
    ∃ f ∈ A, ∀ g ∈ A,
      eVariationOn (pathExtension hL f) (Icc 0 L) ≤
        eVariationOn (pathExtension hL g) (Icc 0 L) := by
  exact ((pathExtension_variation_lowerSemicontinuous hL).lowerSemicontinuousOn A).exists_isMinOn
    hne ((speedControlledPaths_isCompact L hL x).of_isClosed_subset hA hsub)

theorem lipschitz_variation_le {E : Type*} [MetricSpace E] {g : ℝ → E}
    (hg : LipschitzWith 1 g) {r : ℝ} (_hr : 0 ≤ r) :
    eVariationOn g (Icc 0 r) ≤ ENNReal.ofReal r := by
  have hi : eVariationOn (id : ℝ → ℝ) (Icc 0 r) ≤ ENNReal.ofReal r := by
    simpa only [univ_inter, id_eq, sub_zero] using
      ((monotone_id.monotoneOn univ).eVariationOn_eq (a := 0) (b := r) (mem_univ _) (mem_univ _)).le
  have he := hg.lipschitzOnWith.comp_eVariationOn_le (g := id)
    (s := Icc 0 r) (mapsTo_univ id (Icc 0 r))
  simp only [Function.comp_id, ENNReal.coe_one, one_mul] at he
  exact he.trans hi

theorem coordinateExtension_boundedVariation {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 ≤ L) (f : Icc (0 : ℝ) L →ᵇ (ι → ℝ)) (hf : LipschitzWith 1 f) (i : ι) :
    BoundedVariationOn (fun t => pathExtension hL f t i) univ :=
  (LipschitzWith.eval i).comp_boundedVariationOn (pathExtension_boundedVariation hL f hf)

theorem coordinateExtension_continuous {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 ≤ L) (f : Icc (0 : ℝ) L →ᵇ (ι → ℝ)) (i : ι) :
    Continuous (fun t => pathExtension hL f t i) :=
  (continuous_apply i).comp (pathExtension_continuous hL f)

theorem coordinateExtension_variation_le {ι : Type*} [Fintype ι] {L r : ℝ}
    (hL : 0 ≤ L) (f : Icc (0 : ℝ) L →ᵇ (ι → ℝ)) (hf : LipschitzWith 1 f)
    (hr : r ∈ Icc 0 L) (i : ι) :
    (eVariationOn (fun t => pathExtension hL f t i) (Icc 0 r)).toReal ≤ L := by
  have hlip : LipschitzWith 1 (fun t => pathExtension hL f t i) := by
    simpa only [one_mul] using! (LipschitzWith.eval i).comp (pathExtension_lipschitz hL f hf)
  have he := lipschitz_variation_le hlip hr.1
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans (by simpa [ENNReal.toReal_ofReal hr.1] using hr.2)

def prefixSignature {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) (x : ι → ℝ)
    (f : speedControlledPaths L hL x) (r : ℝ) : List ι → ℝ :=
  bvSignature (fun i t => pathExtension hL f.val t i)
    (coordinateExtension_boundedVariation hL f.val f.property.1)
    (coordinateExtension_continuous hL f.val) 0 r

/-- Actual signature coefficients vary continuously on the compact class of
bounded-speed curves. The uniform BV bound is derived from the speed bound. -/
theorem prefixSignature_continuous {ι : Type*} [Fintype ι] {L r : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (hr : r ∈ Icc 0 L) :
    Continuous (fun f : speedControlledPaths L hL x => prefixSignature hL x f r) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  apply bvSignature_tendsto_of_uniform_convergence
    (fun (g : speedControlledPaths L hL x) i t => pathExtension hL g.val t i)
    (fun i t => pathExtension hL f.val t i)
    (fun g => coordinateExtension_boundedVariation hL g.val g.property.1)
    (fun g => coordinateExtension_continuous hL g.val)
    (coordinateExtension_boundedVariation hL f.val f.property.1)
    (coordinateExtension_continuous hL f.val) 0 r
    (1 + 2 * (Fintype.card ι : ℝ) * L) hr.1 (by
      have hn : 0 ≤ 2 * (Fintype.card ι : ℝ) * L := by positivity
      linarith)
  · intro g
    have hfbound : (∑ i, (eVariationOn (fun t => pathExtension hL f.val t i) (Icc 0 r)).toReal) ≤
        (Fintype.card ι : ℝ) * L := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => coordinateExtension_variation_le hL f.val f.property.1 hr i)
    have hgbound : (∑ i, (eVariationOn (fun t => pathExtension hL g.val t i) (Icc 0 r)).toReal) ≤
        (Fintype.card ι : ℝ) * L := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => coordinateExtension_variation_le hL g.val g.property.1 hr i)
    linarith
  · intro i
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have he := Metric.tendsto_nhds.mp
      (continuous_subtype_val.continuousAt : Tendsto (fun g : speedControlledPaths L hL x => g.val)
        (𝓝 f) (𝓝 f.val)) ε hε
    filter_upwards [he] with g hg
    intro t _
    have hcoord := (LipschitzWith.eval i).dist_le_mul
      (pathExtension hL f.val t) (pathExtension hL g.val t)
    simp only [NNReal.coe_one, one_mul] at hcoord
    apply lt_of_le_of_lt (hcoord.trans (BoundedContinuousFunction.dist_coe_le_dist (projIcc 0 L hL t)))
    simpa only [dist_comm] using hg

/-- The usual Chen left product fixes the starting signature point. -/
def basedPrefixSignature {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) (x : ι → ℝ)
    (P : List ι → ℝ) (f : speedControlledPaths L hL x) (r : ℝ) (w : List ι) : ℝ :=
  ∑ k ∈ Finset.range (w.length + 1), P (w.take k) * prefixSignature hL x f r (w.drop k)

theorem basedPrefixSignature_continuous {ι : Type*} [Fintype ι] {L r : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (P : List ι → ℝ) (hr : r ∈ Icc 0 L) :
    Continuous (fun f : speedControlledPaths L hL x => basedPrefixSignature hL x P f r) := by
  apply continuous_pi
  intro w
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul ((continuous_apply (w.drop k)).comp (prefixSignature_continuous hL x hr))

def signatureRangeClass {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (P Q : List ι → ℝ) (K : Set (List ι → ℝ)) :
    Set (speedControlledPaths L hL x) :=
  {f | basedPrefixSignature hL x P f L = Q ∧
    ∀ r : Icc (0 : ℝ) L, basedPrefixSignature hL x P f r.val ∈ K}

/-- Endpoint and all intermediate signature-range constraints are closed,
as a consequence of actual signature continuity, not an extra hypothesis. -/
theorem signatureRangeClass_isClosed {ι : Type*} [Fintype ι] {L : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (P Q : List ι → ℝ)
    {K : Set (List ι → ℝ)} (hK : IsClosed K) :
    IsClosed (signatureRangeClass hL x P Q K) := by
  have he : IsClosed {f : speedControlledPaths L hL x | basedPrefixSignature hL x P f L = Q} :=
    isClosed_eq (basedPrefixSignature_continuous hL x P ⟨hL, le_rfl⟩) continuous_const
  have hr : IsClosed {f : speedControlledPaths L hL x |
      ∀ r : Icc (0 : ℝ) L, basedPrefixSignature hL x P f r.val ∈ K} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun r => hK.preimage (basedPrefixSignature_continuous hL x P r.property))
  exact he.inter hr

/-- An actual least-variation representative exists among bounded-speed
curves whose whole based signature lift remains in a prescribed closed set.
The supplied curve is the nonemptiness witness; endpoint and range closedness
are proved above from uniform convergence with a uniform variation bound. -/
theorem exists_minimal_signature_range_representative {ι : Type*} [Fintype ι]
    {L : ℝ} (hL : 0 ≤ L) (x : ι → ℝ) (P Q : List ι → ℝ)
    {K : Set (List ι → ℝ)} (hK : IsClosed K)
    (f : speedControlledPaths L hL x) (hf : f ∈ signatureRangeClass hL x P Q K) :
    ∃ g : speedControlledPaths L hL x,
      g ∈ signatureRangeClass hL x P Q K ∧
      ∀ h : speedControlledPaths L hL x, h ∈ signatureRangeClass hL x P Q K →
        eVariationOn (pathExtension hL g.val) (Icc 0 L) ≤
          eVariationOn (pathExtension hL h.val) (Icc 0 L) := by
  let : CompactSpace (speedControlledPaths L hL x) :=
    isCompact_iff_compactSpace.mp (speedControlledPaths_isCompact L hL x)
  have hlsc : LowerSemicontinuous (fun g : speedControlledPaths L hL x =>
      eVariationOn (pathExtension hL g.val) (Icc 0 L)) :=
    (pathExtension_variation_lowerSemicontinuous hL).comp continuous_subtype_val
  exact (hlsc.lowerSemicontinuousOn _).exists_isMinOn ⟨f, hf⟩
    (signatureRangeClass_isClosed hL x P Q hK).isCompact

/-- A supplied actual Lipschitz curve is an explicit member of the compact
path class; no existence or choice assumption is needed for nonemptiness. -/
def speedControlledOfLipschitz {E : Type*} [MetricSpace E] {L : ℝ} (hL : 0 ≤ L)
    (γ : ℝ → E) (hγ : LipschitzWith 1 γ) : speedControlledPaths L hL (γ 0) :=
  ⟨BoundedContinuousFunction.mkOfCompact
    ⟨fun t : Icc (0 : ℝ) L => γ t.val, hγ.continuous.comp continuous_subtype_val⟩,
    by
      constructor
      · simpa only [one_mul] using! hγ.comp (LipschitzWith.subtype_val (Icc (0 : ℝ) L))
      · rfl⟩

theorem speedControlledOfLipschitz_eq {E : Type*} [MetricSpace E] {L : ℝ} (hL : 0 ≤ L)
    (γ : ℝ → E) (hγ : LipschitzWith 1 γ) :
    EqOn (pathExtension hL (speedControlledOfLipschitz hL γ hγ).val) γ (Icc 0 L) := by
  intro t ht
  change γ (projIcc 0 L hL t).val = γ t
  rw [projIcc_of_mem hL ht]

/-- The compact-class prefix is the previously defined canonical signature
of its actual finite-dimensional curve, at every intermediate time. -/
theorem prefixSignature_eq_pathSignature {ι : Type*} [Fintype ι] {L r : ℝ}
    (hL : 0 ≤ L) (x : ι → ℝ) (f : speedControlledPaths L hL x) (hr : 0 ≤ r) :
    prefixSignature hL x f r =
      pathSignature (pathExtension hL f.val) hr
        ((pathExtension_boundedVariation hL f.val f.property.1).mono (subset_univ _))
        (pathExtension_continuous hL f.val).continuousOn := by
  funext w
  symm
  unfold prefixSignature bvSignature
  apply pathSignature_eq_representation (pathExtension hL f.val) hr
    ((pathExtension_boundedVariation hL f.val f.property.1).mono (subset_univ _))
    (pathExtension_continuous hL f.val).continuousOn
    (fun i => LinearInputCurveWordStieltjes.bvPositive
      (coordinateExtension_boundedVariation hL f.val f.property.1 i)
      (coordinateExtension_continuous hL f.val i) 0)
    (fun i => LinearInputCurveWordStieltjes.bvNegative
      (coordinateExtension_boundedVariation hL f.val f.property.1 i)
      (coordinateExtension_continuous hL f.val i) 0)
    (fun i => (LinearInputCurveWordStieltjes.jordan_continuous
      (coordinateExtension_boundedVariation hL f.val f.property.1 i)
      (coordinateExtension_continuous hL f.val i) 0).1)
    (fun i => (LinearInputCurveWordStieltjes.jordan_continuous
      (coordinateExtension_boundedVariation hL f.val f.property.1 i)
      (coordinateExtension_continuous hL f.val i) 0).2)
  intro i s _ t _
  have hs := LinearInputCurveWordStieltjes.jordan_difference
    (fun u => pathExtension hL f.val u i) 0 s
  have ht := LinearInputCurveWordStieltjes.jordan_difference
    (fun u => pathExtension hL f.val u i) 0 t
  change (LinearInputCurveWordStieltjes.jordanPositive (fun u => pathExtension hL f.val u i) 0 t -
      LinearInputCurveWordStieltjes.jordanPositive (fun u => pathExtension hL f.val u i) 0 s) -
    (LinearInputCurveWordStieltjes.jordanNegative (fun u => pathExtension hL f.val u i) 0 t -
      LinearInputCurveWordStieltjes.jordanNegative (fun u => pathExtension hL f.val u i) 0 s) = _
  linarith

end LinearInputCurveWordBVCompactness
