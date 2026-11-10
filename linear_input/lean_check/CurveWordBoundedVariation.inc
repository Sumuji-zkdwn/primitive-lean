/-!
Arc-length factorization of continuous bounded-variation curves.
The clock is the actual total variation; flat portions are collapsed using
the variation bound on endpoint distance, not an injectivity hypothesis.
-/

noncomputable section

namespace LinearInputCurveWordBoundedVariation

open Set Filter
open scoped Topology NNReal

theorem distance_le_variation_difference {E : Type*} [PseudoMetricSpace E]
    {f : ℝ → E} {s : Set ℝ} (hf : LocallyBoundedVariationOn f s)
    {a x y : ℝ} (ha : a ∈ s) (hx : x ∈ s) (hy : y ∈ s) :
    dist (f x) (f y) ≤
      |variationOnFromTo f s a y - variationOnFromTo f s a x| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [dist_comm, abs_sub_comm]
    exact this hy hx (le_of_not_ge hxy)
  have hdist := (hf x y hx hy).dist_le ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
  rw [← variationOnFromTo.eq_of_le f s hxy] at hdist
  have hadd := variationOnFromTo.add hf ha hx hy
  have hnonneg := variationOnFromTo.nonneg_of_le f s hxy
  rw [← hadd, add_sub_cancel_left, abs_of_nonneg hnonneg]
  exact hdist

theorem equal_of_variation_clock_eq {E : Type*} [MetricSpace E]
    {f : ℝ → E} {s : Set ℝ} (hf : LocallyBoundedVariationOn f s)
    {a x y : ℝ} (ha : a ∈ s) (hx : x ∈ s) (hy : y ∈ s)
    (he : variationOnFromTo f s a x = variationOnFromTo f s a y) : f x = f y := by
  apply dist_eq_zero.mp
  have hd := distance_le_variation_difference hf ha hx hy
  rw [he, sub_self, abs_zero] at hd
  exact le_antisymm hd dist_nonneg

/-- Descent to the variation range works even for discontinuous BV curves;
continuity is used below to show that this range is the entire length interval. -/
theorem exists_lipschitz_factor_on_variation_range {E : Type*} [MetricSpace E]
    {f : ℝ → E} {s : Set ℝ} (hf : LocallyBoundedVariationOn f s)
    {a : ℝ} (ha : a ∈ s) :
    ∃ g : range (fun x : s => variationOnFromTo f s a x) → E,
      LipschitzWith 1 g ∧
        ∀ x : s, g ⟨variationOnFromTo f s a x, mem_range_self x⟩ = f x := by
  let pick (v : range (fun x : s => variationOnFromTo f s a x)) : s :=
    Classical.choose v.property
  have hp (v : range (fun x : s => variationOnFromTo f s a x)) :
      variationOnFromTo f s a (pick v) = v := Classical.choose_spec v.property
  refine ⟨fun v => f (pick v), LipschitzWith.of_dist_le_mul ?_, ?_⟩
  · intro v w
    have hd := distance_le_variation_difference hf ha (pick v).property (pick w).property
    rw [hp v, hp w] at hd
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using hd
  · intro x
    apply equal_of_variation_clock_eq hf ha (pick _).property x.property
    exact hp _

theorem variation_clock_continuousOn {E : Type*} [MetricSpace E]
    {f : ℝ → E} {s : Set ℝ} (hf : BoundedVariationOn f s) (hc : ContinuousOn f s)
    {a : ℝ} (ha : a ∈ s) : ContinuousOn (variationOnFromTo f s a) s := by
  intro x hx
  have hleft := hf.tendsto_eVariationOn_Icc_zero_left ((hc x hx).mono inter_subset_left)
  have hright := hf.tendsto_eVariationOn_Icc_zero_right x ((hc x hx).mono inter_subset_left)
  have hleftR := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hleft
  have hrightR := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hright
  have hbound : ∀ᶠ y in 𝓝[s] x,
      dist (variationOnFromTo f s a y) (variationOnFromTo f s a x) ≤
        (eVariationOn f (s ∩ Icc y x)).toReal +
          (eVariationOn f (s ∩ Icc x y)).toReal := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [Real.dist_eq, ← variationOnFromTo.add hf.locallyBoundedVariationOn ha hx hy,
      add_sub_cancel_left]
    rcases le_total x y with hxy | hyx
    · rw [variationOnFromTo.eq_of_le f s hxy, abs_of_nonneg ENNReal.toReal_nonneg]
      exact le_add_of_nonneg_left ENNReal.toReal_nonneg
    · rw [variationOnFromTo.eq_of_ge f s hyx, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg]
      exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) hbound
  simpa only [ENNReal.toReal_zero, zero_add] using hleftR.add hrightR

def variationClock {E : Type*} [PseudoEMetricSpace E] (f : ℝ → E) (a b : ℝ) : ℝ → ℝ :=
  variationOnFromTo f (Icc a b) a

def variationLength {E : Type*} [PseudoEMetricSpace E] (f : ℝ → E) (a b : ℝ) : ℝ :=
  (eVariationOn f (Icc a b)).toReal

theorem variationClock_initial {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ → E) (a b : ℝ) : variationClock f a b a = 0 :=
  variationOnFromTo.self f (Icc a b) a

theorem variationClock_terminal {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    variationClock f a b b = variationLength f a b := by
  rw [variationClock, variationOnFromTo.eq_of_le f (Icc a b) hab, inter_self]
  rfl

theorem variationClock_monotoneOn {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : BoundedVariationOn f (Icc a b)) :
    MonotoneOn (variationClock f a b) (Icc a b) :=
  variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn ⟨le_rfl, hab⟩

theorem variationClock_image {E : Type*} [MetricSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hc : ContinuousOn f (Icc a b)) :
    variationClock f a b '' Icc a b = Icc 0 (variationLength f a b) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hm := variationClock_monotoneOn hab hf
    constructor
    · simpa only [variationClock_initial] using hm ⟨le_rfl, hab⟩ hx hx.1
    · simpa only [variationClock_terminal f hab] using hm hx ⟨hab, le_rfl⟩ hx.2
  · have hv : ContinuousOn (variationClock f a b) (Icc a b) :=
      variation_clock_continuousOn hf hc ⟨le_rfl, hab⟩
    simpa only [variationClock_initial, variationClock_terminal f hab] using
      intermediate_value_Icc hab hv

theorem variationClock_mem {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {a b x : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hx : x ∈ Icc a b) :
    variationClock f a b x ∈ Icc 0 (variationLength f a b) := by
  have hm := variationClock_monotoneOn hab hf
  constructor
  · simpa only [variationClock_initial] using hm ⟨le_rfl, hab⟩ hx hx.1
  · simpa only [variationClock_terminal f hab] using hm hx ⟨hab, le_rfl⟩ hx.2

def variationParameter {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : BoundedVariationOn f (Icc a b)) :
    Icc a b → Icc 0 (variationLength f a b) :=
  fun t => ⟨variationClock f a b t, variationClock_mem hab hf t.property⟩

theorem variationParameter_monotone {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : BoundedVariationOn f (Icc a b)) :
    Monotone (variationParameter hab hf) := by
  intro x y hxy
  exact variationClock_monotoneOn hab hf x.property y.property hxy

theorem variationParameter_continuous {E : Type*} [MetricSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hc : ContinuousOn f (Icc a b)) :
    Continuous (variationParameter hab hf) := by
  have hv := variation_clock_continuousOn hf hc (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
  exact hv.restrict.subtype_mk _

theorem variationParameter_surjective {E : Type*} [MetricSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hc : ContinuousOn f (Icc a b)) :
    Function.Surjective (variationParameter hab hf) := by
  intro v
  have hv : v.val ∈ variationClock f a b '' Icc a b := by
    rw [variationClock_image hab hf hc]
    exact v.property
  obtain ⟨x, hx, hval⟩ := hv
  refine ⟨⟨x, hx⟩, Subtype.ext hval⟩

/-- Every continuous BV curve on a closed interval is the composition of a
1-Lipschitz curve on its actual length interval and its continuous, monotone,
surjective variation clock. No strict increase of that clock is required. -/
theorem arcLength_factorization {E : Type*} [MetricSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hc : ContinuousOn f (Icc a b)) :
    ∃ g : Icc 0 (variationLength f a b) → E,
      LipschitzWith 1 g ∧ ∀ t : Icc a b, g (variationParameter hab hf t) = f t := by
  have hsur := variationParameter_surjective hab hf hc
  let pick (v : Icc 0 (variationLength f a b)) : Icc a b := Classical.choose (hsur v)
  have hp (v : Icc 0 (variationLength f a b)) : variationParameter hab hf (pick v) = v :=
    Classical.choose_spec (hsur v)
  have hpval (v : Icc 0 (variationLength f a b)) :
      variationClock f a b (pick v) = v := congrArg Subtype.val (hp v)
  refine ⟨fun v => f (pick v), LipschitzWith.of_dist_le_mul ?_, ?_⟩
  · intro v w
    have hd := distance_le_variation_difference hf.locallyBoundedVariationOn
      (show a ∈ Icc a b from ⟨le_rfl, hab⟩) (pick v).property (pick w).property
    change dist _ _ ≤ |variationClock f a b (pick w) - variationClock f a b (pick v)| at hd
    rw [hpval, hpval] at hd
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using hd
  · intro t
    apply equal_of_variation_clock_eq hf.locallyBoundedVariationOn
      (show a ∈ Icc a b from ⟨le_rfl, hab⟩) (pick _).property t.property
    exact hpval _

theorem boundedVariationOn_of_continuous_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E}
    {a b : ℝ} (hab : a ≤ b) (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Icc a b)) : BoundedVariationOn f (Icc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc.nnnorm
  have hl : LipschitzOnWith C f (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (hd t ht).hasDerivWithinAt) (fun t ht => hC (mem_image_of_mem _ ht))
  simpa only [inter_self] using hl.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩

theorem variation_monotone_surjection {α β E : Type*} [LinearOrder α] [LinearOrder β]
    [PseudoEMetricSpace E] (g : α → E) (φ : β → α)
    (hφ : Monotone φ) (hsur : Function.Surjective φ) :
    eVariationOn (g ∘ φ) univ = eVariationOn g univ := by
  rw [eVariationOn.comp_eq_of_monotoneOn g φ (hφ.monotoneOn univ), image_univ, hsur.range_eq]

theorem factor_preserves_variation {E : Type*} [MetricSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hc : ContinuousOn f (Icc a b))
    (g : Icc 0 (variationLength f a b) → E)
    (hfactor : ∀ t : Icc a b, g (variationParameter hab hf t) = f t) :
    eVariationOn g univ = eVariationOn f (Icc a b) := by
  rw [← variation_monotone_surjection g (variationParameter hab hf)
    (variationParameter_monotone hab hf) (variationParameter_surjective hab hf hc)]
  have he : (g ∘ variationParameter hab hf) = f ∘ (Subtype.val : Icc a b → ℝ) :=
    funext hfactor
  rw [he, eVariationOn.comp_eq_of_monotoneOn f Subtype.val
    (show MonotoneOn (Subtype.val : Icc a b → ℝ) univ from fun _ _ _ _ h => h)]
  simp only [image_univ, Subtype.range_coe]

theorem arcLength_factorization_with_length {E : Type*} [MetricSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hc : ContinuousOn f (Icc a b)) :
    ∃ g : Icc 0 (variationLength f a b) → E,
      LipschitzWith 1 g ∧
        (∀ t : Icc a b, g (variationParameter hab hf t) = f t) ∧
        (eVariationOn g univ).toReal = variationLength f a b := by
  obtain ⟨g, hLip, hfactor⟩ := arcLength_factorization hab hf hc
  refine ⟨g, hLip, hfactor, ?_⟩
  rw [factor_preserves_variation hab hf hc g hfactor]
  rfl

def clamp (a b t : ℝ) : ℝ := max a (min b t)

theorem clamp_mem {a b : ℝ} (hab : a ≤ b) (t : ℝ) : clamp a b t ∈ Icc a b := by
  exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clamp_eq {a b t : ℝ} (ht : t ∈ Icc a b) : clamp a b t = t := by
  simp [clamp, min_eq_right ht.2, max_eq_right ht.1]

theorem clamp_monotone (a b : ℝ) : Monotone (clamp a b) := by
  intro s t hst
  exact max_le_max_left a (min_le_min_left b hst)

theorem clamp_continuous (a b : ℝ) : Continuous (clamp a b) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem constantExtension_boundedVariation {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : BoundedVariationOn f (Icc a b)) :
    BoundedVariationOn (f ∘ clamp a b) univ := by
  apply ne_top_of_le_ne_top hf
  exact eVariationOn.comp_le_of_monotoneOn f (clamp a b) ((clamp_monotone a b).monotoneOn univ)
    (fun t _ => clamp_mem hab t)

theorem constantExtension_continuous {E : Type*} [TopologicalSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) :
    Continuous (f ∘ clamp a b) :=
  hc.comp_continuous (clamp_continuous a b) (fun t => clamp_mem hab t)

end LinearInputCurveWordBoundedVariation
