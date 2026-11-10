/-!
Intrinsic travel time of actual bounded-speed signature lifts.  The path
class and its stopping condition are explicit; compactness is used to
construct shortest admissible representatives. The resulting reachable
component has an actual metric and geodesics, and the distance equals
the minimum variation of its actual admissible coordinate curves.
-/

noncomputable section

namespace LinearInputCurveWordBVIntrinsic

open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
open LinearInputCurveWordFormalSeries LinearInputCurveWordBVCanonical
open LinearInputCurveWordBVCompactness LinearInputCurveWordBVPathOperations
open LinearInputCurveWordBVLoopErase LinearInputCurveWordBoundedVariation
open LinearInputCurveWordTreeLike LinearInputCurveWordTreeLimit
open LinearInputCurveWordStieltjes LinearInputCurveWordBVOrientation

/-- A stopped curve is encoded by a time and a bounded-speed curve on one
fixed compact interval.  The `max` equation makes closedness explicit even
when the stopping time varies. -/
def stoppedClass {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L) (x : ι → ℝ)
    (P Q : Series ι) (K : Set (Series ι)) :
    Set (Icc (0 : ℝ) L × speedControlledPaths L hL x) :=
  {z | z.2 ∈ signatureRangeClass hL x P Q K ∧
    ∀t : Icc (0 : ℝ) L, z.2.val (max z.1 t) = z.2.val z.1}

theorem stoppedClass_isClosed {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L)
    (x : ι → ℝ) (P Q : Series ι) {K : Set (Series ι)} (hK : IsClosed K) :
    IsClosed (stoppedClass hL x P Q K) := by
  have hf : Continuous (fun z : Icc (0 : ℝ) L × speedControlledPaths L hL x => z.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have he : IsClosed {z : Icc (0 : ℝ) L × speedControlledPaths L hL x |
      ∀t : Icc (0 : ℝ) L, z.2.val (max z.1 t) = z.2.val z.1} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun t => isClosed_eq (hf.eval (continuous_fst.max continuous_const))
      (hf.eval continuous_fst))
  exact ((signatureRangeClass_isClosed hL x P Q hK).preimage continuous_snd).inter he

/-- The original endpoint is always an admissible stopping time. -/
theorem terminal_mem_stoppedClass {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L)
    (x : ι → ℝ) (P Q : Series ι) (K : Set (Series ι))
    (f : speedControlledPaths L hL x) (hf : f ∈ signatureRangeClass hL x P Q K) :
    (⟨L, hL, le_rfl⟩, f) ∈ stoppedClass hL x P Q K := by
  refine ⟨hf, ?_⟩
  intro t
  rw [max_eq_left (show t ≤ (⟨L, hL, le_rfl⟩ : Icc (0 : ℝ) L) from t.property.2)]

/-- A genuine least stopping time exists in every nonempty closed
signature-range class, by compactness of curves and stopping times. -/
theorem exists_minimal_stopping_time {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L)
    (x : ι → ℝ) (P Q : Series ι) {K : Set (Series ι)} (hK : IsClosed K)
    (f : speedControlledPaths L hL x) (hf : f ∈ signatureRangeClass hL x P Q K) :
    ∃ z ∈ stoppedClass hL x P Q K,
      ∀w ∈ stoppedClass hL x P Q K, (z.1 : ℝ) ≤ (w.1 : ℝ) := by
  letI : CompactSpace (speedControlledPaths L hL x) :=
    isCompact_iff_compactSpace.mp (speedControlledPaths_isCompact L hL x)
  exact (stoppedClass_isClosed hL x P Q hK).isCompact.exists_isMinOn
    ⟨(⟨L, hL, le_rfl⟩, f), terminal_mem_stoppedClass hL x P Q K f hf⟩
    (continuous_subtype_val.comp continuous_fst).continuousOn

theorem lipSignature_same {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    (hγ : LipschitzWith 1 γ) (a : ℝ) : lipSignature γ hγ a a le_rfl = unitSeries :=
  stieltjesSignature_same _ _ a

theorem constant_lipschitz {E : Type*} [PseudoMetricSpace E] (x : E) :
    LipschitzWith 1 (fun _ : ℝ => x) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [dist_self, NNReal.coe_one, one_mul]
  exact dist_nonneg

theorem lipSignature_constant {ι : Type*} [Fintype ι] (x : ι → ℝ) {a b : ℝ} (hab : a ≤ b) :
    lipSignature (fun _ => x) (constant_lipschitz x) a b hab = unitSeries :=
  treeLike_pathSignature_eq_unit _ hab (lipschitz_boundedVariation _ (constant_lipschitz x) a b)
    (treeLike_constant x a b)

theorem translate_lipschitz {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    (hγ : LipschitzWith 1 γ) (v : ι → ℝ) : LipschitzWith 1 (fun t => γ t + v) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_add_right]
  exact hγ.dist_le_mul s t

/-- Spatial translations do not change any actual signature coefficient. -/
theorem lipSignature_translate {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    (hγ : LipschitzWith 1 γ) (v : ι → ℝ) {a b : ℝ} (hab : a ≤ b) :
    lipSignature (fun t => γ t + v) (translate_lipschitz γ hγ v) a b hab =
      lipSignature γ hγ a b hab := by
  let hf := lipschitz_boundedVariation γ hγ a b
  let hc := hγ.continuous.continuousOn (s := Icc a b)
  let p (i : ι) := canonicalPositive hab (coordinate_boundedVariation hf i) (coordinate_continuousOn hc i)
  let m (i : ι) := canonicalNegative hab (coordinate_boundedVariation hf i) (coordinate_continuousOn hc i)
  funext w
  apply pathSignature_eq_representation _ hab _ _ p m
    (fun _ => canonicalPositive_continuous _ _ _) (fun _ => canonicalNegative_continuous _ _ _) _ w
  intro i x hx y hy
  have he := canonical_represents hab (coordinate_boundedVariation hf i) (coordinate_continuousOn hc i)
    x hx y hy
  change _ = (γ y i + v i) - (γ x i + v i)
  exact he.trans (by ring)

theorem shift_lipschitz (d : ℝ) : LipschitzWith 1 (fun t : ℝ => t + d) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [NNReal.coe_one, one_mul, dist_add_right]
  exact le_rfl

theorem lipSignature_shift {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    (hγ : LipschitzWith 1 γ) (d : ℝ) {a b : ℝ} (hab : a ≤ b) :
    lipSignature (fun t => γ (t + d))
      (by simpa only [one_mul, Function.comp_apply] using (hγ.comp (shift_lipschitz d))) a b hab =
      lipSignature γ hγ (a + d) (b + d) (add_le_add hab le_rfl) :=
  lipSignature_reparametrize γ hγ (fun t => t + d) (shift_lipschitz d)
    (fun _ _ h => add_le_add h le_rfl) (add_le_add hab le_rfl) hab rfl rfl

/-- An admissible route has an actual globally Lipschitz coordinate curve of speed at most one;
its entire based signature lift stays in the prescribed set. -/
structure Route {ι : Type*} [Fintype ι] (K : Set (Series ι)) (P Q : Series ι) where
  duration : ℝ
  nonneg : 0 ≤ duration
  curve : ℝ → ι → ℝ
  lipschitz : LipschitzWith 1 curve
  initial : curve 0 = 0
  terminal : product P (lipSignature curve lipschitz 0 duration nonneg) = Q
  within : ∀t (ht : t ∈ Icc 0 duration), product P (lipSignature curve lipschitz 0 t ht.1) ∈ K


theorem lipSignature_nil {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    (hγ : LipschitzWith 1 γ) {a b : ℝ} (hab : a ≤ b) :
    lipSignature γ hγ a b hab [] = 1 := rfl

theorem lipSignature_singleton {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    (hγ : LipschitzWith 1 γ) {a b : ℝ} (hab : a ≤ b) (i : ι) :
    lipSignature γ hγ a b hab [i] = γ b i - γ a i := by
  change stieltjesIntegral _ _ a b (fun _ => 1) = _
  simp only [stieltjesIntegral, intervalIntegral.integral_of_le hab,
    setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
    StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((canonicalPositive hab
      (coordinate_boundedVariation (lipschitz_boundedVariation γ hγ a b) i)
      (coordinate_continuousOn hγ.continuous.continuousOn i)).mono hab)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((canonicalNegative hab
      (coordinate_boundedVariation (lipschitz_boundedVariation γ hγ a b) i)
      (coordinate_continuousOn hγ.continuous.continuousOn i)).mono hab))]
  exact canonical_represents hab
    (coordinate_boundedVariation (lipschitz_boundedVariation γ hγ a b) i)
    (coordinate_continuousOn hγ.continuous.continuousOn i)
    a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩

theorem Route.target_nil {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) : Q [] = P [] := by
  have he := congrArg (fun S : Series ι => S []) r.terminal
  simpa only [LinearInputCurveWordFormalSeries.product_empty, lipSignature_nil, mul_one] using he.symm

theorem Route.firstLevel_increment {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) (hP : P [] = 1) (i : ι) :
    Q [i] = P [i] + r.curve r.duration i := by
  have he := congrArg (fun S : Series ι => S [i]) r.terminal
  change product P (lipSignature r.curve r.lipschitz 0 r.duration r.nonneg) [i] = Q [i] at he
  rw [product_cons, LinearInputCurveWordFormalSeries.product_empty,
    hP, lipSignature_singleton, lipSignature_nil, r.initial] at he
  simpa only [Pi.zero_apply, sub_zero, one_mul, mul_one, add_comm] using he.symm

theorem Route.firstLevel_bound {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) (hP : P [] = 1) :
    dist (fun i => P [i]) (fun i => Q [i]) ≤ r.duration := by
  have he : (fun i => Q [i]) = (fun i => P [i]) + r.curve r.duration :=
    funext (r.firstLevel_increment hP)
  have hlip := r.lipschitz.dist_le_mul r.duration 0
  rw [r.initial] at hlip
  simp only [NNReal.coe_one, one_mul, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg r.nonneg] at hlip
  rw [he, dist_eq_norm, show (fun i => P [i]) - ((fun i => P [i]) + r.curve r.duration) =
    -r.curve r.duration by abel, norm_neg]
  exact hlip


theorem Route.source_mem {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) : P ∈ K := by
  have he := r.within 0 ⟨le_rfl, r.nonneg⟩
  simpa only [lipSignature_same, product_unit_right] using he

theorem Route.target_mem {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) : Q ∈ K := r.terminal ▸ r.within r.duration ⟨r.nonneg, le_rfl⟩

def Route.refl {ι : Type*} [Fintype ι] {K : Set (Series ι)} (P : Series ι) (hP : P ∈ K) :
    Route K P P where
  duration := 0
  nonneg := le_rfl
  curve := fun _ => 0
  lipschitz := constant_lipschitz 0
  initial := rfl
  terminal := by rw [lipSignature_same, product_unit_right]
  within := by
    intro t ht
    have he : t = 0 := le_antisymm ht.2 ht.1
    subst t
    simpa only [lipSignature_same, product_unit_right] using hP

def Route.controlled {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) : speedControlledPaths r.duration r.nonneg (0 : ι → ℝ) :=
  ⟨(speedControlledOfLipschitz r.nonneg r.curve r.lipschitz).val,
    (speedControlledOfLipschitz r.nonneg r.curve r.lipschitz).property.1,
    (speedControlledOfLipschitz r.nonneg r.curve r.lipschitz).property.2.trans r.initial⟩

theorem Route.controlled_eq {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) : EqOn (pathExtension r.nonneg r.controlled.val) r.curve (Icc 0 r.duration) :=
  speedControlledOfLipschitz_eq r.nonneg r.curve r.lipschitz

theorem Route.controlled_prefix {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) {t : ℝ} (ht : t ∈ Icc 0 r.duration) :
    prefixSignature r.nonneg 0 r.controlled t = lipSignature r.curve r.lipschitz 0 t ht.1 := by
  rw [prefixSignature_eq_pathSignature r.nonneg 0 r.controlled ht.1]
  funext w
  exact pathSignature_congr ht.1 _ _ _ _
    (fun u hu => r.controlled_eq ⟨hu.1, hu.2.trans ht.2⟩) w

theorem Route.controlled_admissible {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) :
    r.controlled ∈ signatureRangeClass r.nonneg 0 P Q K := by
  constructor
  · change product P (prefixSignature r.nonneg 0 r.controlled r.duration) = Q
    rw [r.controlled_prefix ⟨r.nonneg, le_rfl⟩]
    exact r.terminal
  · intro t
    change product P (prefixSignature r.nonneg 0 r.controlled t.val) ∈ K
    rw [r.controlled_prefix t.property]
    exact r.within t.val t.property

theorem stoppedClass_constant {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L)
    {x : ι → ℝ} {P Q : Series ι} {K : Set (Series ι)}
    {z : Icc (0 : ℝ) L × speedControlledPaths L hL x}
    (hz : z ∈ stoppedClass hL x P Q K) {t : ℝ} (ht : t ∈ Icc z.1.val L) :
    pathExtension hL z.2.val t = pathExtension hL z.2.val z.1.val := by
  have htm : t ∈ Icc (0 : ℝ) L := ⟨z.1.property.1.trans ht.1, ht.2⟩
  have he := hz.2 ⟨t, htm⟩
  rw [max_eq_right (show z.1 ≤ (⟨t, htm⟩ : Icc (0 : ℝ) L) from ht.1)] at he
  simpa only [pathExtension, projIcc_of_mem hL htm, projIcc_of_mem hL z.1.property] using he

theorem stoppedClass_terminal {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L)
    {x : ι → ℝ} {P Q : Series ι} {K : Set (Series ι)}
    {z : Icc (0 : ℝ) L × speedControlledPaths L hL x}
    (hz : z ∈ stoppedClass hL x P Q K) :
    product P (lipSignature (pathExtension hL z.2.val)
      (pathExtension_lipschitz hL z.2.val z.2.property.1) 0 z.1.val z.1.property.1) = Q := by
  let γ := pathExtension hL z.2.val
  have hγ : LipschitzWith 1 γ := pathExtension_lipschitz hL z.2.val z.2.property.1
  have ht : lipSignature γ hγ z.1.val L z.1.property.2 = unitSeries := by
    rw [lipSignature_congr γ (fun _ => γ z.1.val) hγ (constant_lipschitz _) z.1.property.2
      (fun _ ht => stoppedClass_constant hL hz ht), lipSignature_constant]
  have he := hz.1.1
  change product P (prefixSignature hL x z.2 L) = Q at he
  rw [prefixSignature_eq_pathSignature hL x z.2 hL] at he
  change product P (lipSignature γ hγ 0 L hL) = Q at he
  rw [lipSignature_split γ hγ z.1.property.1 z.1.property.2, ht, product_unit_right] at he
  exact he

def routeOfStopped {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 ≤ L)
    {P Q : Series ι} {K : Set (Series ι)}
    (z : Icc (0 : ℝ) L × speedControlledPaths L hL (0 : ι → ℝ))
    (hz : z ∈ stoppedClass hL 0 P Q K) : Route K P Q where
  duration := z.1.val
  nonneg := z.1.property.1
  curve := pathExtension hL z.2.val
  lipschitz := pathExtension_lipschitz hL z.2.val z.2.property.1
  initial := by
    change z.2.val (projIcc 0 L hL 0) = 0
    rw [projIcc_of_mem hL (left_mem_Icc.mpr hL)]
    exact z.2.property.2
  terminal := stoppedClass_terminal hL hz
  within := by
    intro t ht
    have hm := hz.1.2 ⟨t, ht.1, ht.2.trans z.1.property.2⟩
    change product P (prefixSignature hL 0 z.2 t) ∈ K at hm
    rw [prefixSignature_eq_pathSignature hL 0 z.2 ht.1] at hm
    exact hm

theorem clamp_lipschitz (a b : ℝ) : LipschitzWith 1 (clamp a b) := by
  have hi : LipschitzWith 1 (id : ℝ → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [id_eq, NNReal.coe_one, one_mul, le_refl]
  exact (hi.const_min b).const_max a

def Route.paddedCurve {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) : ℝ → ι → ℝ := r.curve ∘ clamp 0 r.duration

theorem Route.paddedCurve_lipschitz {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) :
    LipschitzWith 1 r.paddedCurve := by
  simpa only [one_mul] using r.lipschitz.comp (clamp_lipschitz 0 r.duration)

theorem Route.paddedCurve_initial {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) : r.paddedCurve 0 = 0 := by
  rw [Route.paddedCurve, Function.comp_apply, clamp_eq (left_mem_Icc.mpr r.nonneg)]
  exact r.initial

def Route.paddedControlled {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) {L : ℝ} (hL : 0 ≤ L) : speedControlledPaths L hL (0 : ι → ℝ) :=
  ⟨(speedControlledOfLipschitz hL r.paddedCurve r.paddedCurve_lipschitz).val,
    (speedControlledOfLipschitz hL r.paddedCurve r.paddedCurve_lipschitz).property.1,
    (speedControlledOfLipschitz hL r.paddedCurve r.paddedCurve_lipschitz).property.2.trans
      r.paddedCurve_initial⟩

theorem Route.paddedControlled_prefix {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) {L : ℝ} (hL : 0 ≤ L)
    {t : ℝ} (ht : t ∈ Icc 0 L) :
    prefixSignature hL 0 (r.paddedControlled hL) t =
      lipSignature r.curve r.lipschitz 0 (clamp 0 r.duration t) (clamp_mem r.nonneg t).1 := by
  have he : EqOn (pathExtension hL (r.paddedControlled hL).val) r.paddedCurve (Icc 0 L) :=
    speedControlledOfLipschitz_eq hL r.paddedCurve r.paddedCurve_lipschitz
  rw [prefixSignature_eq_pathSignature hL 0 (r.paddedControlled hL) ht.1]
  have hsig : pathSignature (pathExtension hL (r.paddedControlled hL).val) ht.1
      ((pathExtension_boundedVariation hL (r.paddedControlled hL).val
        (r.paddedControlled hL).property.1).mono (subset_univ _))
      (pathExtension_continuous hL (r.paddedControlled hL).val).continuousOn =
      lipSignature r.paddedCurve r.paddedCurve_lipschitz 0 t ht.1 := by
    funext w
    exact pathSignature_congr ht.1 _ _ _ _ (fun u hu => he ⟨hu.1, hu.2.trans ht.2⟩) w
  rw [hsig]
  exact lipSignature_reparametrize r.curve r.lipschitz (clamp 0 r.duration)
    (clamp_lipschitz 0 r.duration) (clamp_monotone 0 r.duration)
    (clamp_mem r.nonneg t).1 ht.1 (clamp_eq (left_mem_Icc.mpr r.nonneg)) rfl

theorem Route.paddedControlled_stopped {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) {L : ℝ} (hL : 0 ≤ L)
    (hrL : r.duration ≤ L) :
    (⟨r.duration, r.nonneg, hrL⟩, r.paddedControlled hL) ∈ stoppedClass hL 0 P Q K := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change product P (prefixSignature hL 0 (r.paddedControlled hL) L) = Q
    rw [r.paddedControlled_prefix hL ⟨hL, le_rfl⟩]
    have he : clamp 0 r.duration L = r.duration := by
      rw [clamp, min_eq_left hrL, max_eq_right r.nonneg]
    rw [lipSignature_endpoint_congr r.curve r.lipschitz _ r.nonneg he]
    exact r.terminal
  · intro t
    change product P (prefixSignature hL 0 (r.paddedControlled hL) t.val) ∈ K
    rw [r.paddedControlled_prefix hL t.property]
    exact r.within _ (clamp_mem r.nonneg t.val)
  · intro t
    change r.curve (clamp 0 r.duration (max r.duration t.val)) =
      r.curve (clamp 0 r.duration r.duration)
    rw [clamp_eq (right_mem_Icc.mpr r.nonneg)]
    congr 1
    rw [clamp, min_eq_left (le_max_left _ _), max_eq_right r.nonneg]

/-- Every actual admissible route in a closed signature set has a globally
shortest admissible route. Arbitrarily long competitors are included: short
competitors fit the compact budget by stopping, and longer ones are trivial. -/
theorem exists_shortest_route {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    (hK : IsClosed K) {P Q : Series ι} (r : Route K P Q) :
    ∃s : Route K P Q, ∀q : Route K P Q, s.duration ≤ q.duration := by
  obtain ⟨z, hz, hmin⟩ := exists_minimal_stopping_time r.nonneg 0 P Q hK
    r.controlled r.controlled_admissible
  refine ⟨routeOfStopped r.nonneg z hz, ?_⟩
  intro q
  by_cases hq : q.duration ≤ r.duration
  · exact hmin (⟨q.duration, q.nonneg, hq⟩, q.paddedControlled r.nonneg)
      (q.paddedControlled_stopped r.nonneg hq)
  · exact z.1.property.2.trans (le_of_not_ge hq)

theorem joinCurve_lipschitz {E : Type*} [PseudoMetricSpace E] (γ η : ℝ → E)
    (hγ : LipschitzWith 1 γ) (hη : LipschitzWith 1 η) {b : ℝ} (he : γ b = η b) :
    LipschitzWith 1 (joinCurve b γ η) := by
  have haux (x y : ℝ) (hxy : x ≤ y) :
      dist (joinCurve b γ η x) (joinCurve b γ η y) ≤ y - x := by
    by_cases hyb : y ≤ b
    · rw [joinCurve_left b γ η (hxy.trans hyb), joinCurve_left b γ η hyb]
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using hγ.dist_le_mul x y
    · by_cases hbx : b ≤ x
      · rw [joinCurve_right he hbx, joinCurve_right he (hbx.trans hxy)]
        simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using hη.dist_le_mul x y
      · have hxb : x ≤ b := (lt_of_not_ge hbx).le
        have hby : b ≤ y := (lt_of_not_ge hyb).le
        rw [joinCurve_left b γ η hxb, joinCurve_right he hby]
        have hx := hγ.dist_le_mul x b
        have hy := hη.dist_le_mul b y
        simp only [NNReal.coe_one, one_mul, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hxb), neg_sub] at hx
        simp only [NNReal.coe_one, one_mul, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hby), neg_sub] at hy
        have htri := dist_triangle (γ x) (γ b) (η y)
        rw [he] at htri
        rw [he] at hx
        linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total x y with hxy | hyx
  · simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using haux x y hxy
  · have he := haux y x hyx
    rw [dist_comm] at he
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hyx)] using he

def concatTail {ι : Type*} (γ η : ℝ → ι → ℝ) (T u : ℝ) : ι → ℝ :=
  η (u + -T) + γ T

theorem concatTail_lipschitz {ι : Type*} [Fintype ι] (γ η : ℝ → ι → ℝ)
    (hη : LipschitzWith 1 η) (T : ℝ) : LipschitzWith 1 (concatTail γ η T) :=
  translate_lipschitz (fun u => η (u + -T))
    (by simpa only [one_mul, Function.comp_apply] using hη.comp (shift_lipschitz (-T))) (γ T)

theorem concatTail_matches {ι : Type*} (γ η : ℝ → ι → ℝ) (T : ℝ) (hη0 : η 0 = 0) :
    γ T = concatTail γ η T T := by simp [concatTail, hη0]

def concatCurve {ι : Type*} (γ η : ℝ → ι → ℝ) (T : ℝ) : ℝ → ι → ℝ :=
  joinCurve T γ (concatTail γ η T)

theorem concatCurve_lipschitz {ι : Type*} [Fintype ι] (γ η : ℝ → ι → ℝ)
    (hγ : LipschitzWith 1 γ) (hη : LipschitzWith 1 η) (T : ℝ) (hη0 : η 0 = 0) :
    LipschitzWith 1 (concatCurve γ η T) :=
  joinCurve_lipschitz γ (concatTail γ η T) hγ (concatTail_lipschitz γ η hη T)
    (concatTail_matches γ η T hη0)

theorem lipSignature_interval_congr {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (ha : a = c) (hb : b = d) :
    lipSignature γ hγ a b hab = lipSignature γ hγ c d hcd := by
  subst c
  subst d
  rfl

theorem concatTail_signature {ι : Type*} [Fintype ι] (γ η : ℝ → ι → ℝ)
    (hη : LipschitzWith 1 η) {T u : ℝ} (hTu : T ≤ u) :
    lipSignature (concatTail γ η T) (concatTail_lipschitz γ η hη T) T u hTu =
      lipSignature η hη 0 (u - T) (sub_nonneg.mpr hTu) := by
  rw [show lipSignature (concatTail γ η T) (concatTail_lipschitz γ η hη T) T u hTu =
      lipSignature (fun z => η (z + -T))
        (by simpa only [one_mul, Function.comp_apply] using hη.comp (shift_lipschitz (-T))) T u hTu from
    lipSignature_translate _ _ (γ T) hTu]
  exact (lipSignature_shift η hη (-T) hTu).trans
    (lipSignature_interval_congr η hη _ _ (by ring) (by ring))

theorem concatCurve_prefix_left {ι : Type*} [Fintype ι] (γ η : ℝ → ι → ℝ)
    (hγ : LipschitzWith 1 γ) (hη : LipschitzWith 1 η) {T u : ℝ} (hη0 : η 0 = 0)
    (hu : 0 ≤ u) (huT : u ≤ T) :
    lipSignature (concatCurve γ η T) (concatCurve_lipschitz γ η hγ hη T hη0) 0 u hu =
      lipSignature γ hγ 0 u hu :=
  lipSignature_congr _ _ _ _ hu (fun _ ht => joinCurve_left T γ _ (ht.2.trans huT))

theorem concatCurve_prefix_right {ι : Type*} [Fintype ι] (γ η : ℝ → ι → ℝ)
    (hγ : LipschitzWith 1 γ) (hη : LipschitzWith 1 η) {T u : ℝ} (hη0 : η 0 = 0)
    (hT : 0 ≤ T) (hTu : T ≤ u) :
    lipSignature (concatCurve γ η T) (concatCurve_lipschitz γ η hγ hη T hη0) 0 u (hT.trans hTu) =
      product (lipSignature γ hγ 0 T hT) (lipSignature η hη 0 (u - T) (sub_nonneg.mpr hTu)) := by
  rw [lipSignature_split _ _ hT hTu, concatCurve_prefix_left γ η hγ hη hη0 hT le_rfl]
  congr 1
  exact (lipSignature_congr _ _ _ _ hTu
    (fun _ ht => joinCurve_right (concatTail_matches γ η T hη0) ht.1)).trans
      (concatTail_signature γ η hη hTu)

def Route.join {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q R : Series ι}
    (r : Route K P Q) (s : Route K Q R) : Route K P R where
  duration := r.duration + s.duration
  nonneg := add_nonneg r.nonneg s.nonneg
  curve := concatCurve r.curve s.curve r.duration
  lipschitz := concatCurve_lipschitz r.curve s.curve r.lipschitz s.lipschitz r.duration s.initial
  initial := (joinCurve_left r.duration r.curve _ r.nonneg).trans r.initial
  terminal := by
    rw [concatCurve_prefix_right r.curve s.curve r.lipschitz s.lipschitz s.initial r.nonneg
      (le_add_of_nonneg_right s.nonneg)]
    rw [lipSignature_endpoint_congr s.curve s.lipschitz _ s.nonneg
      (show r.duration + s.duration - r.duration = s.duration by ring),
      ← product_assoc, r.terminal, s.terminal]
  within := by
    intro t ht
    by_cases htr : t ≤ r.duration
    · rw [concatCurve_prefix_left r.curve s.curve r.lipschitz s.lipschitz s.initial ht.1 htr]
      exact r.within t ⟨ht.1, htr⟩
    · have hrt : r.duration ≤ t := (lt_of_not_ge htr).le
      rw [concatCurve_prefix_right r.curve s.curve r.lipschitz s.lipschitz s.initial r.nonneg hrt,
        ← product_assoc, r.terminal]
      exact s.within (t - r.duration) ⟨sub_nonneg.mpr hrt, by linarith [ht.2]⟩

theorem Route.join_duration {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q R : Series ι}
    (r : Route K P Q) (s : Route K Q R) : (r.join s).duration = r.duration + s.duration := rfl

def Route.mono {ι : Type*} [Fintype ι] {K J : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) (hKJ : K ⊆ J) : Route J P Q :=
  { r with within := fun t ht => hKJ (r.within t ht) }

def Route.copy {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q P' Q' : Series ι}
    (r : Route K P Q) (hP : P = P') (hQ : Q = Q') : Route K P' Q' := by
  subst P'
  subst Q'
  exact r

theorem Route.copy_duration {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q P' Q' : Series ι}
    (r : Route K P Q) (hP : P = P') (hQ : Q = Q') : (r.copy hP hQ).duration = r.duration := by
  subst P'
  subst Q'
  rfl

def Route.prefix {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) (t : ℝ) (ht : t ∈ Icc 0 r.duration) :
    Route K P (product P (lipSignature r.curve r.lipschitz 0 t ht.1)) where
  duration := t
  nonneg := ht.1
  curve := r.curve
  lipschitz := r.lipschitz
  initial := r.initial
  terminal := rfl
  within := fun u hu => r.within u ⟨hu.1, hu.2.trans ht.2⟩

theorem Route.prefix_duration {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) (t : ℝ) (ht : t ∈ Icc 0 r.duration) : (r.prefix t ht).duration = t := rfl

theorem reverseClock_lipschitz (T : ℝ) : LipschitzWith 1 (fun t : ℝ => T - t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rw [show T - x - (T - y) = y - x by ring, abs_sub_comm]

def reverseCurve {ι : Type*} (γ : ℝ → ι → ℝ) (T u : ℝ) : ι → ℝ := γ (T - u) + -γ T

theorem reverseCurve_lipschitz {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) (T : ℝ) :
    LipschitzWith 1 (reverseCurve γ T) :=
  translate_lipschitz (fun u => γ (T - u))
    (by simpa only [one_mul, Function.comp_apply] using hγ.comp (reverseClock_lipschitz T)) (-γ T)

theorem reverseCurve_initial {ι : Type*} (γ : ℝ → ι → ℝ) (T : ℝ) :
    reverseCurve γ T 0 = 0 := by simp [reverseCurve]

/-- Based prefixes of the actual reversed, spatially normalized curve are
the original based prefixes read backwards. -/
theorem reverseCurve_based_prefix {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) (P : Series ι)
    {T u : ℝ} (hT : 0 ≤ T) (hu : u ∈ Icc 0 T) :
    product (product P (lipSignature γ hγ 0 T hT))
      (lipSignature (reverseCurve γ T) (reverseCurve_lipschitz γ hγ T) 0 u hu.1) =
      product P (lipSignature γ hγ 0 (T - u) (sub_nonneg.mpr hu.2)) := by
  have hBV := lipschitz_boundedVariation γ hγ 0 T
  let p (i : ι) := canonicalPositive hT (coordinate_boundedVariation hBV i)
    (coordinate_continuousOn hγ.continuous.continuousOn i)
  let m (i : ι) := canonicalNegative hT (coordinate_boundedVariation hBV i)
    (coordinate_continuousOn hγ.continuous.continuousOn i)
  have hp (i : ι) : Continuous (p i : ℝ → ℝ) := canonicalPositive_continuous _ _ _
  have hm (i : ι) : Continuous (m i : ℝ → ℝ) := canonicalNegative_continuous _ _ _
  have hrep (i : ι) : RepresentsOn (p i) (m i) (fun t => γ t i) 0 T := canonical_represents _ _ _
  have hsig (r : ℝ) (hr : r ∈ Icc 0 T) :
      lipSignature γ hγ 0 r hr.1 = stieltjesSignature p m 0 r := by
    funext w
    exact pathSignature_eq_representation γ hr.1 _ _ p m hp hm
      (fun i x hx y hy => hrep i x ⟨hx.1, hx.2.trans hr.2⟩ y ⟨hy.1, hy.2.trans hr.2⟩) w
  have hφ : AntitoneOn (fun t : ℝ => T - t) (Icc 0 u) :=
    fun _ _ _ _ hxy => sub_le_sub_left hxy _
  have hmap : MapsTo (fun t : ℝ => T - t) (Icc 0 u) (Icc 0 T) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, hu.2]
  have hr := pathSignature_oriented_reparametrize γ p m hp hm hu.1 hBV hγ.continuous.continuousOn
    hrep (Or.inr hφ) (continuous_const.sub continuous_id).continuousOn hmap
  have hreverse : lipSignature (reverseCurve γ T) (reverseCurve_lipschitz γ hγ T) 0 u hu.1 =
      stieltjesSignature p m T (T - u) := by
    have he := lipSignature_translate (fun t => γ (T - t))
      (show LipschitzWith 1 (fun t => γ (T - t)) by
        simpa only [one_mul, Function.comp_apply] using hγ.comp (reverseClock_lipschitz T)) (-γ T) hu.1
    exact he.trans (by simpa only [sub_zero] using hr)
  rw [hreverse, hsig T ⟨hT, le_rfl⟩,
    hsig (T - u) ⟨sub_nonneg.mpr hu.2, by linarith [hu.1]⟩, product_assoc,
    ← LinearInputCurveWordBVAlgebra.signature_product p m hp hm 0 T (T - u)]

def Route.reverse {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) : Route K Q P where
  duration := r.duration
  nonneg := r.nonneg
  curve := reverseCurve r.curve r.duration
  lipschitz := reverseCurve_lipschitz r.curve r.lipschitz r.duration
  initial := reverseCurve_initial r.curve r.duration
  terminal := by
    have he := reverseCurve_based_prefix r.curve r.lipschitz P r.nonneg ⟨r.nonneg, le_rfl⟩
    rw [r.terminal] at he
    refine he.trans ?_
    rw [lipSignature_endpoint_congr r.curve r.lipschitz _ le_rfl (sub_self r.duration),
      lipSignature_same, product_unit_right]
  within := by
    intro u hu
    have he := reverseCurve_based_prefix r.curve r.lipschitz P r.nonneg hu
    rw [r.terminal] at he
    rw [he]
    exact r.within (r.duration - u) ⟨sub_nonneg.mpr hu.2, by linarith [hu.1]⟩

theorem Route.reverse_duration {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) : r.reverse.duration = r.duration := rfl

theorem Route.reverse_prefix {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) {u : ℝ} (hu : u ∈ Icc 0 r.duration) :
    product Q (lipSignature r.reverse.curve r.reverse.lipschitz 0 u hu.1) =
      product P (lipSignature r.curve r.lipschitz 0 (r.duration - u) (sub_nonneg.mpr hu.2)) := by
  have he := reverseCurve_based_prefix r.curve r.lipschitz P r.nonneg hu
  rwa [r.terminal] at he

def subCurve {ι : Type*} (γ : ℝ → ι → ℝ) (s u : ℝ) : ι → ℝ := γ (u + s) + -γ s

theorem subCurve_lipschitz {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    (hγ : LipschitzWith 1 γ) (s : ℝ) : LipschitzWith 1 (subCurve γ s) :=
  translate_lipschitz (fun u => γ (u + s))
    (by simpa only [one_mul, Function.comp_apply] using hγ.comp (shift_lipschitz s)) (-γ s)

theorem subCurve_initial {ι : Type*} (γ : ℝ → ι → ℝ) (s : ℝ) : subCurve γ s 0 = 0 := by
  simp [subCurve]

theorem lipSignature_bounds_congr {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    (hγ : LipschitzWith 1 γ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (ha : a = c) (hb : b = d) : lipSignature γ hγ a b hab = lipSignature γ hγ c d hcd := by
  subst c
  subst d
  rfl

theorem subCurve_signature {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    (hγ : LipschitzWith 1 γ) (s : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    lipSignature (subCurve γ s) (subCurve_lipschitz γ hγ s) 0 u hu =
      lipSignature γ hγ s (u + s) (by linarith) := by
  have he := lipSignature_translate (fun t => γ (t + s))
    (show LipschitzWith 1 (fun t => γ (t + s)) by
      simpa only [one_mul, Function.comp_apply] using hγ.comp (shift_lipschitz s)) (-γ s) hu
  exact he.trans ((lipSignature_shift γ hγ s hu).trans
    (lipSignature_bounds_congr γ hγ _ _ (zero_add s) rfl))

theorem subCurve_based_prefix {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    (hγ : LipschitzWith 1 γ) (P : Series ι) {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) :
    product (product P (lipSignature γ hγ 0 s hs))
      (lipSignature (subCurve γ s) (subCurve_lipschitz γ hγ s) 0 u hu) =
      product P (lipSignature γ hγ 0 (u + s) (add_nonneg hu hs)) := by
  rw [subCurve_signature γ hγ s hu, product_assoc, ← lipSignature_split γ hγ hs]

def Route.subpath {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ r.duration) :
    Route K (product P (lipSignature r.curve r.lipschitz 0 s hs))
      (product P (lipSignature r.curve r.lipschitz 0 t (hs.trans hst))) where
  duration := t - s
  nonneg := sub_nonneg.mpr hst
  curve := subCurve r.curve s
  lipschitz := subCurve_lipschitz r.curve r.lipschitz s
  initial := subCurve_initial r.curve s
  terminal := by
    have he := subCurve_based_prefix r.curve r.lipschitz P hs (sub_nonneg.mpr hst)
    refine he.trans ?_
    congr 1
    exact lipSignature_endpoint_congr r.curve r.lipschitz _ _ (sub_add_cancel t s)
  within := by
    intro u hu
    rw [subCurve_based_prefix r.curve r.lipschitz P hs hu.1]
    exact r.within (u + s) ⟨add_nonneg hu.1 hs, by linarith [hu.2]⟩

theorem Route.subpath_duration {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ r.duration) :
    (r.subpath hs hst ht).duration = t - s := rfl

theorem Route.subpath_prefix {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) {s t u : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ r.duration)
    (hu : u ∈ Icc 0 (t - s)) :
    product (product P (lipSignature r.curve r.lipschitz 0 s hs))
      (lipSignature (r.subpath hs hst ht).curve (r.subpath hs hst ht).lipschitz 0 u hu.1) =
      product P (lipSignature r.curve r.lipschitz 0 (u + s) (add_nonneg hu.1 hs)) :=
  subCurve_based_prefix r.curve r.lipschitz P hs hu.1


theorem Route.subpath_shortest {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q)
    (hmin : ∀ q : Route K P Q, r.duration ≤ q.duration)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ r.duration)
    (q : Route K (product P (lipSignature r.curve r.lipschitz 0 s hs))
      (product P (lipSignature r.curve r.lipschitz 0 t (hs.trans hst)))) :
    t - s ≤ q.duration := by
  let front := r.prefix s ⟨hs, hst.trans ht⟩
  let back := (r.subpath (hs.trans hst) ht le_rfl).copy rfl r.terminal
  have hbound := hmin ((front.join q).join back)
  simp only [Route.join_duration, Route.copy_duration, Route.subpath_duration,
    Route.prefix_duration, front, back] at hbound
  linarith


def intrinsicDist {ι : Type*} [Fintype ι] (K : Set (Series ι)) (P Q : Series ι) : ℝ :=
  sInf (Set.range (fun r : Route K P Q => r.duration))

theorem routeDurations_bddBelow {ι : Type*} [Fintype ι] (K : Set (Series ι)) (P Q : Series ι) :
    BddBelow (Set.range (fun r : Route K P Q => r.duration)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨r, rfl⟩
  exact r.nonneg

theorem intrinsicDist_le_duration {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) :
    intrinsicDist K P Q ≤ r.duration :=
  csInf_le (routeDurations_bddBelow K P Q) ⟨r, rfl⟩

theorem intrinsicDist_nonneg {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (hr : Nonempty (Route K P Q)) :
    0 ≤ intrinsicDist K P Q := by
  change 0 ≤ sInf (Set.range (fun r : Route K P Q => r.duration))
  apply _root_.le_csInf (s := Set.range (fun r : Route K P Q => r.duration))
      ⟨hr.some.duration, hr.some, rfl⟩
  rintro _ ⟨r, rfl⟩
  exact r.nonneg

def shortestRouteOfNonempty {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    (hK : IsClosed K) {P Q : Series ι} (hr : Nonempty (Route K P Q)) : Route K P Q :=
  (exists_shortest_route hK hr.some).choose

theorem shortestRouteOfNonempty_minimal {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    (hK : IsClosed K) {P Q : Series ι} (hr : Nonempty (Route K P Q)) (r : Route K P Q) :
    (shortestRouteOfNonempty hK hr).duration ≤ r.duration :=
  (exists_shortest_route hK hr.some).choose_spec r

theorem shortestRouteOfNonempty_duration {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    (hK : IsClosed K) {P Q : Series ι} (hr : Nonempty (Route K P Q)) :
    (shortestRouteOfNonempty hK hr).duration = intrinsicDist K P Q := by
  apply le_antisymm
  · change _ ≤ sInf (Set.range (fun r : Route K P Q => r.duration))
    apply _root_.le_csInf (s := Set.range (fun r : Route K P Q => r.duration))
      ⟨hr.some.duration, hr.some, rfl⟩
    rintro _ ⟨r, rfl⟩
    exact shortestRouteOfNonempty_minimal hK hr r
  · exact intrinsicDist_le_duration _

theorem intrinsicDist_self {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P : Series ι} (hP : P ∈ K) : intrinsicDist K P P = 0 :=
  le_antisymm (intrinsicDist_le_duration (Route.refl P hP))
    (intrinsicDist_nonneg ⟨Route.refl P hP⟩)

theorem Route.eq_of_duration_zero {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) (hr : r.duration = 0) : P = Q := by
  have he := r.terminal
  rw [lipSignature_endpoint_congr r.curve r.lipschitz r.nonneg le_rfl hr,
    lipSignature_same, product_unit_right] at he
  exact he

theorem eq_of_intrinsicDist_zero {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    (hK : IsClosed K) {P Q : Series ι} (hr : Nonempty (Route K P Q))
    (hd : intrinsicDist K P Q = 0) : P = Q :=
  (shortestRouteOfNonempty hK hr).eq_of_duration_zero
    ((shortestRouteOfNonempty_duration hK hr).trans hd)

theorem intrinsicDist_triangle {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    (hK : IsClosed K) {P Q R : Series ι} (hPQ : Nonempty (Route K P Q))
    (hQR : Nonempty (Route K Q R)) :
    intrinsicDist K P R ≤ intrinsicDist K P Q + intrinsicDist K Q R := by
  have he := intrinsicDist_le_duration ((shortestRouteOfNonempty hK hPQ).join
    (shortestRouteOfNonempty hK hQR))
  simpa only [Route.join_duration, shortestRouteOfNonempty_duration] using he

theorem intrinsicDist_comm {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    (hK : IsClosed K) {P Q : Series ι} (hPQ : Nonempty (Route K P Q)) :
    intrinsicDist K P Q = intrinsicDist K Q P := by
  have hQP : Nonempty (Route K Q P) := ⟨hPQ.some.reverse⟩
  apply le_antisymm
  · have he := intrinsicDist_le_duration (shortestRouteOfNonempty hK hQP).reverse
    simpa only [Route.reverse_duration, shortestRouteOfNonempty_duration] using he
  · have he := intrinsicDist_le_duration (shortestRouteOfNonempty hK hPQ).reverse
    simpa only [Route.reverse_duration, shortestRouteOfNonempty_duration] using he

/-- Only points reachable by actual admissible routes are included. This
makes every distance finite, without assuming a connectedness theorem. -/
structure IntrinsicPoint {ι : Type*} [Fintype ι] (K : Set (Series ι))
    (hK : IsClosed K) (P0 : Series ι) where
  value : Series ι
  reachable : Nonempty (Route K P0 value)

theorem IntrinsicPoint.ext {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} {p q : IntrinsicPoint K hK P0}
    (he : p.value = q.value) : p = q := by
  cases p
  cases q
  cases he
  rfl

def IntrinsicPoint.route {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0) :
    Route K p.value q.value := p.reachable.some.reverse.join q.reachable.some

instance intrinsicPoint_metricSpace {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} : MetricSpace (IntrinsicPoint K hK P0) where
  dist p q := intrinsicDist K p.value q.value
  dist_self p := intrinsicDist_self p.reachable.some.target_mem
  dist_comm p q := intrinsicDist_comm hK ⟨p.route q⟩
  dist_triangle p q r := intrinsicDist_triangle hK ⟨p.route q⟩ ⟨q.route r⟩
  eq_of_dist_eq_zero := by
    intro p q hpq
    exact IntrinsicPoint.ext (eq_of_intrinsicDist_zero hK ⟨p.route q⟩ hpq)

theorem IntrinsicPoint.dist_eq {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0) :
    dist p q = intrinsicDist K p.value q.value := rfl

theorem IntrinsicPoint.value_injective {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} :
    Function.Injective (IntrinsicPoint.value : IntrinsicPoint K hK P0 → Series ι) :=
  fun _ _ he => IntrinsicPoint.ext he

theorem IntrinsicPoint.dist_le_duration {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0)
    (r : Route K p.value q.value) : dist p q ≤ r.duration := intrinsicDist_le_duration r

def shortestRoute {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0) : Route K p.value q.value :=
  shortestRouteOfNonempty hK ⟨p.route q⟩

theorem shortestRoute_duration {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0) :
    (shortestRoute p q).duration = dist p q := shortestRouteOfNonempty_duration hK ⟨p.route q⟩

theorem shortestRoute_minimal {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0) (r : Route K p.value q.value) :
    (shortestRoute p q).duration ≤ r.duration := shortestRouteOfNonempty_minimal hK ⟨p.route q⟩ r

def IntrinsicPoint.ofRoute {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    (hK : IsClosed K) {P0 Q : Series ι} (r : Route K P0 Q) : IntrinsicPoint K hK P0 :=
  ⟨Q, ⟨r⟩⟩

def IntrinsicPoint.root {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    (hK : IsClosed K) (P0 : Series ι) (hP0 : P0 ∈ K) : IntrinsicPoint K hK P0 :=
  IntrinsicPoint.ofRoute hK (Route.refl P0 hP0)

def Route.prefixPoint {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) (hK : IsClosed K) (t : Icc (0 : ℝ) r.duration) : IntrinsicPoint K hK P :=
  IntrinsicPoint.ofRoute hK (r.prefix t.val t.property)

theorem Route.prefixPoint_value {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) (hK : IsClosed K) (t : Icc (0 : ℝ) r.duration) :
    (r.prefixPoint hK t).value = product P (lipSignature r.curve r.lipschitz 0 t.val t.property.1) := rfl

theorem Route.prefixPoint_zero {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) (hK : IsClosed K) :
    r.prefixPoint hK ⟨0, le_rfl, r.nonneg⟩ = IntrinsicPoint.root hK P r.source_mem := by
  apply IntrinsicPoint.ext
  change product P (lipSignature r.curve r.lipschitz 0 0 le_rfl) = P
  rw [lipSignature_same, product_unit_right]

theorem Route.prefixPoint_last {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P Q : Series ι}
    (r : Route K P Q) (hK : IsClosed K) :
    r.prefixPoint hK ⟨r.duration, r.nonneg, le_rfl⟩ = IntrinsicPoint.ofRoute hK r :=
  IntrinsicPoint.ext r.terminal

theorem Route.prefixPoint_closed {ι : Type*} [Fintype ι] {K : Set (Series ι)} {P : Series ι}
    (r : Route K P P) (hK : IsClosed K) :
    r.prefixPoint hK ⟨0, le_rfl, r.nonneg⟩ = r.prefixPoint hK ⟨r.duration, r.nonneg, le_rfl⟩ := by
  rw [r.prefixPoint_zero hK, r.prefixPoint_last hK]
  exact IntrinsicPoint.ext rfl

theorem IntrinsicPoint.value_nil {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (hP0 : P0 [] = 1) (p : IntrinsicPoint K hK P0) :
    p.value [] = 1 := p.reachable.some.target_nil.trans hP0

theorem firstLevel_lipschitz {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (hP0 : P0 [] = 1) :
    LipschitzWith 1 (fun p : IntrinsicPoint K hK P0 => fun i => p.value [i]) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [NNReal.coe_one, one_mul, shortestRoute_duration] using
    (shortestRoute p q).firstLevel_bound (p.value_nil hP0)

theorem Route.prefixPoint_dist_le {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) (hK : IsClosed K)
    (s t : Icc (0 : ℝ) r.duration) (hst : s ≤ t) :
    dist (r.prefixPoint hK s) (r.prefixPoint hK t) ≤ t.val - s.val := by
  change intrinsicDist K (product P (lipSignature r.curve r.lipschitz 0 s.val s.property.1))
    (product P (lipSignature r.curve r.lipschitz 0 t.val t.property.1)) ≤ t.val - s.val
  exact intrinsicDist_le_duration (r.subpath s.property.1 hst t.property.2)

theorem Route.prefixPoint_lipschitz {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) (hK : IsClosed K) :
    LipschitzWith 1 (r.prefixPoint hK) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist (r.prefixPoint hK s) (r.prefixPoint hK t) ≤ 1 * |s.val - t.val|
  rw [one_mul]
  rcases le_total s t with hst | hts
  · rw [abs_of_nonpos (sub_nonpos.mpr (show s.val ≤ t.val from hst)), neg_sub]
    exact r.prefixPoint_dist_le hK s t hst
  · rw [dist_comm, abs_of_nonneg (sub_nonneg.mpr (show t.val ≤ s.val from hts))]
    exact r.prefixPoint_dist_le hK t s hts

theorem Route.prefixPoint_dist_of_le {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) (hK : IsClosed K)
    (hmin : ∀ q : Route K P Q, r.duration ≤ q.duration)
    (s t : Icc (0 : ℝ) r.duration) (hst : s ≤ t) :
    dist (r.prefixPoint hK s) (r.prefixPoint hK t) = t.val - s.val := by
  apply le_antisymm (r.prefixPoint_dist_le hK s t hst)
  have he := r.subpath_shortest hmin s.property.1 hst t.property.2
    (shortestRoute (r.prefixPoint hK s) (r.prefixPoint hK t))
  simpa only [shortestRoute_duration] using he

theorem Route.prefixPoint_isometry {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) (hK : IsClosed K)
    (hmin : ∀ q : Route K P Q, r.duration ≤ q.duration) :
    Isometry (r.prefixPoint hK) := by
  apply isometry_iff_dist_eq.mpr
  intro s t
  change dist (r.prefixPoint hK s) (r.prefixPoint hK t) = |s.val - t.val|
  rcases le_total s t with hst | hts
  · rw [abs_of_nonpos (sub_nonpos.mpr (show s.val ≤ t.val from hst)), neg_sub]
    exact r.prefixPoint_dist_of_le hK hmin s t hst
  · rw [dist_comm, abs_of_nonneg (sub_nonneg.mpr (show t.val ≤ s.val from hts))]
    exact r.prefixPoint_dist_of_le hK hmin t s hts



/-- Moving a reachable component's base point preserves its intrinsic metric. -/
def IntrinsicPoint.embed {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p : IntrinsicPoint K hK P0)
    (q : IntrinsicPoint K hK p.value) : IntrinsicPoint K hK P0 :=
  ⟨q.value, ⟨p.reachable.some.join q.reachable.some⟩⟩

theorem IntrinsicPoint.embed_isometry {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p : IntrinsicPoint K hK P0) :
    Isometry p.embed := isometry_iff_dist_eq.mpr (fun _ _ => rfl)

def geodesicIndex {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0)
    (t : Icc (0 : ℝ) (dist p q)) : Icc (0 : ℝ) (shortestRoute p q).duration :=
  ⟨t.val, t.property.1, by simpa only [shortestRoute_duration] using t.property.2⟩

theorem geodesicIndex_isometry {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0) :
    Isometry (geodesicIndex p q) := isometry_iff_dist_eq.mpr (fun _ _ => rfl)

theorem geodesicIndex_surjective {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0) :
    Function.Surjective (geodesicIndex p q) := by
  intro t
  exact ⟨⟨t.val, t.property.1, by simpa only [shortestRoute_duration] using t.property.2⟩, rfl⟩

def geodesicPoint {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0)
    (t : Icc (0 : ℝ) (dist p q)) : IntrinsicPoint K hK P0 :=
  p.embed ((shortestRoute p q).prefixPoint hK (geodesicIndex p q t))

theorem geodesicPoint_isometry {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0) :
    Isometry (geodesicPoint p q) :=
  p.embed_isometry.comp (((shortestRoute p q).prefixPoint_isometry hK
    (shortestRoute_minimal p q)).comp (geodesicIndex_isometry p q))

theorem geodesicPoint_value {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0)
    (t : Icc (0 : ℝ) (dist p q)) :
    (geodesicPoint p q t).value = product p.value
      (lipSignature (shortestRoute p q).curve (shortestRoute p q).lipschitz 0 t.val t.property.1) := rfl

theorem geodesicPoint_source {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0) :
    geodesicPoint p q ⟨0, le_rfl, dist_nonneg⟩ = p := by
  apply IntrinsicPoint.ext
  rw [geodesicPoint_value, lipSignature_same, product_unit_right]

theorem geodesicPoint_target {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0) :
    geodesicPoint p q ⟨dist p q, dist_nonneg, le_rfl⟩ = q := by
  apply IntrinsicPoint.ext
  rw [geodesicPoint_value]
  exact (congrArg (product p.value) (lipSignature_endpoint_congr
    (shortestRoute p q).curve (shortestRoute p q).lipschitz dist_nonneg
    (shortestRoute p q).nonneg (shortestRoute_duration p q).symm)).trans (shortestRoute p q).terminal

def intrinsicGeodesicSystem {ι : Type*} [Fintype ι] (K : Set (Series ι))
    (hK : IsClosed K) (P0 : Series ι) :
    LinearInputCurveWordGeodesicTree.GeodesicSystem (IntrinsicPoint K hK P0) where
  path := geodesicPoint
  isometry := geodesicPoint_isometry
  source := geodesicPoint_source
  target := geodesicPoint_target

theorem shortestRoute_lift_injective {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0) :
    Function.Injective (fun t : Icc (0 : ℝ) (shortestRoute p q).duration =>
      product p.value (lipSignature (shortestRoute p q).curve
        (shortestRoute p q).lipschitz 0 t.val t.property.1)) := by
  intro s t he
  apply ((shortestRoute p q).prefixPoint_isometry hK (shortestRoute_minimal p q)).injective
  exact IntrinsicPoint.ext he

theorem geodesicPoint_value_range {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0) :
    IntrinsicPoint.value '' Set.range (geodesicPoint p q) =
      Set.range (fun t : Icc (0 : ℝ) (shortestRoute p q).duration =>
        product p.value (lipSignature (shortestRoute p q).curve
          (shortestRoute p q).lipschitz 0 t.val t.property.1)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨geodesicIndex p q t, rfl⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨u, rfl⟩ := geodesicIndex_surjective p q t
    exact ⟨geodesicPoint p q u, ⟨u, rfl⟩, rfl⟩

open LinearInputCurveWordBVReduced LinearInputCurveWordBVArc

theorem Route.exists_arcLength {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) :
    ∃ q : Route K P Q,
      q.duration = variationLength r.curve 0 r.duration ∧
      variationLength q.curve 0 q.duration = q.duration ∧
      Set.range (fun t : Icc (0 : ℝ) q.duration =>
        product P (lipSignature q.curve q.lipschitz 0 t.val t.property.1)) =
      Set.range (fun t : Icc (0 : ℝ) r.duration =>
        product P (lipSignature r.curve r.lipschitz 0 t.val t.property.1)) := by
  obtain ⟨G, hG, hstart, hvar, _, hrange, hend⟩ :=
    arcLength_signature_range_factorization r.nonneg 0 P r.controlled
  have hlength : variationLength (pathExtension r.nonneg r.controlled.val) 0 r.duration =
      variationLength r.curve 0 r.duration := by
    exact congrArg ENNReal.toReal (eVariationOn.congr (fun t ht => r.controlled_eq ht))
  let q : Route K P Q := {
    duration := variationLength (pathExtension r.nonneg r.controlled.val) 0 r.duration
    nonneg := ENNReal.toReal_nonneg
    curve := G
    lipschitz := hG
    initial := hstart
    terminal := hend.trans r.controlled_admissible.1
    within := by
      intro t ht
      have hm : product P (lipSignature G hG 0 t ht.1) ∈
          basedSignatureRange r.nonneg 0 P r.controlled := hrange ▸ ⟨⟨t, ht⟩, rfl⟩
      obtain ⟨u, hu⟩ := hm
      rw [← hu]
      exact r.controlled_admissible.2 u }
  refine ⟨q, hlength, hvar, hrange.trans ?_⟩
  unfold basedSignatureRange
  congr 1
  funext t
  exact congrArg (product P) (r.controlled_prefix t.property)

def Route.arcLengthRoute {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) : Route K P Q :=
  r.exists_arcLength.choose

theorem Route.arcLengthRoute_duration {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) :
    r.arcLengthRoute.duration = variationLength r.curve 0 r.duration :=
  r.exists_arcLength.choose_spec.1

theorem Route.arcLengthRoute_variation {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) :
    variationLength r.arcLengthRoute.curve 0 r.arcLengthRoute.duration = r.arcLengthRoute.duration :=
  r.exists_arcLength.choose_spec.2.1

theorem Route.arcLengthRoute_image {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) :
    Set.range (fun t : Icc (0 : ℝ) r.arcLengthRoute.duration =>
      product P (lipSignature r.arcLengthRoute.curve r.arcLengthRoute.lipschitz 0 t.val t.property.1)) =
    Set.range (fun t : Icc (0 : ℝ) r.duration =>
      product P (lipSignature r.curve r.lipschitz 0 t.val t.property.1)) :=
  r.exists_arcLength.choose_spec.2.2

/-- A shortest bounded-speed route has no unused time: its duration is
exactly its actual variation. -/
theorem Route.shortest_variation {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q)
    (hmin : ∀ q : Route K P Q, r.duration ≤ q.duration) :
    variationLength r.curve 0 r.duration = r.duration := by
  apply le_antisymm
  · simpa only [sub_zero] using unitLipschitz_variation_toReal_le r.lipschitz r.nonneg
  · exact (hmin r.arcLengthRoute).trans_eq r.arcLengthRoute_duration

theorem Route.shortest_variation_minimal {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q)
    (hmin : ∀ q : Route K P Q, r.duration ≤ q.duration) (q : Route K P Q) :
    variationLength r.curve 0 r.duration ≤ variationLength q.curve 0 q.duration := by
  rw [r.shortest_variation hmin]
  exact (hmin q.arcLengthRoute).trans_eq q.arcLengthRoute_duration

theorem intrinsicDist_le_variation {ι : Type*} [Fintype ι]
    {K : Set (Series ι)} {P Q : Series ι} (r : Route K P Q) :
    intrinsicDist K P Q ≤ variationLength r.curve 0 r.duration :=
  (intrinsicDist_le_duration r.arcLengthRoute).trans_eq r.arcLengthRoute_duration

theorem shortestRoute_variation {ι : Type*} [Fintype ι] {K : Set (Series ι)}
    {hK : IsClosed K} {P0 : Series ι} (p q : IntrinsicPoint K hK P0) :
    variationLength (shortestRoute p q).curve 0 (shortestRoute p q).duration = dist p q :=
  ((shortestRoute p q).shortest_variation (shortestRoute_minimal p q)).trans (shortestRoute_duration p q)


end LinearInputCurveWordBVIntrinsic
