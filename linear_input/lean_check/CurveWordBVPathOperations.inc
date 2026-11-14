/-!
Actual reversal and concatenation of continuous BV paths, with canonical
integral signatures.  Curve operations, variation bounds and signature
identities are proved for the constructed paths.
-/

noncomputable section

namespace LinearInputCurveWordBVPathOperations

open Set
open LinearInputCurveWordBoundedVariation LinearInputCurveWordBVCanonical
open LinearInputCurveWordStieltjes LinearInputCurveWordFormalSeries
open LinearInputCurveWordTreeLike LinearInputCurveWordTreeLimit

def reverseTime (a b t : ℝ) : ℝ := a + b - t

def reversePath {E : Type*} (γ : ℝ → E) (a b : ℝ) : ℝ → E := γ ∘ reverseTime a b

theorem reverseTime_continuous (a b : ℝ) : Continuous (reverseTime a b) :=
  continuous_const.sub continuous_id

theorem reverseTime_antitone (a b : ℝ) : Antitone (reverseTime a b) := by
  intro x y hxy
  exact sub_le_sub_left hxy _

theorem reverseTime_mem {a b t : ℝ} (ht : t ∈ Icc a b) : reverseTime a b t ∈ Icc a b := by
  dsimp [reverseTime]
  constructor <;> linarith [ht.1, ht.2]

theorem reverseTime_involutive (a b : ℝ) : Function.Involutive (reverseTime a b) := by
  intro t
  dsimp [reverseTime]
  ring

theorem reverseTime_image (a b : ℝ) : reverseTime a b '' Icc a b = Icc a b := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact reverseTime_mem ht
  · intro t ht
    exact ⟨reverseTime a b t, reverseTime_mem ht, reverseTime_involutive a b t⟩

theorem reversePath_variation {E : Type*} [PseudoEMetricSpace E]
    (γ : ℝ → E) (a b : ℝ) :
    eVariationOn (reversePath γ a b) (Icc a b) = eVariationOn γ (Icc a b) := by
  rw [reversePath, eVariationOn.comp_eq_of_antitoneOn γ (reverseTime a b)
    ((reverseTime_antitone a b).antitoneOn (Icc a b)), reverseTime_image]

theorem reversePath_boundedVariation {E : Type*} [PseudoEMetricSpace E]
    {γ : ℝ → E} {a b : ℝ} (hγ : BoundedVariationOn γ (Icc a b)) :
    BoundedVariationOn (reversePath γ a b) (Icc a b) := by
  change eVariationOn (reversePath γ a b) (Icc a b) ≠ ⊤
  rwa [reversePath_variation]

theorem reversePath_continuousOn {E : Type*} [TopologicalSpace E]
    {γ : ℝ → E} {a b : ℝ} (hc : ContinuousOn γ (Icc a b)) :
    ContinuousOn (reversePath γ a b) (Icc a b) :=
  hc.comp (reverseTime_continuous a b).continuousOn (fun _ ht => reverseTime_mem ht)

theorem reversePath_reversePath {E : Type*} (γ : ℝ → E) (a b : ℝ) :
    reversePath (reversePath γ a b) a b = γ := by
  funext t
  exact congrArg γ (reverseTime_involutive a b t)

def joinCurve {E : Type*} (b : ℝ) (γ η : ℝ → E) : ℝ → E :=
  fun t => if t ≤ b then γ t else η t

theorem joinCurve_left {E : Type*} (b : ℝ) (γ η : ℝ → E) {t : ℝ} (ht : t ≤ b) :
    joinCurve b γ η t = γ t := ite_eq_left ht

theorem joinCurve_right {E : Type*} {b : ℝ} {γ η : ℝ → E} (he : γ b = η b)
    {t : ℝ} (ht : b ≤ t) : joinCurve b γ η t = η t := by
  by_cases htb : t ≤ b
  · have ht' : t = b := le_antisymm htb ht
    rw [ht', joinCurve_left b γ η le_rfl, he]
  · exact ite_eq_right htb

theorem joinCurve_continuousOn {E : Type*} [TopologicalSpace E] {γ η : ℝ → E}
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (he : γ b = η b)
    (hγ : ContinuousOn γ (Icc a b)) (hη : ContinuousOn η (Icc b c)) :
    ContinuousOn (joinCurve b γ η) (Icc a c) := by
  rw [← Icc_union_Icc_eq_Icc hab hbc]
  apply ContinuousOn.union_of_isClosed _ _ isClosed_Icc isClosed_Icc
  · exact hγ.congr (fun t ht => joinCurve_left b γ η ht.2)
  · exact hη.congr (fun t ht => joinCurve_right he ht.1)

theorem joinCurve_variation {E : Type*} [PseudoEMetricSpace E] {γ η : ℝ → E}
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (he : γ b = η b) :
    eVariationOn (joinCurve b γ η) (Icc a c) =
      eVariationOn γ (Icc a b) + eVariationOn η (Icc b c) := by
  have h := eVariationOn.Icc_add_Icc (joinCurve b γ η) (s := univ) hab hbc (mem_univ b)
  simp only [univ_inter] at h
  rw [← h, eVariationOn.congr (fun t (ht : t ∈ Icc a b) => joinCurve_left b γ η ht.2),
    eVariationOn.congr (fun t (ht : t ∈ Icc b c) => joinCurve_right he ht.1)]

theorem joinCurve_boundedVariation {E : Type*} [PseudoEMetricSpace E] {γ η : ℝ → E}
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (he : γ b = η b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hη : BoundedVariationOn η (Icc b c)) :
    BoundedVariationOn (joinCurve b γ η) (Icc a c) := by
  change eVariationOn (joinCurve b γ η) (Icc a c) ≠ ⊤
  rw [joinCurve_variation hab hbc he]
  exact ENNReal.add_ne_top.mpr ⟨hγ, hη⟩

/-- Canonical signatures satisfy Chen on actual compact restrictions of the
same continuous BV path, with no globally chosen representation in the API. -/
theorem pathSignature_split {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hγ : BoundedVariationOn γ (Icc a c)) (hc : ContinuousOn γ (Icc a c)) :
    pathSignature γ (hab.trans hbc) hγ hc =
      product (pathSignature γ hab (hγ.mono (Icc_subset_Icc le_rfl hbc))
        (hc.mono (Icc_subset_Icc le_rfl hbc)))
      (pathSignature γ hbc (hγ.mono (Icc_subset_Icc hab le_rfl))
        (hc.mono (Icc_subset_Icc hab le_rfl))) := by
  let p (i : ι) := canonicalPositive (hab.trans hbc)
    (coordinate_boundedVariation hγ i) (coordinate_continuousOn hc i)
  let m (i : ι) := canonicalNegative (hab.trans hbc)
    (coordinate_boundedVariation hγ i) (coordinate_continuousOn hc i)
  have hp (i : ι) : Continuous (p i : ℝ → ℝ) := canonicalPositive_continuous _ _ _
  have hm (i : ι) : Continuous (m i : ℝ → ℝ) := canonicalNegative_continuous _ _ _
  have hrep (i : ι) : RepresentsOn (p i) (m i) (fun t => γ t i) a c :=
    canonical_represents _ _ _
  have hleft : pathSignature γ hab (hγ.mono (Icc_subset_Icc le_rfl hbc))
      (hc.mono (Icc_subset_Icc le_rfl hbc)) = stieltjesSignature p m a b := by
    funext w
    apply pathSignature_eq_representation γ hab _ _ p m hp hm _ w
    intro i x hx y hy
    exact hrep i x ⟨hx.1, hx.2.trans hbc⟩ y ⟨hy.1, hy.2.trans hbc⟩
  have hright : pathSignature γ hbc (hγ.mono (Icc_subset_Icc hab le_rfl))
      (hc.mono (Icc_subset_Icc hab le_rfl)) = stieltjesSignature p m b c := by
    funext w
    apply pathSignature_eq_representation γ hbc _ _ p m hp hm _ w
    intro i x hx y hy
    exact hrep i x ⟨hab.trans hx.1, hx.2⟩ y ⟨hab.trans hy.1, hy.2⟩
  rw [hleft, hright]
  exact LinearInputCurveWordBVAlgebra.signature_product p m hp hm a b c

/-- Concatenating two separately given matching BV paths multiplies their
actual canonical signatures in chronological order. -/
theorem pathSignature_join {ι : Type*} [Fintype ι] (γ η : ℝ → ι → ℝ)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (he : γ b = η b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hcγ : ContinuousOn γ (Icc a b))
    (hη : BoundedVariationOn η (Icc b c)) (hcη : ContinuousOn η (Icc b c)) :
    pathSignature (joinCurve b γ η) (hab.trans hbc)
      (joinCurve_boundedVariation hab hbc he hγ hη)
      (joinCurve_continuousOn hab hbc he hcγ hcη) =
      product (pathSignature γ hab hγ hcγ) (pathSignature η hbc hη hcη) := by
  rw [pathSignature_split (joinCurve b γ η) hab hbc]
  congr 1
  · funext w
    exact pathSignature_congr hab _ _ hγ hcγ (fun _ ht => joinCurve_left b γ η ht.2) w
  · funext w
    exact pathSignature_congr hbc _ _ hη hcη (fun _ ht => joinCurve_right he ht.1) w

theorem reversePath_length {E : Type*} [PseudoEMetricSpace E] (γ : ℝ → E) (a b : ℝ) :
    variationLength (reversePath γ a b) a b = variationLength γ a b := by
  unfold variationLength
  rw [reversePath_variation]

theorem joinCurve_length {E : Type*} [PseudoEMetricSpace E] {γ η : ℝ → E}
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (he : γ b = η b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hη : BoundedVariationOn η (Icc b c)) :
    variationLength (joinCurve b γ η) a c = variationLength γ a b + variationLength η b c := by
  unfold variationLength
  rw [joinCurve_variation hab hbc he, ENNReal.toReal_add hγ hη]

/-- A closed continuous motion of the time parameter retraces the BV path
through a genuine geometric height, built from its actual variation clock. -/
theorem retrace_treeLike {E : Type*} [MetricSpace E] (γ : ℝ → E)
    {a b c d : ℝ} (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc c d)) (hm : MapsTo φ (Icc c d) (Icc a b))
    (hclosed : φ c = φ d) : TreeLike (γ ∘ φ) c d := by
  let clock := variationClock γ a b ∘ φ
  have hclock : ContinuousOn clock (Icc c d) :=
    (variation_clock_continuousOn hγ hc (left_mem_Icc.mpr hab)).comp hφ hm
  have hclockclosed : clock c = clock d := by dsimp [clock]; rw [hclosed]
  obtain ⟨_, H, hH⟩ := real_closed_treeLike hclock hclockclosed
  refine ⟨hc.comp hφ hm, H, hH.1, hH.2.1, hH.2.2.1, hH.2.2.2.1, ?_⟩
  intro s hs t ht
  obtain ⟨r, hr, hb⟩ := hH.2.2.2.2 s hs t ht
  refine ⟨r, hr, le_trans ?_ hb⟩
  have he := distance_le_variation_difference hγ.locallyBoundedVariationOn
    (left_mem_Icc.mpr hab) (hm hs) (hm ⟨hs.1.trans ht.1, ht.2⟩)
  simpa only [clock, variationClock, Function.comp_apply, Real.dist_eq, abs_sub_comm] using he

theorem reparam_mapsTo_endpoints {φ : ℝ → ℝ} {a b c d : ℝ} (hcd : c ≤ d)
    (hm : MonotoneOn φ (Icc c d)) (ha : φ c = a) (hb : φ d = b) :
    MapsTo φ (Icc c d) (Icc a b) := by
  simpa only [ha, hb] using clock_mapsTo hcd hm

theorem reparam_bv_endpoints {E : Type*} [PseudoEMetricSpace E] {γ : ℝ → E}
    {φ : ℝ → ℝ} {a b c d : ℝ} (hcd : c ≤ d) (hm : MonotoneOn φ (Icc c d))
    (ha : φ c = a) (hb : φ d = b) (hγ : BoundedVariationOn γ (Icc a b)) :
    BoundedVariationOn (γ ∘ φ) (Icc c d) :=
  ne_top_of_le_ne_top hγ (eVariationOn.comp_le_of_monotoneOn γ φ hm
    (reparam_mapsTo_endpoints hcd hm ha hb))

theorem reparam_cont_endpoints {E : Type*} [TopologicalSpace E] {γ : ℝ → E}
    {φ : ℝ → ℝ} {a b c d : ℝ} (hcd : c ≤ d) (hm : MonotoneOn φ (Icc c d))
    (hφ : ContinuousOn φ (Icc c d)) (ha : φ c = a) (hb : φ d = b)
    (hc : ContinuousOn γ (Icc a b)) : ContinuousOn (γ ∘ φ) (Icc c d) :=
  hc.comp hφ (reparam_mapsTo_endpoints hcd hm ha hb)

theorem pathSignature_reparametrize_endpoints {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    {φ : ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hm : MonotoneOn φ (Icc c d)) (hφ : ContinuousOn φ (Icc c d))
    (ha : φ c = a) (hb : φ d = b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    pathSignature (γ ∘ φ) hcd (reparam_bv_endpoints hcd hm ha hb hγ)
      (reparam_cont_endpoints hcd hm hφ ha hb hc) = pathSignature γ hab hγ hc := by
  funext w
  have hf' : BoundedVariationOn γ (Icc (φ c) (φ d)) := by simpa only [ha, hb] using hγ
  have hc' : ContinuousOn γ (Icc (φ c) (φ d)) := by simpa only [ha, hb] using hc
  have he := pathSignature_reparametrize γ hcd hm hφ hf' hc' w
  simpa only [ha, hb] using he

def retraceTime (b t : ℝ) : ℝ := min t (2 * b - t)

theorem retraceTime_continuous (b : ℝ) : Continuous (retraceTime b) :=
  continuous_id.min (continuous_const.sub continuous_id)

theorem retraceTime_left {b t : ℝ} (ht : t ≤ b) : retraceTime b t = t :=
  min_eq_left (by linarith)

theorem retraceTime_right {b t : ℝ} (ht : b ≤ t) : retraceTime b t = 2 * b - t :=
  min_eq_right (by linarith)

theorem retraceTime_mem {a b t : ℝ} (ht : t ∈ Icc a (2 * b - a)) :
    retraceTime b t ∈ Icc a b := by
  refine ⟨le_min ht.1 (by linarith [ht.2]), ?_⟩
  by_cases htb : t ≤ b
  · rw [retraceTime_left htb]; exact htb
  · rw [retraceTime_right (le_of_not_ge htb)]; linarith

def mirrorPath {E : Type*} (γ : ℝ → E) (b : ℝ) : ℝ → E := fun t => γ (2 * b - t)

theorem join_mirror_eq_retrace {E : Type*} (γ : ℝ → E) (b : ℝ) :
    joinCurve b γ (mirrorPath γ b) = γ ∘ retraceTime b := by
  funext t
  by_cases ht : t ≤ b
  · simp only [joinCurve, ite_eq_left ht, Function.comp_apply, retraceTime_left ht]
  · simp only [joinCurve, ite_eq_right ht, Function.comp_apply,
      retraceTime_right (le_of_not_ge ht), mirrorPath]

theorem mirrorPath_boundedVariation {E : Type*} [PseudoEMetricSpace E]
    {γ : ℝ → E} {a b : ℝ} (hγ : BoundedVariationOn γ (Icc a b)) :
    BoundedVariationOn (mirrorPath γ b) (Icc b (2 * b - a)) := by
  apply ne_top_of_le_ne_top hγ
  apply eVariationOn.comp_le_of_antitoneOn γ (fun t => 2 * b - t)
    (fun _ _ _ _ h => sub_le_sub_left h _)
  intro t ht
  constructor <;> linarith [ht.1, ht.2]

theorem mirrorPath_continuousOn {E : Type*} [TopologicalSpace E]
    {γ : ℝ → E} {a b : ℝ} (hc : ContinuousOn γ (Icc a b)) :
    ContinuousOn (mirrorPath γ b) (Icc b (2 * b - a)) := by
  apply hc.comp (continuous_const.sub continuous_id).continuousOn
  intro t ht
  change a ≤ 2 * b - t ∧ 2 * b - t ≤ b
  constructor <;> linarith [ht.1, ht.2]

theorem mirrorPath_matches {E : Type*} (γ : ℝ → E) (b : ℝ) : γ b = mirrorPath γ b b := by
  dsimp [mirrorPath]
  congr 1
  ring

theorem backtrack_treeLike {E : Type*} [MetricSpace E] (γ : ℝ → E)
    {a b : ℝ} (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) : TreeLike (joinCurve b γ (mirrorPath γ b)) a (2 * b - a) := by
  rw [join_mirror_eq_retrace]
  apply retrace_treeLike γ hab hγ hc (retraceTime_continuous b).continuousOn
    (fun _ ht => retraceTime_mem ht)
  rw [retraceTime_left hab, retraceTime_right (by linarith : b ≤ 2 * b - a)]
  ring

theorem pathSignature_mirror {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    {a b : ℝ} (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) :
    pathSignature (mirrorPath γ b) (show b ≤ 2 * b - a by linarith)
      (mirrorPath_boundedVariation hγ) (mirrorPath_continuousOn hc) =
    pathSignature (reversePath γ a b) hab
      (reversePath_boundedVariation hγ) (reversePath_continuousOn hc) := by
  let φ : ℝ → ℝ := fun t => t - (b - a)
  have hbc : b ≤ 2 * b - a := by linarith
  have hm : MonotoneOn φ (Icc b (2 * b - a)) :=
    fun _ _ _ _ h => sub_le_sub_right h _
  have hφ : ContinuousOn φ (Icc b (2 * b - a)) :=
    (continuous_id.sub continuous_const).continuousOn
  have ha : φ b = a := by dsimp [φ]; ring
  have hb : φ (2 * b - a) = b := by dsimp [φ]; ring
  have hcomp : reversePath γ a b ∘ φ = mirrorPath γ b := by
    funext t
    dsimp [reversePath, reverseTime, mirrorPath, φ, Function.comp_def]
    congr 1
    ring
  have he := pathSignature_reparametrize_endpoints (reversePath γ a b) hab hbc hm hφ ha hb
    (reversePath_boundedVariation hγ) (reversePath_continuousOn hc)
  refine Eq.trans ?_ he
  funext w
  exact pathSignature_congr hbc _ _ _ _ (fun t _ => (congrFun hcomp t).symm) w

/-- Forward travel followed by actual reversed travel has unit signature.
The proof uses the explicit variation-clock height of the retraced path and
the proved BV tree-height theorem, followed by actual concatenation Chen. -/
theorem pathSignature_product_reverse {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    {a b : ℝ} (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) :
    product (pathSignature γ hab hγ hc)
      (pathSignature (reversePath γ a b) hab
        (reversePath_boundedVariation hγ) (reversePath_continuousOn hc)) = unitSeries := by
  have hbc : b ≤ 2 * b - a := by linarith
  have hunit := treeLike_pathSignature_eq_unit (joinCurve b γ (mirrorPath γ b)) (hab.trans hbc)
    (joinCurve_boundedVariation hab hbc (mirrorPath_matches γ b) hγ (mirrorPath_boundedVariation hγ))
    (backtrack_treeLike γ hab hγ hc)
  rw [pathSignature_join γ (mirrorPath γ b) hab hbc (mirrorPath_matches γ b)
    hγ hc (mirrorPath_boundedVariation hγ) (mirrorPath_continuousOn hc),
    pathSignature_mirror γ hab hγ hc] at hunit
  exact hunit

theorem stieltjesSignature_same {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (a : ℝ) : stieltjesSignature p m a a = unitSeries := by
  funext w
  cases w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w i =>
    simp [stieltjesSignature, List.reverse_append, reverseStieltjes, stieltjesIntegral, unitSeries]
    cases w <;> rfl

theorem stieltjesSignature_inverse {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀i, Continuous (p i : ℝ → ℝ)) (hm : ∀i, Continuous (m i : ℝ → ℝ)) (a b : ℝ) :
    product (stieltjesSignature p m a b) (stieltjesSignature p m b a) = unitSeries ∧
    product (stieltjesSignature p m b a) (stieltjesSignature p m a b) = unitSeries := by
  constructor
  · rw [← LinearInputCurveWordBVAlgebra.signature_product p m hp hm a b a, stieltjesSignature_same]
  · rw [← LinearInputCurveWordBVAlgebra.signature_product p m hp hm b a b, stieltjesSignature_same]

/-- The signature of the time-reversed path is exactly the oriented reverse
interval signature of the original canonical continuous Stieltjes pair. -/
theorem pathSignature_reverse {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    {a b : ℝ} (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) :
    pathSignature (reversePath γ a b) hab
      (reversePath_boundedVariation hγ) (reversePath_continuousOn hc) =
      stieltjesSignature
        (fun i => canonicalPositive hab (coordinate_boundedVariation hγ i) (coordinate_continuousOn hc i))
        (fun i => canonicalNegative hab (coordinate_boundedVariation hγ i) (coordinate_continuousOn hc i)) b a := by
  let p (i : ι) := canonicalPositive hab (coordinate_boundedVariation hγ i) (coordinate_continuousOn hc i)
  let m (i : ι) := canonicalNegative hab (coordinate_boundedVariation hγ i) (coordinate_continuousOn hc i)
  let S := pathSignature γ hab hγ hc
  let R := pathSignature (reversePath γ a b) hab
    (reversePath_boundedVariation hγ) (reversePath_continuousOn hc)
  let O := stieltjesSignature p m b a
  have hOS : product O S = unitSeries := (stieltjesSignature_inverse p m
    (fun _ => canonicalPositive_continuous _ _ _) (fun _ => canonicalNegative_continuous _ _ _) a b).2
  have hSR : product S R = unitSeries := pathSignature_product_reverse γ hab hγ hc
  change R = O
  calc
    R = product unitSeries R := (product_unit_left R).symm
    _ = product (product O S) R := by rw [hOS]
    _ = product O (product S R) := product_assoc O S R
    _ = O := by rw [hSR, product_unit_right]

theorem pathSignature_reverse_product {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ)
    {a b : ℝ} (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b))
    (hc : ContinuousOn γ (Icc a b)) :
    product (pathSignature (reversePath γ a b) hab
      (reversePath_boundedVariation hγ) (reversePath_continuousOn hc))
      (pathSignature γ hab hγ hc) = unitSeries := by
  rw [pathSignature_reverse γ hab hγ hc]
  exact (stieltjesSignature_inverse _ _
    (fun _ => canonicalPositive_continuous _ _ _) (fun _ => canonicalNegative_continuous _ _ _) a b).2

/-- The separately given paths may have arbitrary parametrizations on the
same compact interval. Matching terminal points suffice for the actual
forward/reverse concatenation. -/
theorem pathSignature_eq_iff_join_reverse_unit {ι : Type*} [Fintype ι]
    (γ η : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b) (he : γ b = η b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hcγ : ContinuousOn γ (Icc a b))
    (hη : BoundedVariationOn η (Icc a b)) (hcη : ContinuousOn η (Icc a b)) :
    pathSignature γ hab hγ hcγ = pathSignature η hab hη hcη ↔
      pathSignature (joinCurve b γ (mirrorPath η b)) (show a ≤ 2 * b - a by linarith)
        (joinCurve_boundedVariation hab (by linarith) (he.trans (mirrorPath_matches η b))
          hγ (mirrorPath_boundedVariation hη))
        (joinCurve_continuousOn hab (by linarith) (he.trans (mirrorPath_matches η b))
          hcγ (mirrorPath_continuousOn hcη)) = unitSeries := by
  rw [pathSignature_join γ (mirrorPath η b) hab (by linarith)
    (he.trans (mirrorPath_matches η b)) hγ hcγ (mirrorPath_boundedVariation hη)
    (mirrorPath_continuousOn hcη), pathSignature_mirror η hab hη hcη]
  constructor
  · intro hs
    rw [hs]
    exact pathSignature_product_reverse η hab hη hcη
  · intro hs
    let S := pathSignature γ hab hγ hcγ
    let T := pathSignature η hab hη hcη
    let R := pathSignature (reversePath η a b) hab
      (reversePath_boundedVariation hη) (reversePath_continuousOn hcη)
    have hRT : product R T = unitSeries := pathSignature_reverse_product η hab hη hcη
    change S = T
    calc
      S = product S unitSeries := (product_unit_right S).symm
      _ = product S (product R T) := by rw [hRT]
      _ = product (product S R) T := (product_assoc S R T).symm
      _ = T := by rw [hs, product_unit_left]

theorem join_reverse_endpoints {E : Type*} (γ η : ℝ → E) {a b : ℝ}
    (hab : a ≤ b) (he : γ b = η b) :
    joinCurve b γ (mirrorPath η b) a = γ a ∧
      joinCurve b γ (mirrorPath η b) (2 * b - a) = η a := by
  refine ⟨joinCurve_left b γ (mirrorPath η b) hab, ?_⟩
  rw [joinCurve_right (he.trans (mirrorPath_matches η b)) (by linarith)]
  dsimp [mirrorPath]
  congr 1
  ring

theorem join_reverse_closed {E : Type*} (γ η : ℝ → E) {a b : ℝ}
    (hab : a ≤ b) (hstart : γ a = η a) (hend : γ b = η b) :
    joinCurve b γ (mirrorPath η b) a = joinCurve b γ (mirrorPath η b) (2 * b - a) := by
  rw [(join_reverse_endpoints γ η hab hend).1, (join_reverse_endpoints γ η hab hend).2]
  exact hstart

theorem same_signature_of_treeLike_join_reverse {ι : Type*} [Fintype ι]
    (γ η : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b) (he : γ b = η b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hcγ : ContinuousOn γ (Icc a b))
    (hη : BoundedVariationOn η (Icc a b)) (hcη : ContinuousOn η (Icc a b))
    (htree : TreeLike (joinCurve b γ (mirrorPath η b)) a (2 * b - a)) :
    pathSignature γ hab hγ hcγ = pathSignature η hab hη hcη := by
  apply (pathSignature_eq_iff_join_reverse_unit γ η hab he hγ hcγ hη hcη).mpr
  exact treeLike_pathSignature_eq_unit _ (by linarith)
    (joinCurve_boundedVariation hab (by linarith) (he.trans (mirrorPath_matches η b))
      hγ (mirrorPath_boundedVariation hη)) htree

end LinearInputCurveWordBVPathOperations
