/-!
The pseudometric encoded by a continuous height, its separated metric
quotient, and the Lipschitz factorization of a path with that height.
-/

noncomputable section

namespace LinearInputCurveWordHeightMetric

open Set
open scoped NNReal
open LinearInputCurveWordTreeLike LinearInputCurveWordSignatureTree

def intervalMinimum (h : ℝ → ℝ) (s t : ℝ) : ℝ := sInf (h '' uIcc s t)

theorem intervalMinimum_symm (h : ℝ → ℝ) (s t : ℝ) :
    intervalMinimum h s t = intervalMinimum h t s := by
  simp only [intervalMinimum, uIcc_comm s t]

theorem intervalMinimum_self (h : ℝ → ℝ) (s : ℝ) : intervalMinimum h s s = h s := by
  simp [intervalMinimum]

theorem uIcc_subset_interval {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    uIcc s t ⊆ Icc a b := by
  intro r hr
  rcases mem_uIcc.mp hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

theorem intervalMinimum_attained {h : ℝ → ℝ} {a b s t : ℝ}
    (hh : ContinuousOn h (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∃ r ∈ uIcc s t, intervalMinimum h s t = h r ∧ ∀ q ∈ uIcc s t, h r ≤ h q :=
  isCompact_uIcc.exists_sInf_image_eq_and_le nonempty_uIcc
    (hh.mono (uIcc_subset_interval hs ht))

theorem intervalMinimum_le {h : ℝ → ℝ} {a b s t r : ℝ}
    (hh : ContinuousOn h (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hr : r ∈ uIcc s t) : intervalMinimum h s t ≤ h r := by
  obtain ⟨q, _, he, hb⟩ := intervalMinimum_attained hh hs ht
  rw [he]
  exact hb r hr

theorem min_le_intervalMinimum {h : ℝ → ℝ} {a b s t u : ℝ}
    (hh : ContinuousOn h (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hu : u ∈ Icc a b) :
    min (intervalMinimum h s t) (intervalMinimum h t u) ≤ intervalMinimum h s u := by
  obtain ⟨r, hr, he, _⟩ := intervalMinimum_attained hh hs hu
  rw [he]
  rcases uIcc_subset_uIcc_union_uIcc hr with hr | hr
  · exact (min_le_left _ _).trans (intervalMinimum_le hh hs ht hr)
  · exact (min_le_right _ _).trans (intervalMinimum_le hh ht hu hr)

def heightDist (h : ℝ → ℝ) (s t : ℝ) : ℝ := h s + h t - 2 * intervalMinimum h s t

theorem heightDist_self (h : ℝ → ℝ) (s : ℝ) : heightDist h s s = 0 := by
  rw [heightDist, intervalMinimum_self]
  ring

theorem heightDist_symm (h : ℝ → ℝ) (s t : ℝ) : heightDist h s t = heightDist h t s := by
  rw [heightDist, heightDist, intervalMinimum_symm h s t]
  ring

theorem heightDist_nonneg {h : ℝ → ℝ} {a b s t : ℝ}
    (hh : ContinuousOn h (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    0 ≤ heightDist h s t := by
  have h1 := intervalMinimum_le hh hs ht (left_mem_uIcc : s ∈ uIcc s t)
  have h2 := intervalMinimum_le hh hs ht (right_mem_uIcc : t ∈ uIcc s t)
  unfold heightDist
  linarith

theorem heightDist_zero_iff {h : ℝ → ℝ} {a b s t : ℝ}
    (hh : ContinuousOn h (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    heightDist h s t = 0 ↔ h s = h t ∧ intervalMinimum h s t = h s := by
  have h1 := intervalMinimum_le hh hs ht (left_mem_uIcc : s ∈ uIcc s t)
  have h2 := intervalMinimum_le hh hs ht (right_mem_uIcc : t ∈ uIcc s t)
  unfold heightDist
  constructor
  · intro he
    constructor <;> linarith
  · rintro ⟨he, hm⟩
    linarith

theorem heightDist_triangle {h : ℝ → ℝ} {a b s t u : ℝ}
    (hh : ContinuousOn h (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hu : u ∈ Icc a b) : heightDist h s u ≤ heightDist h s t + heightDist h t u := by
  have hm := min_le_intervalMinimum hh hs ht hu
  have h1 := intervalMinimum_le hh hs ht (right_mem_uIcc : t ∈ uIcc s t)
  have h2 := intervalMinimum_le hh ht hu (left_mem_uIcc : t ∈ uIcc t u)
  unfold heightDist
  rcases le_total (intervalMinimum h s t) (intervalMinimum h t u) with hc | hc
  · rw [min_eq_left hc] at hm
    linarith
  · rw [min_eq_right hc] at hm
    linarith

/-- A purely algebraic consequence of the rooted minimum inequality. -/
theorem similarity_fourPoint {X : Type*} (m : X → X → ℝ)
    (hsym : ∀ x y, m x y = m y x)
    (hmin : ∀ x y z, min (m x y) (m y z) ≤ m x z) (a b c d : X) :
    min (m a b + m c d) (m a d + m b c) ≤ m a c + m b d := by
  have aux (a b c d : X) (hac : m a c ≤ m b d) :
      min (m a b + m c d) (m a d + m b c) ≤ m a c + m b d := by
    have habc := (min_le_iff.mp (hmin a b c))
    have hadc := (min_le_iff.mp (hmin a d c))
    have hbcd := (min_le_iff.mp (hmin b c d))
    have hbad := (min_le_iff.mp (hmin b a d))
    rw [hsym d c] at hadc
    rw [hsym b a] at hbad
    rcases habc with hab | hbc <;> rcases hadc with had | hcd
    · rcases hbcd with hbc | hcd
      · exact (min_le_right _ _).trans (by linarith)
      · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
    · rcases hbad with hab | had
      · exact (min_le_left _ _).trans (by linarith)
      · exact (min_le_right _ _).trans (by linarith)
  rcases le_total (m a c) (m b d) with hac | hbd
  · exact aux a b c d hac
  · have h := aux b a d c hbd
    simpa only [hsym b a, hsym d c, hsym d a, hsym c a, add_comm,
      min_comm] using h

/-- The time domain is a distinct type so the height pseudometric does not
replace the usual Euclidean metric on an interval. -/
structure HeightTime (h : ℝ → ℝ) (a b : ℝ) (hh : ContinuousOn h (Icc a b)) where
  val : ℝ
  mem_interval : val ∈ Icc a b

instance {h : ℝ → ℝ} {a b : ℝ} {hh : ContinuousOn h (Icc a b)} :
    PseudoMetricSpace (HeightTime h a b hh) where
  dist s t := heightDist h s.val t.val
  dist_self s := heightDist_self h s.val
  dist_comm s t := heightDist_symm h s.val t.val
  dist_triangle s t u := heightDist_triangle hh s.mem_interval t.mem_interval u.mem_interval

theorem heightTime_fourPoint {h : ℝ → ℝ} {a b : ℝ} (hh : ContinuousOn h (Icc a b)) :
    @FourPoint (HeightTime h a b hh) _ := by
  intro s t u v
  have hm := similarity_fourPoint (fun x y : HeightTime h a b hh => intervalMinimum h x.val y.val)
    (fun x y => intervalMinimum_symm h x.val y.val)
    (fun x y z => min_le_intervalMinimum hh x.mem_interval y.mem_interval z.mem_interval) s t u v
  change heightDist h s.val u.val + heightDist h t.val v.val ≤
    max (heightDist h s.val t.val + heightDist h u.val v.val)
      (heightDist h s.val v.val + heightDist h t.val u.val)
  unfold heightDist
  rcases min_le_iff.mp hm with hm | hm
  · exact le_trans (by linarith) (le_max_left _ _)
  · exact le_trans (by linarith) (le_max_right _ _)

abbrev HeightQuotient (h : ℝ → ℝ) (a b : ℝ) (hh : ContinuousOn h (Icc a b)) :=
  SeparationQuotient (HeightTime h a b hh)

theorem heightQuotient_fourPoint {h : ℝ → ℝ} {a b : ℝ} (hh : ContinuousOn h (Icc a b)) :
    @FourPoint (HeightQuotient h a b hh) _ := by
  intro s t u v
  obtain ⟨s, rfl⟩ := SeparationQuotient.surjective_mk s
  obtain ⟨t, rfl⟩ := SeparationQuotient.surjective_mk t
  obtain ⟨u, rfl⟩ := SeparationQuotient.surjective_mk u
  obtain ⟨v, rfl⟩ := SeparationQuotient.surjective_mk v
  exact heightTime_fourPoint hh s t u v

def timeMap {h : ℝ → ℝ} {a b : ℝ} (hh : ContinuousOn h (Icc a b)) :
    Icc a b → HeightTime h a b hh := fun t => ⟨t.val, t.property⟩

theorem interval_point_dist_le {s t r : ℝ} (hr : r ∈ uIcc s t) : dist r s ≤ dist t s := by
  rw [Real.dist_eq, Real.dist_eq]
  rcases mem_uIcc.mp hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr h1), abs_of_nonneg (sub_nonneg.mpr (h1.trans h2))]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr h2), abs_of_nonpos (sub_nonpos.mpr (h1.trans h2))]
    linarith

/-- Continuity of the height is enough to make the canonical time map
continuous for the new pseudometric. -/
theorem timeMap_continuous {h : ℝ → ℝ} {a b : ℝ} (hh : ContinuousOn h (Icc a b)) :
    Continuous (timeMap hh) := by
  apply Metric.continuous_iff.mpr
  intro s ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousOn_iff.mp hh s.val s.property (ε / 3) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  change dist t.val s.val < δ at ht
  obtain ⟨r, hr, he, _⟩ := intervalMinimum_attained hh s.property t.property
  have hri : r ∈ Icc a b := uIcc_subset_interval s.property t.property hr
  have hrδ := lt_of_le_of_lt (interval_point_dist_le hr) ht
  have htr := hb t.val t.property ht
  have hrr := hb r hri hrδ
  rw [Real.dist_eq] at htr hrr
  change heightDist h t.val s.val < ε
  rw [heightDist_symm h t.val s.val, heightDist, he]
  have ht' := abs_lt.mp htr
  have hr' := abs_lt.mp hrr
  linarith

theorem timeMap_surjective {h : ℝ → ℝ} {a b : ℝ} (hh : ContinuousOn h (Icc a b)) :
    Function.Surjective (timeMap hh) := by
  intro t
  exact ⟨⟨t.val, t.mem_interval⟩, by cases t; rfl⟩

def quotientTime {h : ℝ → ℝ} {a b : ℝ} (hh : ContinuousOn h (Icc a b)) :
    Icc a b → HeightQuotient h a b hh := SeparationQuotient.mk ∘ timeMap hh

theorem quotientTime_continuous {h : ℝ → ℝ} {a b : ℝ} (hh : ContinuousOn h (Icc a b)) :
    Continuous (quotientTime hh) :=
  SeparationQuotient.continuous_mk.comp (timeMap_continuous hh)

theorem quotientTime_surjective {h : ℝ → ℝ} {a b : ℝ} (hh : ContinuousOn h (Icc a b)) :
    Function.Surjective (quotientTime hh) :=
  SeparationQuotient.surjective_mk.comp (timeMap_surjective hh)

theorem quotientTime_eq_iff {h : ℝ → ℝ} {a b : ℝ} (hh : ContinuousOn h (Icc a b))
    (s t : Icc a b) : quotientTime hh s = quotientTime hh t ↔
      h s = h t ∧ intervalMinimum h s t = h s := by
  change SeparationQuotient.mk (timeMap hh s) = SeparationQuotient.mk (timeMap hh t) ↔ _
  rw [SeparationQuotient.mk_eq_mk, Metric.inseparable_iff]
  exact heightDist_zero_iff hh s.property t.property

instance heightQuotient_compactSpace {h : ℝ → ℝ} {a b : ℝ} {hh : ContinuousOn h (Icc a b)} :
    CompactSpace (HeightQuotient h a b hh) := by
  apply isCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr (quotientTime_surjective hh)]
  exact isCompact_range (quotientTime_continuous hh)

instance heightQuotient_preconnectedSpace {h : ℝ → ℝ} {a b : ℝ} {hh : ContinuousOn h (Icc a b)} :
    PreconnectedSpace (HeightQuotient h a b hh) := by
  let : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  constructor
  rw [← Set.range_eq_univ.mpr (quotientTime_surjective hh)]
  exact isPreconnected_range (quotientTime_continuous hh)

theorem heightQuotient_pathConnectedSpace {h : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hh : ContinuousOn h (Icc a b)) :
    PathConnectedSpace (HeightQuotient h a b hh) := by
  let : PathConnectedSpace (Icc a b) := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc a b).isPathConnected (nonempty_Icc.mpr hab))
  exact (quotientTime_surjective hh).pathConnectedSpace (quotientTime_continuous hh)

theorem curve_dist_le_heightDist {E : Type*} [PseudoMetricSpace E]
    {γ : ℝ → E} {h : ℝ → ℝ} {a b s t : ℝ} (hh : HasTreeHeight γ a b h)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : dist (γ s) (γ t) ≤ heightDist h s t := by
  have aux {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      dist (γ s) (γ t) ≤ heightDist h s t := by
    obtain ⟨r, hr, hb⟩ := hh.2.2.2.2 s hs t ⟨hst, ht.2⟩
    have hr' : r ∈ uIcc s t := by rw [uIcc_of_le hst]; exact hr
    have hm := intervalMinimum_le hh.1 hs ht hr'
    unfold heightDist
    linarith
  rcases le_total s t with hst | hts
  · exact aux hs ht hst
  · rw [dist_comm, heightDist_symm]
    exact aux ht hs hts

theorem curve_eq_of_heightDist_zero {E : Type*} [MetricSpace E]
    {γ : ℝ → E} {h : ℝ → ℝ} {a b s t : ℝ} (hh : HasTreeHeight γ a b h)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : heightDist h s t = 0) : γ s = γ t := by
  apply dist_eq_zero.mp
  exact le_antisymm (hst ▸ curve_dist_le_heightDist hh hs ht) dist_nonneg

/-- The actual curve descends to the separated metric quotient. -/
def factorCurve {E : Type*} [MetricSpace E] {γ : ℝ → E} {h : ℝ → ℝ} {a b : ℝ}
    (hh : HasTreeHeight γ a b h) : HeightQuotient h a b hh.1 → E :=
  SeparationQuotient.lift (fun t : HeightTime h a b hh.1 => γ t.val)
    (fun s t hst => curve_eq_of_heightDist_zero hh s.mem_interval t.mem_interval
      (Inseparable.dist_eq_zero hst))

theorem factorCurve_time {E : Type*} [MetricSpace E] {γ : ℝ → E} {h : ℝ → ℝ} {a b : ℝ}
    (hh : HasTreeHeight γ a b h) (t : Icc a b) :
    factorCurve hh (quotientTime hh.1 t) = γ t := rfl

theorem factorCurve_lipschitz {E : Type*} [MetricSpace E] {γ : ℝ → E} {h : ℝ → ℝ} {a b : ℝ}
    (hh : HasTreeHeight γ a b h) : LipschitzWith 1 (factorCurve hh) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  obtain ⟨s, rfl⟩ := SeparationQuotient.surjective_mk s
  obtain ⟨t, rfl⟩ := SeparationQuotient.surjective_mk t
  change dist (γ s.val) (γ t.val) ≤ (1 : ℝ≥0) * heightDist h s.val t.val
  simpa using curve_dist_le_heightDist hh s.mem_interval t.mem_interval

theorem height_implies_curve_continuous {E : Type*} [MetricSpace E]
    {γ : ℝ → E} {h : ℝ → ℝ} {a b : ℝ} (hh : HasTreeHeight γ a b h) :
    ContinuousOn γ (Icc a b) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact (factorCurve_lipschitz hh).continuous.comp (quotientTime_continuous hh.1)

theorem quotientTime_endpoints {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hh : ContinuousOn h (Icc a b)) (ha : h a = 0) (hb : h b = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ h t) :
    quotientTime hh ⟨a, ⟨le_rfl, hab⟩⟩ = quotientTime hh ⟨b, ⟨hab, le_rfl⟩⟩ := by
  apply SeparationQuotient.mk_eq_mk.mpr
  apply Metric.inseparable_iff.mpr
  change heightDist h a b = 0
  obtain ⟨r, hr, he, hmin⟩ := intervalMinimum_attained hh ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  have hr' : r ∈ Icc a b := by rwa [uIcc_of_le hab] at hr
  have hge := hnonneg r hr'
  have hle := hmin a left_mem_uIcc
  rw [ha] at hle
  have hz : intervalMinimum h a b = 0 := by rw [he]; linarith
  simp [heightDist, ha, hb, hz]

/-- A height witness yields a concrete compact separated four-point metric
space, a continuous surjective loop into it, and a 1-Lipschitz factor map. -/
theorem height_metric_factorization {E : Type*} [MetricSpace E]
    {γ : ℝ → E} {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hh : HasTreeHeight γ a b h) :
    @FourPoint (HeightQuotient h a b hh.1) _ ∧
      Continuous (quotientTime hh.1) ∧ Function.Surjective (quotientTime hh.1) ∧
      quotientTime hh.1 ⟨a, ⟨le_rfl, hab⟩⟩ = quotientTime hh.1 ⟨b, ⟨hab, le_rfl⟩⟩ ∧
      LipschitzWith 1 (factorCurve hh) ∧
      ∀ t : Icc a b, factorCurve hh (quotientTime hh.1 t) = γ t :=
  ⟨heightQuotient_fourPoint hh.1, quotientTime_continuous hh.1, quotientTime_surjective hh.1,
    quotientTime_endpoints hab hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1,
    factorCurve_lipschitz hh, factorCurve_time hh⟩

end LinearInputCurveWordHeightMetric
