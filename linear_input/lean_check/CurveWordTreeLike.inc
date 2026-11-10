/-!
Geometric height functions for tree-like paths. The predicate is independent
of all signature coefficients. We first establish its elementary geometry and
the complete scalar case; the general bounded-variation uniqueness theorem
requires further arguments and is not postulated here.
-/

noncomputable section

namespace LinearInputCurveWordTreeLike
open Set Real MeasureTheory

open scoped NNReal

/-- A witness form of the usual height-function condition. On each compact
subinterval a continuous height attains its minimum, so choosing the witnessing
point is equivalent to using that minimum in the height pseudometric. -/
def HasTreeHeight {E : Type*} [PseudoMetricSpace E] (γ : ℝ → E) (a b : ℝ)
    (h : ℝ → ℝ) : Prop :=
  ContinuousOn h (Icc a b) ∧ h a = 0 ∧ h b = 0 ∧
    (∀ t ∈ Icc a b, 0 ≤ h t) ∧
    ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
      ∃ r ∈ Icc s t, dist (γ s) (γ t) ≤ h s + h t - 2 * h r

def TreeLike {E : Type*} [PseudoMetricSpace E] (γ : ℝ → E) (a b : ℝ) : Prop :=
  ContinuousOn γ (Icc a b) ∧ ∃ h, HasTreeHeight γ a b h

theorem treeLike_closed {E : Type*} [MetricSpace E] {γ : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hγ : TreeLike γ a b) : γ a = γ b := by
  obtain ⟨_, h, _, ha, hb, hnonneg, hdist⟩ := hγ
  obtain ⟨r, hr, hbound⟩ := hdist a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩
  rw [ha, hb] at hbound
  have hn := hnonneg r hr
  exact dist_eq_zero.mp (le_antisymm (by linarith) dist_nonneg)

theorem treeLike_constant {E : Type*} [PseudoMetricSpace E] (x : E) (a b : ℝ) :
    TreeLike (fun _ => x) a b := by
  refine ⟨continuousOn_const, (fun _ => 0), continuousOn_const, rfl, rfl,
    (fun _ _ => le_rfl), ?_⟩
  intro s _ t ht
  exact ⟨s, ⟨le_rfl, ht.1⟩, by simp⟩

theorem HasTreeHeight.lipschitz_map {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {γ : ℝ → E} {a b : ℝ} {h : ℝ → ℝ} (hh : HasTreeHeight γ a b h)
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    HasTreeHeight (f ∘ γ) a b (fun t => (K : ℝ) * h t) := by
  refine ⟨continuousOn_const.mul hh.1, by simp only [hh.2.1, mul_zero],
    by simp only [hh.2.2.1, mul_zero], (fun t ht => mul_nonneg K.coe_nonneg (hh.2.2.2.1 t ht)), ?_⟩
  intro s hs t ht
  obtain ⟨r, hr, hb⟩ := hh.2.2.2.2 s hs t ht
  refine ⟨r, hr, ?_⟩
  calc
    dist (f (γ s)) (f (γ t)) ≤ (K : ℝ) * dist (γ s) (γ t) := hf.dist_le_mul _ _
    _ ≤ (K : ℝ) * (h s + h t - 2 * h r) := mul_le_mul_of_nonneg_left hb K.coe_nonneg
    _ = _ := by ring

theorem TreeLike.lipschitz_map {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {γ : ℝ → E} {a b : ℝ} (hγ : TreeLike γ a b)
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f) : TreeLike (f ∘ γ) a b := by
  obtain ⟨hc, h, hh⟩ := hγ
  exact ⟨hf.continuous.comp_continuousOn hc, _, hh.lipschitz_map hf⟩

/-- The witness condition gives the usual height bound at every point where
the height takes its minimum on the intervening interval. -/
theorem HasTreeHeight.minimum_bound {E : Type*} [PseudoMetricSpace E]
    {γ : ℝ → E} {a b : ℝ} {h : ℝ → ℝ} (hh : HasTreeHeight γ a b h)
    {s t r : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc s b)
    (hmin : IsMinOn h (Icc s t) r) :
    dist (γ s) (γ t) ≤ h s + h t - 2 * h r := by
  obtain ⟨u, hu, hb⟩ := hh.2.2.2.2 s hs t ht
  have hm : h r ≤ h u := hmin hu
  linarith

/-- Geometric height witnesses pass to a uniform limit of both paths and
heights. No signature assumption occurs in this closure theorem. -/
theorem HasTreeHeight.uniform_limit {E : Type*} [PseudoMetricSpace E]
    {Γ : ℕ → ℝ → E} {H : ℕ → ℝ → ℝ} {γ : ℝ → E} {h : ℝ → ℝ}
    {a b : ℝ} (hab : a ≤ b) (hw : ∀ n, HasTreeHeight (Γ n) a b (H n))
    (hΓ : TendstoUniformlyOn Γ γ Filter.atTop (Icc a b))
    (hH : TendstoUniformlyOn H h Filter.atTop (Icc a b)) :
    HasTreeHeight γ a b h := by
  have hc : ContinuousOn h (Icc a b) :=
    hH.continuousOn (Filter.Eventually.of_forall (fun n => (hw n).1)).frequently
  have ha : h a = 0 := tendsto_nhds_unique (hH.tendsto_at ⟨le_rfl, hab⟩)
    (by simpa only [funext (fun n => (hw n).2.1)] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0)))
  have hb : h b = 0 := tendsto_nhds_unique (hH.tendsto_at ⟨hab, le_rfl⟩)
    (by simpa only [funext (fun n => (hw n).2.2.1)] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0)))
  refine ⟨hc, ha, hb, ?_, ?_⟩
  · intro t ht
    exact ge_of_tendsto (hH.tendsto_at ht)
      (Filter.Eventually.of_forall (fun n => (hw n).2.2.2.1 t ht))
  · intro s hs t ht
    have ht' : t ∈ Icc a b := ⟨hs.1.trans ht.1, ht.2⟩
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    obtain ⟨r, hr, hm⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr ht.1) (hc.mono hsub)
    refine ⟨r, hr, ?_⟩
    by_contra hn
    have hgap : 0 < dist (γ s) (γ t) - (h s + h t - 2 * h r) := by
      linarith [not_le.mp hn]
    let ε := (dist (γ s) (γ t) - (h s + h t - 2 * h r)) / 7
    have hε : 0 < ε := div_pos hgap (by norm_num)
    obtain ⟨n, hnΓ, hnH⟩ := ((Metric.tendstoUniformlyOn_iff.mp hΓ ε hε).and
      (Metric.tendstoUniformlyOn_iff.mp hH ε hε)).exists
    obtain ⟨u, hu, hbound⟩ := (hw n).2.2.2.2 s hs t ht
    have hmin : h r ≤ h u := hm hu
    have hsε := hnH s hs
    have htε := hnH t ht'
    have huε := hnH u (hsub hu)
    rw [Real.dist_eq] at hsε htε huε
    have hpath : dist (γ s) (γ t) ≤
        dist (γ s) (Γ n s) + dist (Γ n s) (Γ n t) + dist (γ t) (Γ n t) := by
      calc
        _ ≤ dist (γ s) (Γ n s) + dist (Γ n s) (γ t) := dist_triangle _ _ _
        _ ≤ dist (γ s) (Γ n s) + (dist (Γ n s) (Γ n t) + dist (Γ n t) (γ t)) :=
          add_le_add_right (dist_triangle _ _ _) _
        _ = _ := by rw [dist_comm (Γ n t) (γ t)]; ring
    have hsΓ := hnΓ s hs
    have htΓ := hnΓ t ht'
    rcases abs_lt.mp hsε with ⟨hslo, hshi⟩
    rcases abs_lt.mp htε with ⟨htlo, hthi⟩
    rcases abs_lt.mp huε with ⟨hulo, huhi⟩
    dsimp [ε] at *
    linarith

theorem treeLike_uniform_limit {E : Type*} [PseudoMetricSpace E]
    {Γ : ℕ → ℝ → E} {H : ℕ → ℝ → ℝ} {γ : ℝ → E} {h : ℝ → ℝ}
    {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ n, ContinuousOn (Γ n) (Icc a b))
    (hw : ∀ n, HasTreeHeight (Γ n) a b (H n))
    (hΓ : TendstoUniformlyOn Γ γ Filter.atTop (Icc a b))
    (hH : TendstoUniformlyOn H h Filter.atTop (Icc a b)) : TreeLike γ a b := by
  exact ⟨hΓ.continuousOn (Filter.Eventually.of_forall hc).frequently,
    h, HasTreeHeight.uniform_limit hab hw hΓ hH⟩

theorem real_height_witness {γ : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hγ : ContinuousOn γ (Icc s t)) (c : ℝ) :
    ∃ r ∈ Icc s t,
      |γ s - γ t| ≤ |γ s - c| + |γ t - c| - 2 * |γ r - c| := by
  rcases le_total (γ s) (γ t) with hst' | hts'
  · by_cases hc : c ≤ γ s
    · refine ⟨s, ⟨le_rfl, hst⟩, ?_⟩
      rw [abs_of_nonpos (sub_nonpos.mpr hst'), abs_of_nonneg (sub_nonneg.mpr hc),
        abs_of_nonneg (sub_nonneg.mpr (hc.trans hst'))]
      linarith
    · by_cases ht : γ t ≤ c
      · refine ⟨t, ⟨hst, le_rfl⟩, ?_⟩
        rw [abs_of_nonpos (sub_nonpos.mpr hst'),
          abs_of_nonpos (sub_nonpos.mpr (hst'.trans ht)), abs_of_nonpos (sub_nonpos.mpr ht)]
        linarith
      · obtain ⟨r, hr, he⟩ := intermediate_value_Icc hst hγ
          (show c ∈ Icc (γ s) (γ t) from ⟨(not_le.mp hc).le, (not_le.mp ht).le⟩)
        refine ⟨r, hr, ?_⟩
        rw [he, sub_self, abs_zero, mul_zero, sub_zero]
        simpa only [Real.dist_eq, abs_sub_comm c (γ t)] using dist_triangle (γ s) c (γ t)
  · by_cases hc : c ≤ γ t
    · refine ⟨t, ⟨hst, le_rfl⟩, ?_⟩
      rw [abs_of_nonneg (sub_nonneg.mpr hts'),
        abs_of_nonneg (sub_nonneg.mpr (hc.trans hts')), abs_of_nonneg (sub_nonneg.mpr hc)]
      linarith
    · by_cases hs : γ s ≤ c
      · refine ⟨s, ⟨le_rfl, hst⟩, ?_⟩
        rw [abs_of_nonneg (sub_nonneg.mpr hts'), abs_of_nonpos (sub_nonpos.mpr hs),
          abs_of_nonpos (sub_nonpos.mpr (hts'.trans hs))]
        linarith
      · obtain ⟨r, hr, he⟩ := intermediate_value_Icc' hst hγ
          (show c ∈ Icc (γ t) (γ s) from ⟨(not_le.mp hc).le, (not_le.mp hs).le⟩)
        refine ⟨r, hr, ?_⟩
        rw [he, sub_self, abs_zero, mul_zero, sub_zero]
        simpa only [Real.dist_eq, abs_sub_comm c (γ t)] using dist_triangle (γ s) c (γ t)

/-- Every continuous real-valued closed path has an actual geometric height
function, regardless of its amount of backtracking. -/
theorem real_closed_treeLike {γ : ℝ → ℝ} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) : TreeLike γ a b := by
  refine ⟨hγ, (fun t => |γ t - γ a|), (hγ.sub continuousOn_const).abs,
    by simp, by simp [hclosed], (fun _ _ => abs_nonneg _), ?_⟩
  intro s hs t ht
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  simpa only [Real.dist_eq] using real_height_witness ht.1 (hγ.mono hsub) (γ a)

theorem real_treeLike_iff_closed {γ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) : TreeLike γ a b ↔ γ a = γ b :=
  ⟨treeLike_closed hab, real_closed_treeLike hγ⟩

open LinearInputCurveWordSignature

/-- For one scalar coordinate the actual iterated integrals are divided powers
of the displacement; no uniqueness theorem is used in this calculation. -/
theorem reverseIntegral_scalar {ι : Type*} {v : ℝ → ℝ} (hv : Continuous v)
    (a b : ℝ) (w : List ι) :
    reverseIntegral (fun _ : ι => v) a w b =
      (∫ t in a..b, v t) ^ w.length / (w.length.factorial : ℝ) := by
  induction w generalizing b with
  | nil => simp [reverseIntegral]
  | cons i w ih =>
    simp only [reverseIntegral, ih, List.length_cons]
    let x : ℝ → ℝ := fun t => ∫ s in a..t, v s
    have hx : Continuous x := (intervalIntegral.differentiable_integral_of_continuous hv).continuous
    have hd (t : ℝ) : HasDerivAt
        (fun t => x t ^ (w.length + 1) / ((w.length + 1).factorial : ℝ))
        (x t ^ w.length / (w.length.factorial : ℝ) * v t) t := by
      have hbase := ((hv.integral_hasStrictDerivAt a t).hasDerivAt.pow (w.length + 1)).div_const
        ((w.length + 1).factorial : ℝ)
      convert hbase using 1
      simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hn : (w.length.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero w.length
      have hn1 : (w.length : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      dsimp [x]
      ring
    have hi : IntervalIntegrable (fun t => x t ^ w.length / (w.length.factorial : ℝ) * v t)
        volume a b := ((hx.pow _).div_const _ |>.mul hv).intervalIntegrable a b
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
    simpa [x] using hf

theorem signature_scalar {ι : Type*} {v : ℝ → ℝ} (hv : Continuous v)
    (a b : ℝ) (w : List ι) :
    signature (fun _ : ι => v) a b w =
      (∫ t in a..b, v t) ^ w.length / (w.length.factorial : ℝ) := by
  simpa only [signature, List.length_reverse] using reverseIntegral_scalar hv a b w.reverse

def scalarCurve (v : ℝ → ℝ) (a t : ℝ) : ℝ := ∫ s in a..t, v s

/-- A complete geometric/signature equivalence for the scalar continuously
differentiable reconstruction. It is a preliminary case, not the general
bounded-variation Hambly--Lyons theorem. -/
theorem scalar_treeLike_iff_signature_trivial {v : ℝ → ℝ} (hv : Continuous v)
    (a b : ℝ) (hab : a ≤ b) :
    TreeLike (scalarCurve v a) a b ↔
      ∀ w : List Unit, signature (fun _ : Unit => v) a b w = if w = [] then 1 else 0 := by
  have hc : Continuous (scalarCurve v a) :=
    (intervalIntegral.differentiable_integral_of_continuous hv).continuous
  rw [real_treeLike_iff_closed hab hc.continuousOn]
  constructor
  · intro he w
    have hz : (∫ t in a..b, v t) = 0 := by simpa [scalarCurve] using he.symm
    rw [signature_scalar hv, hz]
    cases w with
    | nil => simp
    | cons i w => simp
  · intro he
    have hz := he [()]
    simpa [signature_singleton, scalarCurve] using hz.symm

end LinearInputCurveWordTreeLike
