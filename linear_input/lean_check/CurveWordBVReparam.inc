/-!
Monotone time changes of Stieltjes measures and signatures. Flat time fibers
are allowed: a right-end inverse is obtained from a supremum, not assumed.
-/

noncomputable section

namespace LinearInputCurveWordBVReparam

open Real Set MeasureTheory Filter
open scoped Topology
open LinearInputCurveWordStieltjes LinearInputCurveWordBVSignature

def rightEndInverse (φ : ℝ → ℝ) (y : ℝ) : ℝ := sSup (φ ⁻¹' Iic y)

theorem sublevel_nonempty {φ : ℝ → ℝ} (hs : Function.Surjective φ) (y : ℝ) :
    (φ ⁻¹' Iic y).Nonempty := by
  obtain ⟨x, hx⟩ := hs y
  exact ⟨x, by simpa only [Set.mem_preimage, Set.mem_Iic, hx] using (le_refl y)⟩

theorem sublevel_bddAbove {φ : ℝ → ℝ} (hm : Monotone φ)
    (hs : Function.Surjective φ) (y : ℝ) : BddAbove (φ ⁻¹' Iic y) := by
  obtain ⟨x, hx⟩ := hs (y + 1)
  refine ⟨x, ?_⟩
  intro t ht
  by_contra hn
  have hφ := hm (le_of_not_ge hn)
  change φ t ≤ y at ht
  linarith

theorem rightEndInverse_spec {φ : ℝ → ℝ} (hm : Monotone φ) (hc : Continuous φ)
    (hs : Function.Surjective φ) (y : ℝ) : φ (rightEndInverse φ y) = y := by
  have hb := sublevel_bddAbove hm hs y
  have hne := sublevel_nonempty hs y
  have hclosed : IsClosed (φ ⁻¹' Iic y) := isClosed_Iic.preimage hc
  have hle : φ (rightEndInverse φ y) ≤ y := hclosed.csSup_mem hne hb
  obtain ⟨x, hx⟩ := hs y
  have hxs : x ∈ φ ⁻¹' Iic y := by simp only [Set.mem_preimage, Set.mem_Iic, hx, le_refl]
  have hge := hm (le_csSup hb hxs)
  rw [hx] at hge
  exact le_antisymm hle hge

theorem preimage_Iic {φ : ℝ → ℝ} (hm : Monotone φ) (hc : Continuous φ)
    (hs : Function.Surjective φ) (y : ℝ) :
    φ ⁻¹' Iic y = Iic (rightEndInverse φ y) := by
  ext t
  constructor
  · intro ht
    exact le_csSup (sublevel_bddAbove hm hs y) ht
  · intro ht
    change φ t ≤ y
    rw [← rightEndInverse_spec hm hc hs y]
    exact hm ht

theorem preimage_Ioc {φ : ℝ → ℝ} (hm : Monotone φ) (hc : Continuous φ)
    (hs : Function.Surjective φ) (a b : ℝ) :
    φ ⁻¹' Ioc a b = Ioc (rightEndInverse φ a) (rightEndInverse φ b) := by
  rw [← Iic_diff_Iic, preimage_diff, preimage_Iic hm hc hs, preimage_Iic hm hc hs,
    Iic_diff_Iic]

def reparam (p : StieltjesFunction ℝ) (hp : Continuous (p : ℝ → ℝ))
    (φ : ℝ → ℝ) (hm : Monotone φ) (hc : Continuous φ) : StieltjesFunction ℝ :=
  ofContinuousMonotone (p ∘ φ) (p.mono.comp hm) (hp.comp hc)

theorem reparam_map_measure (p : StieltjesFunction ℝ) (hp : Continuous (p : ℝ → ℝ))
    {φ : ℝ → ℝ} (hm : Monotone φ) (hc : Continuous φ) (hs : Function.Surjective φ) :
    Measure.map φ (reparam p hp φ hm hc).measure = p.measure := by
  have hi (a b : ℝ) :
      (Measure.map φ (reparam p hp φ hm hc).measure) (Ioc a b) = p.measure (Ioc a b) := by
    rw [Measure.map_apply hc.measurable measurableSet_Ioc, preimage_Ioc hm hc hs,
      StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc]
    change ENNReal.ofReal (p (φ (rightEndInverse φ b)) - p (φ (rightEndInverse φ a))) = _
    rw [rightEndInverse_spec hm hc hs, rightEndInverse_spec hm hc hs]
  apply Measure.ext_of_Ioc'
  · intro a b _
    rw [hi, StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_ne_top
  · intro a b _
    exact hi a b

theorem reparam_map_restrict (p : StieltjesFunction ℝ) (hp : Continuous (p : ℝ → ℝ))
    {φ : ℝ → ℝ} (hm : Monotone φ) (hc : Continuous φ) (hs : Function.Surjective φ)
    (a b : ℝ) :
    Measure.map φ ((reparam p hp φ hm hc).measure.restrict (Ioc a b)) =
      p.measure.restrict (Ioc (φ a) (φ b)) := by
  have hi (c d : ℝ) :
      (Measure.map φ ((reparam p hp φ hm hc).measure.restrict (Ioc a b))) (Ioc c d) =
        (p.measure.restrict (Ioc (φ a) (φ b))) (Ioc c d) := by
    rw [Measure.map_apply hc.measurable measurableSet_Ioc,
      Measure.restrict_apply (measurableSet_Ioc.preimage hc.measurable),
      Measure.restrict_apply measurableSet_Ioc, preimage_Ioc hm hc hs,
      Set.Ioc_inter_Ioc, Set.Ioc_inter_Ioc, StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc]
    change ENNReal.ofReal (p (φ (min (rightEndInverse φ d) b)) -
      p (φ (max (rightEndInverse φ c) a))) = _
    rw [hm.map_min, hm.map_max, rightEndInverse_spec hm hc hs, rightEndInverse_spec hm hc hs]
  apply Measure.ext_of_Ioc'
  · intro c d _
    rw [hi, Measure.restrict_apply measurableSet_Ioc]
    have hn : p.measure (Ioc c d) ≠ ⊤ := by
      rw [StieltjesFunction.measure_Ioc]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hn (measure_mono inter_subset_left)
  · intro c d _
    exact hi c d

theorem reparam_setIntegral (p : StieltjesFunction ℝ) (hp : Continuous (p : ℝ → ℝ))
    {φ : ℝ → ℝ} (hm : Monotone φ) (hc : Continuous φ) (hs : Function.Surjective φ)
    {F : ℝ → ℝ} (hF : Continuous F) (a b : ℝ) :
    (∫ t in Ioc a b, F (φ t) ∂(reparam p hp φ hm hc).measure) =
      ∫ t in Ioc (φ a) (φ b), F t ∂p.measure := by
  rw [← reparam_map_restrict p hp hm hc hs a b]
  exact (integral_map_of_stronglyMeasurable hc.measurable hF.stronglyMeasurable).symm

theorem reparam_intervalIntegral (p : StieltjesFunction ℝ) (hp : Continuous (p : ℝ → ℝ))
    {φ : ℝ → ℝ} (hm : Monotone φ) (hc : Continuous φ) (hs : Function.Surjective φ)
    {F : ℝ → ℝ} (hF : Continuous F) (a b : ℝ) :
    (∫ t in a..b, F (φ t) ∂(reparam p hp φ hm hc).measure) =
      ∫ t in (φ a)..(φ b), F t ∂p.measure := by
  simp only [intervalIntegral]
  rw [reparam_setIntegral p hp hm hc hs hF a b, reparam_setIntegral p hp hm hc hs hF b a]

theorem reparam_stieltjesIntegral (p m : StieltjesFunction ℝ)
    (hp : Continuous (p : ℝ → ℝ)) (hmp : Continuous (m : ℝ → ℝ))
    {φ : ℝ → ℝ} (hm : Monotone φ) (hc : Continuous φ) (hs : Function.Surjective φ)
    {F : ℝ → ℝ} (hF : Continuous F) (a b : ℝ) :
    stieltjesIntegral (reparam p hp φ hm hc) (reparam m hmp φ hm hc) a b (F ∘ φ) =
      stieltjesIntegral p m (φ a) (φ b) F := by
  unfold stieltjesIntegral
  simp only [Function.comp_apply]
  rw [reparam_intervalIntegral p hp hm hc hs hF a b,
    reparam_intervalIntegral m hmp hm hc hs hF a b]

theorem reverseStieltjes_reparam {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hmp : ∀ i, Continuous (m i : ℝ → ℝ))
    {φ : ℝ → ℝ} (hm : Monotone φ) (hc : Continuous φ) (hs : Function.Surjective φ)
    (a : ℝ) (w : List ι) (b : ℝ) :
    reverseStieltjes (fun i => reparam (p i) (hp i) φ hm hc)
        (fun i => reparam (m i) (hmp i) φ hm hc) a w b =
      reverseStieltjes p m (φ a) w (φ b) := by
  induction w generalizing b with
  | nil => rfl
  | cons i w ih =>
    change stieltjesIntegral _ _ a b _ = stieltjesIntegral _ _ (φ a) (φ b) _
    rw [show reverseStieltjes (fun i => reparam (p i) (hp i) φ hm hc)
        (fun i => reparam (m i) (hmp i) φ hm hc) a w =
        reverseStieltjes p m (φ a) w ∘ φ from funext ih]
    exact reparam_stieltjesIntegral (p i) (m i) (hp i) (hmp i) hm hc hs
      (reverseStieltjes_continuous p m hp hmp (φ a) w) a b

/-- A continuous monotone surjective change of real time preserves every
coefficient. Its flat fibers are handled by the measure pushforward proof. -/
theorem stieltjesSignature_reparam {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hmp : ∀ i, Continuous (m i : ℝ → ℝ))
    {φ : ℝ → ℝ} (hm : Monotone φ) (hc : Continuous φ) (hs : Function.Surjective φ)
    (a b : ℝ) (w : List ι) :
    stieltjesSignature (fun i => reparam (p i) (hp i) φ hm hc)
        (fun i => reparam (m i) (hmp i) φ hm hc) a b w =
      stieltjesSignature p m (φ a) (φ b) w :=
  reverseStieltjes_reparam p m hp hmp hm hc hs a w.reverse b

open LinearInputCurveWordBoundedVariation

/-- Extend a compact-interval clock with affine tails. Within the interval its
values, including all flat fibers, are unchanged. -/
def ontoExtension (φ : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  φ (clamp a b t) + min (t - a) 0 + max (t - b) 0

theorem ontoExtension_eq {φ : ℝ → ℝ} {a b t : ℝ} (ht : t ∈ Icc a b) :
    ontoExtension φ a b t = φ t := by
  simp only [ontoExtension, clamp_eq ht, min_eq_right (sub_nonneg.mpr ht.1),
    max_eq_right (sub_nonpos.mpr ht.2), add_zero]

theorem ontoExtension_continuous {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn φ (Icc a b)) : Continuous (ontoExtension φ a b) := by
  have he := constantExtension_continuous hab hc
  exact (he.add ((continuous_id.sub continuous_const).min continuous_const)).add
    ((continuous_id.sub continuous_const).max continuous_const)

theorem ontoExtension_monotone {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hm : MonotoneOn φ (Icc a b)) : Monotone (ontoExtension φ a b) := by
  intro s t hst
  have h1 := hm (clamp_mem hab s) (clamp_mem hab t) (clamp_monotone a b hst)
  have h2 := min_le_min_right (0 : ℝ) (sub_le_sub_right hst a)
  have h3 := max_le_max_right (0 : ℝ) (sub_le_sub_right hst b)
  exact add_le_add (add_le_add h1 h2) h3

theorem ontoExtension_surjective {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn φ (Icc a b)) :
    Function.Surjective (ontoExtension φ a b) := by
  intro y
  by_cases hya : y ≤ φ a
  · refine ⟨a + y - φ a, ?_⟩
    have hta : a + y - φ a ≤ a := by linarith
    have htb : a + y - φ a ≤ b := hta.trans hab
    have hcl : clamp a b (a + y - φ a) = a := by
      simp only [clamp, min_eq_right htb, max_eq_left hta]
    rw [ontoExtension, hcl, min_eq_left (by linarith : a + y - φ a - a ≤ 0),
      max_eq_right (by linarith : a + y - φ a - b ≤ 0)]
    ring
  · by_cases hyb : φ b ≤ y
    · refine ⟨b + y - φ b, ?_⟩
      have htb : b ≤ b + y - φ b := by linarith
      have hta : a ≤ b + y - φ b := hab.trans htb
      have hcl : clamp a b (b + y - φ b) = b := by
        simp only [clamp, min_eq_left htb, max_eq_right hab]
      rw [ontoExtension, hcl, min_eq_right (by linarith : 0 ≤ b + y - φ b - a),
        max_eq_left (by linarith : 0 ≤ b + y - φ b - b)]
      ring
    · have hmem : y ∈ Icc (φ a) (φ b) := ⟨(not_le.mp hya).le, (not_le.mp hyb).le⟩
      obtain ⟨t, ht, he⟩ := intermediate_value_Icc hab hc hmem
      exact ⟨t, (ontoExtension_eq ht).trans he⟩

/-- Compact-interval time changes require only continuity and monotonicity
on that interval. The explicit affine-tail extension makes the global measure
construction applicable and agrees with the requested clock everywhere inside. -/
theorem stieltjesSignature_interval_reparam {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hmp : ∀ i, Continuous (m i : ℝ → ℝ))
    {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hm : MonotoneOn φ (Icc a b)) (hc : ContinuousOn φ (Icc a b)) (w : List ι) :
    stieltjesSignature
        (fun i => reparam (p i) (hp i) (ontoExtension φ a b)
          (ontoExtension_monotone hab hm) (ontoExtension_continuous hab hc))
        (fun i => reparam (m i) (hmp i) (ontoExtension φ a b)
          (ontoExtension_monotone hab hm) (ontoExtension_continuous hab hc)) a b w =
      stieltjesSignature p m (φ a) (φ b) w := by
  rw [stieltjesSignature_reparam p m hp hmp (ontoExtension_monotone hab hm)
    (ontoExtension_continuous hab hc) (ontoExtension_surjective hab hc),
    ontoExtension_eq (show a ∈ Icc a b from ⟨le_rfl, hab⟩),
    ontoExtension_eq (show b ∈ Icc a b from ⟨hab, le_rfl⟩)]

end LinearInputCurveWordBVReparam
