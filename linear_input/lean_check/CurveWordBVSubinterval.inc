/-!
Local consequences of trivial signatures for actual continuous BV lifts.
All maps below come from the original time interval. No arbitrary arc in the
signature image is identified with a time subinterval.
-/

noncomputable section
namespace LinearInputCurveWordBVSubinterval
open Set MeasureTheory
open LinearInputCurveWordStieltjes LinearInputCurveWordBVSignature
open LinearInputCurveWordBVCanonical LinearInputCurveWordBVChen
open LinearInputCurveWordBVShuffle LinearInputCurveWordBVTopology

def signatureTimeMap {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b : ℝ) : C(Icc a b, signatureRange p m a b) :=
  ⟨fun t => ⟨stieltjesSignature p m a t.val, ⟨t, rfl⟩⟩,
    ((signature_lift_continuous hp hm a).comp continuous_subtype_val).subtype_mk _⟩

theorem time_coefficient_descends {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    {a b : ℝ} (hab : a ≤ b) {F : ℝ → ℝ} (hF : ContinuousOn F (Icc a b))
    (hcompat : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      stieltjesSignature p m a s = stieltjesSignature p m a t → F s = F t) :
    ∃ f : C(signatureRange p m a b, ℝ),
      ∀ t ∈ Icc a b, f (signaturePoint p m a b hab t) = F t := by
  let T := signatureTimeMap p m hp hm a b
  have hs : Function.Surjective T := by
    intro x
    obtain ⟨t, ht⟩ := x.property
    exact ⟨t, Subtype.ext ht⟩
  have hq := IsQuotientMap.of_surjective_continuous hs T.continuous
  let G : C(Icc a b, ℝ) := ⟨fun t => F t.val, hF.restrict⟩
  have hf : Function.FactorsThrough G T := by
    intro s t hst
    exact hcompat s.val s.property t.val t.property (congrArg Subtype.val hst)
  refine ⟨hq.lift G hf, ?_⟩
  intro t ht
  have he := congrArg (fun g : C(Icc a b, ℝ) => g ⟨t, ht⟩) (hq.lift_comp G hf)
  simpa only [ContinuousMap.comp_apply, G, ContinuousMap.coe_mk, T, signatureTimeMap,
    signaturePoint, projIcc_of_mem hab ht] using he

theorem periodic_time_integral_zero {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    {a b : ℝ} (hab : a ≤ b)
    (hzero : ∀ w : List ι, w ≠ [] → stieltjesSignature p m a b w = 0)
    (hsimple : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      stieltjesSignature p m a s = stieltjesSignature p m a t →
      s = t ∨ (s = a ∧ t = b) ∨ (s = b ∧ t = a))
    {F : ℝ → ℝ} (hF : ContinuousOn F (Icc a b)) (hend : F a = F b) (i : ι) :
    stieltjesIntegral (p i) (m i) a b F = 0 := by
  obtain ⟨f, hf⟩ := time_coefficient_descends p m hp hm hab hF (by
    intro s hs t ht hst
    rcases hsimple s hs t ht hst with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hend
    · exact hend.symm)
  have he := continuous_one_form_zero_of_trivial_signature p m hp hm a b hab hzero f [] i
  simp only [reverseStieltjes, mul_one] at he
  rw [← he]
  exact stieltjesIntegral_congr_on (p i) (m i) hab (fun t ht => (hf t ht).symm)

theorem stieltjesIntegral_one (p m : StieltjesFunction ℝ) {a b : ℝ} (hab : a ≤ b) :
    stieltjesIntegral p m a b (fun _ => 1) = (p b - p a) - (m b - m a) := by
  simp only [stieltjesIntegral, intervalIntegral.integral_of_le hab,
    setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
    StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (p.mono hab)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (m.mono hab))]

/-- Vanishing against every continuous periodic time coefficient forces the
underlying signed BV coordinate to be constant. The proof uses its actual
Stieltjes measures and a zero-mean primitive as a test coefficient. -/
theorem constant_of_periodic_integrals_zero (p m : StieltjesFunction ℝ)
    (hp : Continuous (p : ℝ → ℝ)) (hm : Continuous (m : ℝ → ℝ))
    {a b : ℝ} (hab : a < b)
    (hz : ∀ F : ℝ → ℝ, Continuous F → F a = F b → stieltjesIntegral p m a b F = 0) :
    ∀ t ∈ Icc a b, p t - m t = p a - m a := by
  let x : ℝ → ℝ := fun t => p t - m t
  have hx : Continuous x := hp.sub hm
  let c : ℝ := (∫ t in a..b, x t) / (b - a)
  let z : ℝ → ℝ := fun t => x t - c
  have hzc : Continuous z := hx.sub continuous_const
  have hzi : (∫ t in a..b, z t) = 0 := by
    dsimp [z]
    rw [intervalIntegral.integral_sub (hx.intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b), intervalIntegral.integral_const]
    dsimp [c]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  let q := positiveStieltjes z hzc
  let n := negativeStieltjes z hzc
  have hq : Continuous (q : ℝ → ℝ) := primitive_continuous (positiveVelocity_continuous hzc)
  have hn : Continuous (n : ℝ → ℝ) := primitive_continuous (negativeVelocity_continuous hzc)
  have hc1 (t : ℝ) : stieltjesIntegral q n a t (fun _ => 1) = ∫ s in a..t, z s := by
    simpa only [one_mul] using c1_stieltjesIntegral (F := fun _ => 1) hzc continuous_const a t
  let F : ℝ → ℝ := fun t => stieltjesIntegral q n a t (fun _ => 1)
  have hF : Continuous F := stieltjesIntegral_continuous q n hq hn continuous_const a
  have hFa : F a = 0 := by simp only [F, hc1, intervalIntegral.integral_same]
  have hFb : F b = 0 := by simpa only [F, hc1] using hzi
  have hFzero := hz F hF (hFa.trans hFb.symm)
  have hibp := stieltjes_integration_by_parts p m q n hp hm hq hn
    (F := fun _ => 1) (G := fun _ => 1) continuous_const continuous_const hab.le
  simp only [one_mul, mul_one] at hibp
  have hcross : stieltjesIntegral q n a b (fun t => stieltjesIntegral p m a t (fun _ => 1)) = 0 := by
    change stieltjesIntegral p m a b (fun _ => 1) * F b =
      stieltjesIntegral p m a b F + _ at hibp
    rw [hFb, hFzero] at hibp
    linarith
  rw [c1_stieltjesIntegral hzc
    (stieltjesIntegral_continuous p m hp hm continuous_const a)] at hcross
  have hxz : (∫ t in a..b, (x t - x a) * z t) = 0 := by
    rw [← hcross]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le hab.le] at ht
    rw [stieltjesIntegral_one p m ht.1]
    dsimp [x]
    ring
  have hsquare : (∫ t in a..b, z t ^ 2) = 0 := by
    have he : (fun t => (x t - x a) * z t) =
        (fun t => z t ^ 2 + (c - x a) * z t) := by
      funext t
      dsimp [z]
      ring
    have hi : IntervalIntegrable (fun t => (c - x a) * z t) volume a b :=
      (hzc.const_mul (c - x a)).intervalIntegrable a b
    rw [he, intervalIntegral.integral_add ((hzc.pow 2).intervalIntegrable a b) hi,
      intervalIntegral.integral_const_mul, hzi, mul_zero, add_zero] at hxz
    exact hxz
  have hzpoint : ∀ t ∈ Icc a b, z t = 0 := by
    intro t ht
    by_contra hne
    have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hab continuousOn_const (hzc.pow 2).continuousOn
      (fun s _ => sq_nonneg (z s)) ⟨t, ht, sq_pos_of_ne_zero hne⟩
    simp only [intervalIntegral.integral_zero, hsquare, lt_self_iff_false] at hlt
  intro t ht
  have hta := hzpoint a ⟨le_rfl, hab.le⟩
  have htt := hzpoint t ht
  dsimp [z, x] at hta htt
  linarith

theorem reverseStieltjes_diagonal {ι : Type*} (m : ι → StieltjesFunction ℝ)
    (a t : ℝ) (w : List ι) :
    reverseStieltjes m m a w t = if w = [] then 1 else 0 := by
  cases w <;> simp [reverseStieltjes, stieltjesIntegral]

theorem stieltjesSignature_same {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (a : ℝ) (w : List ι) :
    stieltjesSignature p m a a w = if w = [] then 1 else 0 := by
  unfold stieltjesSignature
  cases hw : w.reverse with
  | nil => have : w = [] := List.reverse_eq_nil_iff.mp hw; subst w; rfl
  | cons i l =>
    have hn : w ≠ [] := by intro h; simp only [h, List.reverse_nil] at hw; cases hw
    simp only [reverseStieltjes, stieltjesIntegral, intervalIntegral.integral_same,
      sub_self, if_neg hn]

theorem signature_prefix_constant_of_coordinate_constant {ι : Type*}
    (p m : ι → StieltjesFunction ℝ) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    {a b : ℝ} (hconstant : ∀ i t, t ∈ Icc a b → p i t - m i t = p i a - m i a)
    {t : ℝ} (ht : t ∈ Icc a b) :
    stieltjesSignature p m a t = stieltjesSignature p m a a := by
  funext w
  have he := stieltjesSignature_independent_on (p := p) (m := m) (q := m) (n := m)
    hm hm ht.1 (by
      intro i s hs u hu
      have hs' := hconstant i s ⟨hs.1, hs.2.trans ht.2⟩
      have hu' := hconstant i u ⟨hu.1, hu.2.trans ht.2⟩
      linarith) w
  rw [he, stieltjesSignature, reverseStieltjes_diagonal, stieltjesSignature_same]
  simp only [List.reverse_eq_nil_iff]

/-- An actual signature lift on a nondegenerate interval with trivial total
signature cannot be injective except for its two matching endpoints. -/
theorem signature_lift_not_simple_loop {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    {a b : ℝ} (hab : a < b)
    (hzero : ∀ w : List ι, w ≠ [] → stieltjesSignature p m a b w = 0) :
    ¬ (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      stieltjesSignature p m a s = stieltjesSignature p m a t →
      s = t ∨ (s = a ∧ t = b) ∨ (s = b ∧ t = a)) := by
  intro hsimple
  have hc (i : ι) := constant_of_periodic_integrals_zero (p i) (m i) (hp i) (hm i) hab
    (fun F hF hend => periodic_time_integral_zero p m hp hm hab.le hzero hsimple
      hF.continuousOn hend i)
  have hmid : (a + b) / 2 ∈ Icc a b := by constructor <;> linarith
  have he := signature_prefix_constant_of_coordinate_constant p m hm hc hmid
  rcases hsimple ((a + b) / 2) hmid a ⟨le_rfl, hab.le⟩ he with h | ⟨h, _⟩ | ⟨h, _⟩ <;>
    linarith

/-- Equality of two points of the actual signature lift implies trivial
signature on the intervening oriented interval, by the full Chen identity. -/
theorem subinterval_signature_zero_of_prefix_eq {ι : Type*}
    (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    {a s t : ℝ} (he : stieltjesSignature p m a s = stieltjesSignature p m a t)
    (w : List ι) (hw : w ≠ []) : stieltjesSignature p m s t w = 0 := by
  rw [stieltjesSignature_chen p m hp hm s a t w, ← he,
    ← stieltjesSignature_chen p m hp hm s a s w, stieltjesSignature_same, if_neg hw]

/-- Every nondegenerate actual BV interval with trivial total signature
contains a strictly shorter nondegenerate subinterval with trivial signature.
This is a time-subinterval statement, not an assertion about arbitrary arcs
in the signature range. -/
theorem exists_proper_trivial_subinterval {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    {a b : ℝ} (hab : a < b)
    (hzero : ∀ w : List ι, w ≠ [] → stieltjesSignature p m a b w = 0) :
    ∃ s t : ℝ, a ≤ s ∧ s < t ∧ t ≤ b ∧ t - s < b - a ∧
      ∀ w : List ι, w ≠ [] → stieltjesSignature p m s t w = 0 := by
  by_contra hn
  apply signature_lift_not_simple_loop p m hp hm hab hzero
  intro s hs t ht he
  by_cases hst : s = t
  · exact Or.inl hst
  by_cases hlt : s < t
  · by_cases hbnd : s = a ∧ t = b
    · exact Or.inr (Or.inl hbnd)
    · have hshort : t - s < b - a := by
        by_contra hh
        have heq1 : s = a := by linarith [hs.1, ht.2]
        have heq2 : t = b := by linarith [hs.1, ht.2]
        exact hbnd ⟨heq1, heq2⟩
      exact False.elim (hn ⟨s, t, hs.1, hlt, ht.2, hshort,
        subinterval_signature_zero_of_prefix_eq p m hp hm he⟩)
  · have hts : t < s := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hst)
    by_cases hbnd : s = b ∧ t = a
    · exact Or.inr (Or.inr hbnd)
    · have hshort : s - t < b - a := by
        by_contra hh
        have heq1 : s = b := by linarith [ht.1, hs.2]
        have heq2 : t = a := by linarith [ht.1, hs.2]
        exact hbnd ⟨heq1, heq2⟩
      exact False.elim (hn ⟨t, s, ht.1, hts, hs.2, hshort,
        subinterval_signature_zero_of_prefix_eq p m hp hm he.symm⟩)

/-- Restricting the curve interval also restricts its actual signature, even
though the explicit Jordan pair is recomputed for the smaller interval. -/
theorem curveSignature_subinterval_eq {ι : Type*} (f : ι → ℝ → ℝ) {a b s t : ℝ}
    (hab : a ≤ b) (hf : ∀ i, BoundedVariationOn (f i) (Icc a b))
    (hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (w : List ι) :
    curveSignature f hst (fun i => (hf i).mono (Icc_subset_Icc has htb))
      (fun i => (hc i).mono (Icc_subset_Icc has htb)) w =
      stieltjesSignature (fun i => canonicalPositive hab (hf i) (hc i))
        (fun i => canonicalNegative hab (hf i) (hc i)) s t w := by
  apply curveSignature_eq_representation _ _ _ _ _ _
    (fun i => canonicalPositive_continuous hab (hf i) (hc i))
    (fun i => canonicalNegative_continuous hab (hf i) (hc i))
  intro i x hx y hy
  exact canonical_represents hab (hf i) (hc i) x (Icc_subset_Icc has htb hx)
    y (Icc_subset_Icc has htb hy)

theorem curveSignature_singleton {ι : Type*} (f : ι → ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ i, BoundedVariationOn (f i) (Icc a b))
    (hc : ∀ i, ContinuousOn (f i) (Icc a b)) (i : ι) :
    curveSignature f hab hf hc [i] = f i b - f i a := by
  change stieltjesIntegral _ _ a b (fun _ => 1) = _
  rw [stieltjesIntegral_one _ _ hab]
  exact canonical_represents hab (hf i) (hc i) a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩

/-- A genuinely shorter closed subcurve with trivial canonical BV signature.
No globally selected Stieltjes representation occurs in the conclusion. -/
theorem curveSignature_exists_proper_trivial_subinterval {ι : Type*}
    (f : ι → ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ∀ i, BoundedVariationOn (f i) (Icc a b))
    (hc : ∀ i, ContinuousOn (f i) (Icc a b))
    (hzero : ∀ w : List ι, w ≠ [] → curveSignature f hab.le hf hc w = 0) :
    ∃ s t : ℝ, ∃ has : a ≤ s, ∃ hst : s < t, ∃ htb : t ≤ b,
      t - s < b - a ∧ (∀ i, f i s = f i t) ∧
      ∀ w : List ι, w ≠ [] →
        curveSignature f hst.le (fun i => (hf i).mono (Icc_subset_Icc has htb))
          (fun i => (hc i).mono (Icc_subset_Icc has htb)) w = 0 := by
  obtain ⟨s, t, has, hst, htb, hshort, hz⟩ := exists_proper_trivial_subinterval
    (fun i => canonicalPositive hab.le (hf i) (hc i))
    (fun i => canonicalNegative hab.le (hf i) (hc i))
    (fun i => canonicalPositive_continuous hab.le (hf i) (hc i))
    (fun i => canonicalNegative_continuous hab.le (hf i) (hc i)) hab hzero
  have hs : ∀ w : List ι, w ≠ [] →
      curveSignature f hst.le (fun i => (hf i).mono (Icc_subset_Icc has htb))
        (fun i => (hc i).mono (Icc_subset_Icc has htb)) w = 0 := by
    intro w hw
    rw [curveSignature_subinterval_eq f hab.le hf hc has hst.le htb]
    exact hz w hw
  refine ⟨s, t, has, hst, htb, hshort, ?_, hs⟩
  intro i
  have hi := hs [i] (by simp)
  rw [curveSignature_singleton] at hi
  linarith

theorem pathSignature_exists_proper_trivial_subinterval {ι : Type*} [Fintype ι]
    (γ : ℝ → (ι → ℝ)) {a b : ℝ} (hab : a < b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hzero : ∀ w : List ι, w ≠ [] → pathSignature γ hab.le hγ hc w = 0) :
    ∃ s t : ℝ, ∃ has : a ≤ s, ∃ hst : s < t, ∃ htb : t ≤ b,
      t - s < b - a ∧ γ s = γ t ∧
      ∀ w : List ι, w ≠ [] →
        pathSignature γ hst.le (hγ.mono (Icc_subset_Icc has htb))
          (hc.mono (Icc_subset_Icc has htb)) w = 0 := by
  obtain ⟨s, t, has, hst, htb, hshort, he, hz⟩ :=
    curveSignature_exists_proper_trivial_subinterval (fun i t => γ t i) hab
      (coordinate_boundedVariation hγ) (coordinate_continuousOn hc) hzero
  exact ⟨s, t, has, hst, htb, hshort, funext he, hz⟩

end LinearInputCurveWordBVSubinterval
