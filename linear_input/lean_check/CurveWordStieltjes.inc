/-!
Stieltjes measures of C1 coordinates and their actual iterated integrals.
The measure/density identification is proved from interval masses and FTC.
-/

noncomputable section

namespace LinearInputCurveWordStieltjes

open Real Set MeasureTheory Filter
open scoped Topology

def ofContinuousMonotone (f : ℝ → ℝ) (hm : Monotone f) (hc : Continuous f) :
    StieltjesFunction ℝ where
  toFun := f
  mono' := hm
  right_continuous' := fun _ => hc.continuousWithinAt

theorem c1_stieltjes_measure {f v : ℝ → ℝ} (hm : Monotone f) (hc : Continuous f)
    (hd : ∀ t, HasDerivAt f (v t) t) (hv : Continuous v) (hn : ∀ t, 0 ≤ v t) :
    (ofContinuousMonotone f hm hc).measure = volume.withDensity (fun t => ENNReal.ofReal (v t)) := by
  apply Measure.ext_of_Ioc
  intro a b hab
  rw [StieltjesFunction.measure_Ioc, withDensity_apply _ measurableSet_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (hv.intervalIntegrable a b).1
      (Eventually.of_forall hn),
    ← intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hv.intervalIntegrable a b)]
  rfl

def primitive (v : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in 0..t, v s

theorem primitive_hasDerivAt {v : ℝ → ℝ} (hv : Continuous v) (t : ℝ) :
    HasDerivAt (primitive v) (v t) t :=
  intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 t)
    hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt

theorem primitive_continuous {v : ℝ → ℝ} (hv : Continuous v) : Continuous (primitive v) :=
  (show Differentiable ℝ (primitive v) from fun t => (primitive_hasDerivAt hv t).differentiableAt).continuous

theorem primitive_sub {v : ℝ → ℝ} (hv : Continuous v) (a b : ℝ) :
    primitive v b - primitive v a = ∫ t in a..b, v t := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hv.intervalIntegrable 0 a) (hv.intervalIntegrable a b)
  dsimp [primitive]
  linarith

theorem primitive_monotone {v : ℝ → ℝ} (hv : Continuous v) (hn : ∀ t, 0 ≤ v t) :
    Monotone (primitive v) := by
  intro a b hab
  apply sub_nonneg.mp
  rw [primitive_sub hv]
  exact intervalIntegral.integral_nonneg hab (fun t _ => hn t)

def primitiveStieltjes (v : ℝ → ℝ) (hv : Continuous v) (hn : ∀ t, 0 ≤ v t) :
    StieltjesFunction ℝ :=
  ofContinuousMonotone (primitive v) (primitive_monotone hv hn) (primitive_continuous hv)

theorem primitiveStieltjes_measure (v : ℝ → ℝ) (hv : Continuous v) (hn : ∀ t, 0 ≤ v t) :
    (primitiveStieltjes v hv hn).measure =
      volume.withDensity (fun t => ENNReal.ofReal (v t)) :=
  c1_stieltjes_measure (primitive_monotone hv hn) (primitive_continuous hv)
    (primitive_hasDerivAt hv) hv hn

theorem intervalIntegral_withDensity (v : ℝ → ℝ) (hv : Continuous v)
    (hn : ∀ t, 0 ≤ v t) (F : ℝ → ℝ) (a b : ℝ) :
    (∫ t in a..b, F t ∂volume.withDensity (fun t => ENNReal.ofReal (v t))) =
      ∫ t in a..b, v t * F t := by
  simp only [intervalIntegral]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
      hv.measurable.ennreal_ofReal (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _ measurableSet_Ioc,
    setIntegral_withDensity_eq_setIntegral_toReal_smul
      hv.measurable.ennreal_ofReal (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _ measurableSet_Ioc]
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul]

def positiveVelocity (v : ℝ → ℝ) (t : ℝ) : ℝ := max (v t) 0

def negativeVelocity (v : ℝ → ℝ) (t : ℝ) : ℝ := max (-v t) 0

theorem positiveVelocity_continuous {v : ℝ → ℝ} (hv : Continuous v) :
    Continuous (positiveVelocity v) := hv.max continuous_const

theorem negativeVelocity_continuous {v : ℝ → ℝ} (hv : Continuous v) :
    Continuous (negativeVelocity v) := hv.neg.max continuous_const

theorem velocity_decomposition (v : ℝ → ℝ) (t : ℝ) :
    positiveVelocity v t - negativeVelocity v t = v t := by
  dsimp [positiveVelocity, negativeVelocity]
  by_cases ht : 0 ≤ v t
  · rw [max_eq_left ht, max_eq_right (neg_nonpos.mpr ht), sub_zero]
  · rw [max_eq_right (le_of_not_ge ht), max_eq_left (neg_nonneg.mpr (le_of_not_ge ht))]
    ring

def positiveStieltjes (v : ℝ → ℝ) (hv : Continuous v) : StieltjesFunction ℝ :=
  primitiveStieltjes (positiveVelocity v) (positiveVelocity_continuous hv) (fun _ => le_max_right _ _)

def negativeStieltjes (v : ℝ → ℝ) (hv : Continuous v) : StieltjesFunction ℝ :=
  primitiveStieltjes (negativeVelocity v) (negativeVelocity_continuous hv) (fun _ => le_max_right _ _)

/-- Oriented integration against the difference of two genuine Stieltjes measures. -/
def stieltjesIntegral (p m : StieltjesFunction ℝ) (a b : ℝ) (F : ℝ → ℝ) : ℝ :=
  (∫ t in a..b, F t ∂p.measure) - ∫ t in a..b, F t ∂m.measure

theorem c1_stieltjesIntegral {v F : ℝ → ℝ} (hv : Continuous v) (hF : Continuous F) (a b : ℝ) :
    stieltjesIntegral (positiveStieltjes v hv) (negativeStieltjes v hv) a b F =
      ∫ t in a..b, F t * v t := by
  unfold stieltjesIntegral positiveStieltjes negativeStieltjes
  rw [primitiveStieltjes_measure, primitiveStieltjes_measure,
    intervalIntegral_withDensity _ (positiveVelocity_continuous hv) (fun _ => le_max_right _ _),
    intervalIntegral_withDensity _ (negativeVelocity_continuous hv) (fun _ => le_max_right _ _)]
  have hP : IntervalIntegrable (fun t => positiveVelocity v t * F t) volume a b :=
    ((positiveVelocity_continuous hv).mul hF).intervalIntegrable a b
  have hM : IntervalIntegrable (fun t => negativeVelocity v t * F t) volume a b :=
    ((negativeVelocity_continuous hv).mul hF).intervalIntegrable a b
  rw [← intervalIntegral.integral_sub hP hM]
  apply intervalIntegral.integral_congr
  intro t _
  change positiveVelocity v t * F t - negativeVelocity v t * F t = F t * v t
  rw [← sub_mul, velocity_decomposition, mul_comm]

theorem coordinate_increment {f v : ℝ → ℝ} (hv : Continuous v)
    (hd : ∀ t, HasDerivAt f (v t) t) (a b : ℝ) :
    stieltjesIntegral (positiveStieltjes v hv) (negativeStieltjes v hv) a b (fun _ => 1) =
      f b - f a := by
  rw [c1_stieltjesIntegral hv continuous_const]
  simp only [one_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hv.intervalIntegrable a b)

/-- Each integration step uses the signed difference of the two Stieltjes
measures; no velocity-integral formula occurs in this definition. -/
def reverseStieltjes {ι : Type*} (p m : ι → StieltjesFunction ℝ) (a : ℝ) :
    List ι → ℝ → ℝ
  | [], _ => 1
  | i :: w, b => stieltjesIntegral (p i) (m i) a b (reverseStieltjes p m a w)

def stieltjesSignature {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (a b : ℝ) (w : List ι) : ℝ := reverseStieltjes p m a w.reverse b

theorem reverseStieltjes_eq_reverseIntegral {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a : ℝ) (w : List ι) (b : ℝ) :
    reverseStieltjes (fun i => positiveStieltjes (v i) (hv i))
        (fun i => negativeStieltjes (v i) (hv i)) a w b =
      LinearInputCurveWordSignature.reverseIntegral v a w b := by
  induction w generalizing b with
  | nil => rfl
  | cons i w ih =>
    change stieltjesIntegral _ _ a b _ = _
    rw [show reverseStieltjes (fun i => positiveStieltjes (v i) (hv i))
        (fun i => negativeStieltjes (v i) (hv i)) a w =
        LinearInputCurveWordSignature.reverseIntegral v a w from funext ih,
      c1_stieltjesIntegral (hv i) (LinearInputCurveWordSignature.reverseIntegral_continuous hv a w)]
    rfl

/-- At every finite degree, the actual Stieltjes signature of the C1 coordinate
primitives equals the existing iterated velocity-integral signature. -/
theorem c1_stieltjesSignature_eq_signature {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) (w : List ι) :
    stieltjesSignature (fun i => positiveStieltjes (v i) (hv i))
        (fun i => negativeStieltjes (v i) (hv i)) a b w =
      LinearInputCurveWordSignature.signature v a b w :=
  reverseStieltjes_eq_reverseIntegral hv a w.reverse b

open LinearInputCurveWordBoundedVariation

def jordanPositive (f : ℝ → ℝ) (a t : ℝ) : ℝ :=
  (variationOnFromTo f univ a t + f t - f a) / 2

def jordanNegative (f : ℝ → ℝ) (a t : ℝ) : ℝ :=
  (variationOnFromTo f univ a t - f t + f a) / 2

theorem jordan_difference (f : ℝ → ℝ) (a t : ℝ) :
    jordanPositive f a t - jordanNegative f a t = f t - f a := by
  unfold jordanPositive jordanNegative
  ring

theorem jordan_sum (f : ℝ → ℝ) (a t : ℝ) :
    jordanPositive f a t + jordanNegative f a t = variationOnFromTo f univ a t := by
  unfold jordanPositive jordanNegative
  ring

theorem jordan_monotone {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) (a : ℝ) :
    Monotone (jordanPositive f a) ∧ Monotone (jordanNegative f a) := by
  have hclock := variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn (mem_univ a)
  have hbound (x y : ℝ) (hxy : x ≤ y) :
      |f x - f y| ≤ variationOnFromTo f univ a y - variationOnFromTo f univ a x := by
    have hd := distance_le_variation_difference hf.locallyBoundedVariationOn
      (mem_univ a) (mem_univ x) (mem_univ y)
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hclock (mem_univ x) (mem_univ y) hxy))] at hd
    exact hd
  constructor
  · intro x y hxy
    have hb := (abs_le.mp (hbound x y hxy)).2
    unfold jordanPositive
    linarith
  · intro x y hxy
    have hb := (abs_le.mp (hbound x y hxy)).1
    unfold jordanNegative
    linarith

theorem jordan_continuous {f : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    (hc : Continuous f) (a : ℝ) :
    Continuous (jordanPositive f a) ∧ Continuous (jordanNegative f a) := by
  have hclock : Continuous (variationOnFromTo f univ a) :=
    continuousOn_univ.mp (variation_clock_continuousOn hf hc.continuousOn (mem_univ a))
  exact ⟨((hclock.add hc).sub continuous_const).div_const 2,
    ((hclock.sub hc).add continuous_const).div_const 2⟩

def bvPositive {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) (hc : Continuous f) (a : ℝ) :
    StieltjesFunction ℝ :=
  ofContinuousMonotone (jordanPositive f a) (jordan_monotone hf a).1 (jordan_continuous hf hc a).1

def bvNegative {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) (hc : Continuous f) (a : ℝ) :
    StieltjesFunction ℝ :=
  ofContinuousMonotone (jordanNegative f a) (jordan_monotone hf a).2 (jordan_continuous hf hc a).2

/-- The signed interval mass of the canonical BV Stieltjes pair is exactly
the coordinate increment. -/
theorem bv_signed_interval_mass {f : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    (hc : Continuous f) (a x y : ℝ) (hxy : x ≤ y) :
    ((bvPositive hf hc a).measure (Ioc x y)).toReal -
        ((bvNegative hf hc a).measure (Ioc x y)).toReal = f y - f x := by
  rw [StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((bvPositive hf hc a).mono hxy)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((bvNegative hf hc a).mono hxy))]
  change (jordanPositive f a y - jordanPositive f a x) -
    (jordanNegative f a y - jordanNegative f a x) = _
  have hx := jordan_difference f a x
  have hy := jordan_difference f a y
  linarith

/-- Extension by endpoint constants converts any continuous BV coordinate on
a compact interval into a global continuous BV coordinate with the same values. -/
theorem compact_bv_stieltjes_representation {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hc : ContinuousOn f (Icc a b)) :
    ∃ p m : StieltjesFunction ℝ,
      Continuous (p : ℝ → ℝ) ∧ Continuous (m : ℝ → ℝ) ∧
      (∀ t ∈ Icc a b, p t - m t = f t - f a) ∧
      (∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
        (p.measure (Ioc x y)).toReal - (m.measure (Ioc x y)).toReal = f y - f x) := by
  let F := f ∘ clamp a b
  have hF := constantExtension_boundedVariation hab hf
  have hC := constantExtension_continuous hab hc
  refine ⟨bvPositive hF hC a, bvNegative hF hC a,
    (jordan_continuous hF hC a).1, (jordan_continuous hF hC a).2, ?_, ?_⟩
  · intro t ht
    change jordanPositive F a t - jordanNegative F a t = _
    rw [jordan_difference]
    simp only [F, Function.comp_apply, clamp_eq ht, clamp_eq (show a ∈ Icc a b from ⟨le_rfl, hab⟩)]
  · intro x hx y hy hxy
    rw [bv_signed_interval_mass hF hC a x y hxy]
    simp only [Function.comp_apply, clamp_eq hx, clamp_eq hy]

end LinearInputCurveWordStieltjes
