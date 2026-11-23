import ObservedQuotient
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

/-! The normalized standard interval, fair independent binary labels,
and the uniform phase of the observed square sandpile. The comparison
of the uncalibrated and calibrated metrics uses this *same* law. -/
noncomputable section
open MeasureTheory ObservedSandpile Set
open scoped ENNReal
namespace SingleSquare

abbrev Samples := (H × Bits) × Phase

def heightLaw : Measure H := (2 : ℝ≥0∞)⁻¹ • (Measure.comap Subtype.val (volume : Measure ℝ))
def bitsLaw : Measure Bits :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)
def angleLaw : Measure Phase :=
  Measure.map (fun x : ℝ => (x : Phase)) (volume.restrict (Ico (0:ℝ) 1))
def standardLaw : Measure Samples := (heightLaw.prod bitsLaw).prod angleLaw

instance heightLaw_probability : IsProbabilityMeasure heightLaw := by
  constructor
  rw [heightLaw, Measure.smul_apply, comap_subtype_coe_apply measurableSet_Icc]
  rw [Set.image_univ, Subtype.range_coe, Real.volume_Icc]
  norm_num [smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance bitsLaw_probability : IsProbabilityMeasure bitsLaw := by
  unfold bitsLaw
  infer_instance

instance angleLaw_probability : IsProbabilityMeasure angleLaw := by
  constructor
  rw [angleLaw, Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp [Real.volume_Ico]

instance standardLaw_probability : IsProbabilityMeasure standardLaw := by
  unfold standardLaw
  infer_instance

theorem standard_height_marginal (S : Set H) :
    standardLaw {w | w.1.1 ∈ S} = heightLaw S := by
  have he : {w : Samples | w.1.1 ∈ S} = (S ×ˢ (univ : Set Bits)) ×ˢ (univ : Set Phase) := by
    ext w; simp
  rw [he, standardLaw, Measure.prod_prod, Measure.prod_prod]
  simp

/-- On a subinterval of [-1,1], the observed standard coordinate is uniform. -/
theorem sampled_interval_mass {u v : ℝ} (hu : -1 ≤ u) (hv : v ≤ 1) :
    standardLaw {w | w.1.1.1 ∈ Icc u v} = ENNReal.ofReal ((v-u)/2) := by
  rw [show {w : Samples | w.1.1.1 ∈ Icc u v} =
      {w : Samples | w.1.1 ∈ ((↑) : H → ℝ) ⁻¹' Icc u v} from rfl,
    standard_height_marginal, heightLaw, Measure.smul_apply,
    comap_subtype_coe_apply measurableSet_Icc]
  have image : ((↑) : H → ℝ) '' (((↑) : H → ℝ) ⁻¹' Icc u v) = Icc u v := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx
      exact ⟨⟨x,hu.trans hx.1,hx.2.trans hv⟩,hx,rfl⟩
  rw [image, Real.volume_Icc, ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num [div_eq_mul_inv,smul_eq_mul,mul_comm]

def rawSampleHeight (a : ℝ) (s : Samples) : ℝ := signedPower (a+1)⁻¹ s.1.1.1

theorem rawSampleHeight_measurable (a : ℝ) (ha : 0 ≤ a) : Measurable (rawSampleHeight a) := by
  have h : Measurable (fun s : Samples => s.1.1.1) := by fun_prop
  have he : 0 ≤ (a+1)⁻¹ := by positivity
  unfold rawSampleHeight signedPower
  exact Measurable.ite (measurableSet_le measurable_const h)
    ((Real.continuous_rpow_const he).measurable.comp h)
    (((Real.continuous_rpow_const he).measurable.comp h.neg).neg)

private theorem absolute_signedPower (p x : ℝ) : |signedPower p x| = |x|^p := by
  by_cases hx : 0 ≤ x
  · simp [signedPower,hx,abs_of_nonneg hx, abs_of_nonneg (Real.rpow_nonneg hx p)]
  · have hn : 0 ≤ -x := by linarith
    simp [signedPower,hx,abs_of_neg (lt_of_not_ge hx),abs_of_nonneg (Real.rpow_nonneg hn p)]

theorem sample_band_mass (a : ℝ) (ha : 0 ≤ a) {δ : ℝ} (hd : 0 < δ) (hd' : δ ≤ 1/2) :
    standardLaw ((rawSampleHeight a) ⁻¹' Icc (-δ) δ) = ENNReal.ofReal (δ^(a+1)) := by
  have hp : 0 < a+1 := by linarith
  have hh := Real.rpow_le_one hd.le (show δ ≤ 1 by linarith) hp.le
  have he : (rawSampleHeight a) ⁻¹' Icc (-δ) δ =
      {s : Samples | s.1.1.1 ∈ Icc (-(δ^(a+1))) (δ^(a+1))} := by
    ext s
    change -δ ≤ rawSampleHeight a s ∧ rawSampleHeight a s ≤ δ ↔
      -(δ^(a+1)) ≤ s.1.1.1 ∧ s.1.1.1 ≤ δ^(a+1)
    rw [← abs_le, ← abs_le, rawSampleHeight, absolute_signedPower]
    exact Real.rpow_inv_le_iff_of_pos (abs_nonneg _) hd.le hp
  rw [he, sampled_interval_mass (by linarith) hh]
  congr 1
  ring

/-- Both wings have at least 1/4 of the sampled mass uniformly in a.
On [-1,1] a positive root of order at least one moves |s| outwards. -/
theorem sample_wings (a : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal (1/4:ℝ) ≤ standardLaw {w | rawSampleHeight a w ≤ -(1/2:ℝ)} ∧
    ENNReal.ofReal (1/4:ℝ) ≤ standardLaw {w | (1/2:ℝ) ≤ rawSampleHeight a w} := by
  have hp : 0 < a+1 := by linarith
  have hh : (1/2:ℝ)^(a+1) ≤ (1/2:ℝ) := by
    calc
      _ ≤ (1/2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = _ := Real.rpow_one _
  have left := sampled_interval_mass (u := -1) (v := -(1/2:ℝ)) (by norm_num) (by norm_num)
  have right := sampled_interval_mass (u := 1/2) (v := 1) (by norm_num) (by norm_num)
  norm_num at left right
  constructor
  · rw [← left]
    apply measure_mono
    intro s hs
    have hs' : s.1.1.1 ≤ -(1/2:ℝ) := hs.2
    have hx : ¬ 0 ≤ s.1.1.1 := by linarith
    have hval := (Real.le_rpow_inv_iff_of_pos (by norm_num : 0 ≤ (1/2:ℝ))
      (show 0 ≤ -s.1.1.1 by linarith) hp).2 (by linarith : (1/2:ℝ)^(a+1) ≤ -s.1.1.1)
    change signedPower (a+1)⁻¹ s.1.1.1 ≤ -(1/2)
    rw [signedPower, if_neg hx]
    linarith
  · rw [← right]
    apply measure_mono
    intro s hs
    have hs' : (1/2:ℝ) ≤ s.1.1.1 := hs.1
    have hx : 0 ≤ s.1.1.1 := by linarith
    change (1/2:ℝ) ≤ signedPower (a+1)⁻¹ s.1.1.1
    rw [signedPower, if_pos hx]
    exact (Real.le_rpow_inv_iff_of_pos (by norm_num) hx hp).2 (hh.trans hs')

#print axioms standardLaw_probability
#print axioms sample_band_mass
#print axioms sample_wings
end SingleSquare
