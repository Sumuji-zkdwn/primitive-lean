import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! A central cut on any space admitting a 1-Lipschitz height coordinate.
We use the clipped height itself as a test function. Multiplying both
it and its upper gradient by the reciprocal of the band width gives
the usual unit ramp. This file does not import the sandpile model. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SubLaakso.Cut

def clip (l u x : ℝ) : ℝ := min (max x l) u
def inside (l u x : ℝ) : ℝ := (Icc l u).indicator (fun _ => (1:ℝ)) x

theorem clip_lipschitz (l u : ℝ) : LipschitzWith 1 (clip l u) :=
  (LipschitzWith.max_const LipschitzWith.id l).min_const u

theorem inside_measurable (l u : ℝ) : Measurable (inside l u) :=
  measurable_const.indicator measurableSet_Icc

theorem inside_nonneg (l u x : ℝ) : 0 ≤ inside l u x := by
  by_cases h : x ∈ Icc l u <;> simp [inside, h]

theorem occupation_upper {l u s t : ℝ} (hlu : l ≤ u) (hst : s ≤ t)
    (y : ℝ → ℝ) (hy : LipschitzWith 1 y) :
    |clip l u (y t) - clip l u (y s)| ≤ ∫ z in s..t, inside l u (y z) := by
  let f := clip l u ∘ y
  have hLip : LipschitzWith 1 f := by simpa [f] using (clip_lipschitz l u).comp hy
  have hac : AbsolutelyContinuousOnInterval f s t :=
    hLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hband : MeasurableSet (y ⁻¹' Icc l u) := hy.continuous.measurable measurableSet_Icc
  have hrepr : (fun z => inside l u (y z)) =
      (y ⁻¹' Icc l u).indicator (fun _ => (1:ℝ)) := by
    ext z
    by_cases hz : y z ∈ Icc l u <;> simp [inside, hz]
  have hg : IntervalIntegrable (fun z => inside l u (y z)) volume s t := by
    rw [hrepr, intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact (integrableOn_const (by simp) (by simp)).indicator hband
  have hder (z : ℝ) : |deriv f z| ≤ inside l u (y z) := by
    by_cases hz : y z ∈ Icc l u
    · simpa [inside, hz, Real.norm_eq_abs] using
        (norm_deriv_le_of_lipschitz (x₀ := z) hLip)
    · have hz' : y z < l ∨ u < y z := by
        rcases lt_or_ge (y z) l with h | h
        · exact Or.inl h
        · exact Or.inr (lt_of_not_ge (fun h' => hz ⟨h,h'⟩))
      have hd : deriv f z = 0 := by
        rcases hz' with hleft | hright
        · have he : f =ᶠ[𝓝 z] (fun _ => l) := by
            filter_upwards [hy.continuous.continuousAt.eventually_lt
              (g := fun _ => l) continuousAt_const hleft] with w hw
            simp [f, clip, max_eq_right hw.le, min_eq_left hlu]
          rw [he.deriv_eq]; simp
        · have he : f =ᶠ[𝓝 z] (fun _ => u) := by
            filter_upwards [continuousAt_const.eventually_lt
              hy.continuous.continuousAt hright] with w hw
            simp [f, clip, min_eq_right (hw.le.trans (le_max_left _ _))]
          rw [he.deriv_eq]; simp
      simp [inside, hz, hd]
  change |f t-f s| ≤ _
  rw [← hac.integral_deriv_eq_sub]
  apply (intervalIntegral.abs_integral_le_integral_abs hst).trans
  apply intervalIntegral.integral_mono_on hst _ hg (fun x _ => hder x)
  exact hac.intervalIntegrable_deriv.abs

/-- Pullback along a real-valued height, in the ENNReal line-integral
convention on Icc 0 T used by the quotient PI formalization. -/
theorem upper_along_height {X : Type*} {d : X → X → ℝ} (H : X → ℝ)
    (hH : ∀ x y, |H x-H y| ≤ d x y) {l u : ℝ} (hlu : l ≤ u)
    {T : ℝ} (hT : 0 ≤ T) (γ : ℝ → X)
    (hγ : ∀ s t, d (γ s) (γ t) ≤ |s-t|) :
    ENNReal.ofReal |clip l u (H (γ T))-clip l u (H (γ 0))| ≤
      ∫⁻ s in Icc 0 T, ENNReal.ofReal (inside l u (H (γ s))) := by
  let y := H ∘ γ
  have hy : LipschitzWith 1 y := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simpa [Real.dist_eq,y] using (hH (γ s) (γ t)).trans (hγ s t)
  have h := ENNReal.ofReal_le_ofReal (occupation_upper hlu hT y hy)
  rw [intervalIntegral.integral_of_le hT,
    Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))] at h
  have hg : IntegrableOn (fun x => inside l u (y x)) (Icc 0 T) := by
    apply Integrable.mono' (g := fun _ => (1:ℝ)) (integrableOn_const (by simp) (by simp))
    · exact ((inside_measurable l u).comp hy.continuous.measurable).aestronglyMeasurable
    · apply ae_of_all
      intro x
      by_cases hx : y x ∈ Icc l u <;> simp [inside,hx]
  rw [ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ (fun x => inside_nonneg l u (y x)))] at h
  exact h

/-- Mean-zero whole-ball consequence of a weighted (1,1)-PI on [-1,1].
The weight is |x|^q and distance is Euclidean in this calibrated height.
The tested functions are globally defined and their upper gradients
control every 1-Lipschitz real path, including all paths in [-1,1]. -/
def WholeBallPI (q : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : ℝ → ℝ), LipschitzWith 1 f → Measurable g →
    (∀ x, |f x| ≤ 1) → (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) →
    (∀ (y : ℝ → ℝ), LipschitzWith 1 y → ∀ s t : ℝ, s ≤ t →
      |f (y t)-f (y s)| ≤ ∫ z in s..t, g (y z)) →
    (∫ x in (-1:ℝ)..1, |x|^q * f x) = 0 →
    (∫ x in (-1:ℝ)..1, |x|^q * |f x|) ≤ C * ∫ x in (-1:ℝ)..1, |x|^q * g x

theorem symmetric_clip_mean_zero {r : ℝ} (hr : 0 ≤ r) (q : ℝ) :
    (∫ x in (-1:ℝ)..1, |x|^q * clip (-r) r x) = 0 := by
  let F := fun x : ℝ => |x|^q * clip (-r) r x
  have oddclip (x : ℝ) : clip (-r) r (-x) = -(clip (-r) r x) := by
    simp only [clip, min_def, max_def]
    split_ifs <;> linarith
  have ho (x : ℝ) : F (-x) = -(F x) := by simp [F,oddclip]
  have h := intervalIntegral.integral_comp_neg (a := (-1:ℝ)) (b := 1) F
  simp only [neg_neg,ho,intervalIntegral.integral_neg] at h
  change (∫ x in (-1:ℝ)..1, F x) = 0
  linarith

theorem cut_energy_le {r q : ℝ} (hr : 0 < r) (hq : 0 ≤ q) :
    (∫ x in (-1:ℝ)..1, |x|^q * inside (-r) r x) ≤ (2*r)*r^q := by
  have hrepr : (fun x : ℝ => |x|^q * inside (-r) r x) =
      (Icc (-r) r).indicator (fun x => |x|^q) := by
    ext x; by_cases hx : x ∈ Icc (-r) r <;> simp [inside,hx]
  have hc : Continuous (fun x : ℝ => |x|^q) := (Real.continuous_rpow_const hq).comp continuous_abs
  rw [hrepr, intervalIntegral.integral_of_le (by norm_num), setIntegral_indicator measurableSet_Icc]
  calc
    _ ≤ ∫ x in Icc (-r) r, |x|^q :=
      setIntegral_mono_set hc.integrableOn_Icc
        (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg x) _) inter_subset_right.eventuallyLE
    _ ≤ ∫ _ in Icc (-r) r, r^q := by
      apply setIntegral_mono_on hc.integrableOn_Icc (integrableOn_const (by simp) (by simp))
        measurableSet_Icc
      intro x hx
      exact Real.rpow_le_rpow (abs_nonneg _) (abs_le.mpr hx) hq
    _ = _ := by
      rw [setIntegral_const, Real.volume_real_Icc, max_eq_left (show 0 ≤ r - -r by linarith),
        smul_eq_mul]
      ring

theorem cut_osc_lower {r q : ℝ} (hr : 0 < r) (hr' : r ≤ 1/2) (hq : 0 ≤ q) :
    (1/2:ℝ) * ((1/2:ℝ)^q*r) ≤ ∫ x in (-1:ℝ)..1, |x|^q * |clip (-r) r x| := by
  have hc : Continuous (fun x : ℝ => |x|^q * |clip (-r) r x|) :=
    ((Real.continuous_rpow_const hq).comp continuous_abs).mul (clip_lipschitz (-r) r).continuous.abs
  calc
    _ = ∫ _ in (1/2:ℝ)..1, ((1/2:ℝ)^q*r) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ ∫ x in (1/2:ℝ)..1, |x|^q * |clip (-r) r x| := by
      apply intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
        (hc.intervalIntegrable _ _)
      intro x hx
      have ht : r ≤ x := hr'.trans hx.1
      have hp : 0 ≤ x := hr.le.trans ht
      simp only [clip, min_eq_right (ht.trans (le_max_left _ _)), abs_of_nonneg hr.le,
        abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by norm_num) hx.1 hq) hr.le
    _ ≤ _ := intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) le_rfl
      (ae_of_all _ fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg x) _) (abs_nonneg _))
      (hc.intervalIntegrable _ _)

/-- A genuine global PI obstruction on an interval, with explicit
Lipschitz functions and Borel upper gradients, for every real q>0. -/
theorem not_wholeBallPI {q : ℝ} (hq : 0 < q) : ¬ WholeBallPI q := by
  rintro ⟨C,hC,hPI⟩
  have hsmall (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) :
      (1/2:ℝ)*(1/2:ℝ)^q ≤ (2*C)*r^q := by
    have hl : -r ≤ r := by linarith
    have hfbound (x : ℝ) : |clip (-r) r x| ≤ 1 := by
      apply abs_le.mpr
      constructor
      · apply le_min <;> first | exact (show (-1:ℝ) ≤ -r by linarith).trans (le_max_right _ _) | linarith
      · exact (min_le_right _ _).trans (by linarith)
    have hgbound (x : ℝ) : inside (-r) r x ≤ 1 := by
      by_cases hx : x ∈ Icc (-r) r <;> simp [inside,hx]
    have h := hPI (clip (-r) r) (inside (-r) r) (clip_lipschitz _ _) (inside_measurable _ _)
      hfbound (inside_nonneg _ _) hgbound (fun y hy s t hst => occupation_upper hl hst y hy)
      (symmetric_clip_mean_zero hr.le q)
    have hi := (cut_osc_lower hr hr' hq.le).trans
      (h.trans (mul_le_mul_of_nonneg_left (cut_energy_le hr hq.le) hC))
    apply (le_of_mul_le_mul_right _ hr)
    convert hi using 1 <;> ring
  have hd : Tendsto (fun r : ℝ => r^q) (𝓝[>] 0) (𝓝 0) := by
    have hc := (Real.continuous_rpow_const hq.le).continuousAt (x := (0:ℝ))
    simpa [ContinuousWithinAt, Real.zero_rpow hq.ne'] using hc.continuousWithinAt (s := Ioi (0:ℝ))
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, (1/2:ℝ)*(1/2:ℝ)^q ≤ (2*C)*r^q := by
    have hh : ∀ᶠ r : ℝ in 𝓝[>] 0, r ≤ 1/2 :=
      (eventually_le_nhds (by norm_num : (0:ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hh] with r hr hr'
    exact hsmall r hr hr'
  have bad := le_of_tendsto_of_tendsto tendsto_const_nhds (hd.const_mul (2*C)) hev
  have hp : 0 < (1/2:ℝ)*(1/2:ℝ)^q := by positivity
  simpa using (not_le.mpr hp (by simpa using bad))

/-- In signed-power length coordinates, the pushforward density exponent
is q=(a-b)/(1+b); a>b is exactly the obstructed regime. -/
theorem transformed_cut_obstruction {a b : ℝ} (hb : 0 ≤ b) (hab : b < a) :
    ¬ WholeBallPI ((a-b)/(1+b)) := not_wholeBallPI (div_pos (sub_pos.mpr hab) (by linarith))

/-- Whole-space consequence tested by globally 1-Lipschitz functions
on an arbitrary metric measure space. A bounded-space weak PI implies
this on a ball containing the space, with its radius absorbed into C. -/
def MetricWholePI {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : X → ℝ), LipschitzWith 1 f → Measurable g →
    (∀ x, |f x| ≤ 1) → (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) →
    (∀ (γ : ℝ → X), LipschitzWith 1 γ → ∀ s t : ℝ, s ≤ t →
      |f (γ t)-f (γ s)| ≤ ∫ z in s..t, g (γ z)) →
    (∫ x, f x ∂μ) = 0 → (∫ x, |f x| ∂μ) ≤ C * ∫ x, g x ∂μ

/-- The interval obstruction lifts to *any* compact candidate when
its height is 1-Lipschitz and its measured height marginal is the
positive multiple of |x|^q dx displayed below. No lifting of paths
from the interval back to the candidate is needed. -/
theorem height_marginal_obstruction {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ] {q k : ℝ} (hq : 0 < q) (hk : 0 < k)
    (H : X → ℝ) (hH : LipschitzWith 1 H)
    (marginal : ∀ (φ : ℝ → ℝ), Measurable φ →
      (∫ x, φ (H x) ∂μ) = k * ∫ t in (-1:ℝ)..1, |t|^q * φ t) :
    ¬ MetricWholePI μ := by
  rintro ⟨C,hC,hPI⟩
  apply not_wholeBallPI hq
  refine ⟨C,hC,?_⟩
  intro f g hf hg hfbound hpos hgbound hupper hzero
  have hfl : LipschitzWith 1 (f ∘ H) := by simpa using hf.comp hH
  have hgl : Measurable (g ∘ H) := hg.comp hH.continuous.measurable
  have hu (γ : ℝ → X) (hγ : LipschitzWith 1 γ) (s t : ℝ) (hst : s ≤ t) :
      |(f ∘ H) (γ t) - (f ∘ H) (γ s)| ≤ ∫ z in s..t, (g ∘ H) (γ z) := by
    exact hupper (H ∘ γ) (by simpa using hH.comp hγ) s t hst
  have hz : (∫ x, (f ∘ H) x ∂μ) = 0 := by
    rw [show (∫ x, (f ∘ H) x ∂μ) = k * ∫ t in (-1:ℝ)..1, |t|^q*f t from
      marginal f hf.continuous.measurable, hzero, mul_zero]
  have h := hPI _ _ hfl hgl (fun x => hfbound (H x)) (fun x => hpos (H x))
    (fun x => hgbound (H x)) hu hz
  change (∫ x, |f (H x)| ∂μ) ≤ C * ∫ x, g (H x) ∂μ at h
  rw [marginal (fun t => |f t|) hf.continuous.abs.measurable, marginal g hg] at h
  apply le_of_mul_le_mul_left _ hk
  convert h using 1
  ring

#print axioms upper_along_height
#print axioms not_wholeBallPI
#print axioms transformed_cut_obstruction
#print axioms height_marginal_obstruction

end SubLaakso.Cut
