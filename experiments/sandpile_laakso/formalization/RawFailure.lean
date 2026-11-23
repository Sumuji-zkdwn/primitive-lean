import ObservedQuotient
import CutObstruction

/-! A cut obstruction for the actual weak Poincaré predicate on an observation.
Only distributions of heights, bounded diameter, and coordinate regularity are inputs.
Neither an energy bound for any test function nor an oscillation bound is assumed. -/

noncomputable section
open Set Filter MeasureTheory ObservedSandpile
open scoped ENNReal Topology

namespace SubLaakso.RawFailure

variable {Ω X : Type*} [MeasurableSpace Ω]

private theorem lower_on {P : Measure Ω} {S : Set Ω} (hS : MeasurableSet S)
    (k : ℝ≥0∞) (f : Ω → ℝ≥0∞) (h : ∀ w ∈ S, k ≤ f w) :
    k * P S ≤ ∫⁻ w, f w ∂P := by
  rw [← lintegral_indicator_const hS k]
  apply lintegral_mono
  intro w
  by_cases hw : w ∈ S
  · simpa [hw] using h w hw
  · simp [hw]

private theorem whole_average (D : Observation Ω X) [IsProbabilityMeasure D.law]
    (x : X) (r : ℝ) (hcov : ∀ w, D.distance x (D.readout w) < r) (f : X → ℝ≥0∞) :
    D.average x r f = ∫⁻ w, f (D.readout w) ∂D.law := by
  simp [Observation.average, Observation.ballIntegral, hcov]

/-- Positive mass on both outer half-intervals and a central band of mass at most
δ^(1+a) for a>0 obstruct the raw PI. The band estimate and outer masses refer only
to the sampled physical height. The samples are independent in the pairwise oscillation.
The measurability-test hypothesis records how the observation's Borel predicate treats
real coordinate functions. -/
theorem no_PI_of_thin_band (D : Observation Ω X) [IsProbabilityMeasure D.law]
    (height : X → ℝ) (hmeas : Measurable (fun w => height (D.readout w)))
    (hlip : ∀ x y, |height x - height y| ≤ D.distance x y)
    (hborel : ∀ ψ : ℝ → ℝ≥0∞, Measurable ψ → D.borelTest (fun x => ψ (height x)))
    (x : X) {R a c : ℝ} (hR : 0 < R) (ha : 0 < a) (hc : 0 < c)
    (hcov : ∀ w, D.distance x (D.readout w) < R)
    (hleft : ENNReal.ofReal c ≤ D.law {w | height (D.readout w) ≤ -(1/2 : ℝ)})
    (hright : ENNReal.ofReal c ≤ D.law {w | (1/2 : ℝ) ≤ height (D.readout w)})
    (hband : ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 →
      D.law ((fun w => height (D.readout w)) ⁻¹' Icc (-δ) δ) ≤
        ENNReal.ofReal (δ^(a+1))) : ¬ WeakPI D := by
  rintro ⟨C, Λ, hC, hΛ, pi⟩
  have hCR : 0 < C*R := mul_pos hC hR
  let left : Set Ω := {w | height (D.readout w) ≤ -(1/2 : ℝ)}
  let right : Set Ω := {w | (1/2 : ℝ) ≤ height (D.readout w)}
  have hL : MeasurableSet left := measurableSet_le hmeas measurable_const
  have hT : MeasurableSet right := measurableSet_le measurable_const hmeas
  have every (δ : ℝ) (hd : 0 < δ) (hh : δ ≤ 1/2) : 2*c*c ≤ C*R*δ^a := by
    let f := fun u : X => Cut.clip (-δ) δ (height u)
    let ψ := fun s : ℝ => ENNReal.ofReal (Cut.inside (-δ) δ s)
    let g := fun u : X => ψ (height u)
    have hmψ : Measurable ψ := ENNReal.measurable_ofReal.comp (Cut.inside_measurable _ _)
    have hf : TestLip D.distance f := by
      refine ⟨1, by norm_num, fun u v => ?_⟩
      have h := (Cut.clip_lipschitz (-δ) δ).dist_le_mul (height u) (height v)
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
      simpa [f] using h.trans (hlip u v)
    have hu : Upper D.distance f g := fun T hT γ hγ =>
      Cut.upper_along_height height hlip (by linarith : -δ ≤ δ) hT γ hγ
    have bound := pi f g hf (hborel ψ hmψ) hu x R hR
    have hg : (∫⁻ w, g (D.readout w) ∂D.law) ≤ ENNReal.ofReal (δ^(a+1)) := by
      let S := (fun w => height (D.readout w)) ⁻¹' Icc (-δ) δ
      have hs : MeasurableSet S := hmeas measurableSet_Icc
      have he : (fun w => g (D.readout w)) = S.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext w
        by_cases hw : height (D.readout w) ∈ Icc (-δ) δ <;>
          simp [S, g, ψ, Cut.inside, hw]
      rw [he, lintegral_indicator_const hs, one_mul]
      exact hband δ hd hh
    have hl (w) (hw : w ∈ left) : f (D.readout w) = -δ := by
      change height (D.readout w) ≤ -(1/2 : ℝ) at hw
      simp [f, Cut.clip, max_eq_right (show height (D.readout w) ≤ -δ by linarith),
        min_eq_left (show -δ ≤ δ by linarith)]
    have hr (w) (hw : w ∈ right) : f (D.readout w) = δ := by
      change (1/2 : ℝ) ≤ height (D.readout w) at hw
      simp [f, Cut.clip, max_eq_left (show -δ ≤ height (D.readout w) by linarith),
        min_eq_right (show δ ≤ height (D.readout w) by linarith)]
    have inner (w) (hw : w ∈ left) :
        ENNReal.ofReal (2*δ*c) ≤
          ∫⁻ v, ENNReal.ofReal |f (D.readout w) - f (D.readout v)| ∂D.law := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2*δ)]
      refine (mul_le_mul_right hright _).trans (lower_on hT _ _ ?_)
      intro v hv
      rw [hl w hw, hr v hv, abs_of_nonpos (by linarith)]
      apply ENNReal.ofReal_le_ofReal
      linarith
    have outer : ENNReal.ofReal ((2*δ*c)*c) ≤ D.average x R (fun u =>
        D.average x R (fun v => ENNReal.ofReal |f u - f v|)) := by
      simp_rw [whole_average D x R hcov]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2*δ*c)]
      exact (mul_le_mul_right hleft _).trans (lower_on hL _ _ inner)
    have dCov (w) : D.distance x (D.readout w) < Λ*R :=
      (hcov w).trans_le (le_mul_of_one_le_left hR.le hΛ)
    rw [whole_average D x (Λ*R) dCov] at bound
    have he := outer.trans (bound.trans (mul_le_mul_right hg _))
    rw [← ENNReal.ofReal_mul hCR.le] at he
    have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he
    rw [Real.rpow_add hd, Real.rpow_one] at hreal
    apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith only [hreal]
  have hc2 : 0 < 2*c*c := by positivity
  have ht : Tendsto (fun t : ℝ => C*R*t^a) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous (fun t : ℝ => C*R*t^a) :=
      continuous_const.mul (Real.continuous_rpow_const ha.le)
    simpa [ContinuousWithinAt, Real.zero_rpow ha.ne'] using
      (h.continuousAt.continuousWithinAt (s := Ioi (0:ℝ)) (x := (0:ℝ)))
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, t ≤ 1/2 :=
    (eventually_le_nhds (by norm_num : (0:ℝ)<1/2)).filter_mono nhdsWithin_le_nhds
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, 2*c*c ≤ C*R*t^a := by
    filter_upwards [self_mem_nhdsWithin, hh] with t tpos tsmall
    exact every t tpos tsmall
  exact (not_le.mpr hc2) (le_of_tendsto_of_tendsto tendsto_const_nhds ht he)

/-- The source law specified by its closed-interval probabilities. These are
exactly the integrals of (a+1)|t|^a/2 on subintervals of [-1,1]. -/
def SignedHeightLaw (D : Observation Ω X) (height : X → ℝ) (a : ℝ) : Prop :=
  ∀ l u : ℝ, -1 ≤ l → l ≤ u → u ≤ 1 →
    D.law ((fun w => height (D.readout w)) ⁻¹' Icc l u) =
      ENNReal.ofReal ((signedPower (a+1) u - signedPower (a+1) l)/2)

/-- A single explicit probability law supplies all the mass hypotheses in the
cut theorem. No inequality about a test function or its energy is an input. -/
theorem no_PI_of_signedPower_interval_law (D : Observation Ω X) [IsProbabilityMeasure D.law]
    (height : X → ℝ) (hmeas : Measurable (fun w => height (D.readout w)))
    (hlip : ∀ x y, |height x - height y| ≤ D.distance x y)
    (hborel : ∀ ψ : ℝ → ℝ≥0∞, Measurable ψ → D.borelTest (fun x => ψ (height x)))
    (x : X) {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hcov : ∀ w, D.distance x (D.readout w) < R) (law : SignedHeightLaw D height a) :
    ¬ WeakPI D := by
  let c := (1 - (1/2 : ℝ)^(a+1))/2
  have hc : 0 < c := by
    have h := Real.rpow_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2:ℝ) < 1)
      (by linarith : 0 < a+1)
    dsimp [c]
    linarith
  apply no_PI_of_thin_band D height hmeas hlip hborel x hR ha hc hcov
  · have h := law (-1) (-(1/2)) (by norm_num) (by norm_num) (by norm_num)
    have value : (signedPower (a+1) (-(1/2)) - signedPower (a+1) (-1))/2 = c := by
      norm_num [signedPower, c]
      ring
    rw [value] at h
    rw [← h]
    exact measure_mono (fun w hw => hw.2)
  · have h := law (1/2) 1 (by norm_num) (by norm_num) (by norm_num)
    have value : (signedPower (a+1) 1 - signedPower (a+1) (1/2))/2 = c := by
      norm_num [signedPower, c]
    rw [value] at h
    rw [← h]
    exact measure_mono (fun w hw => hw.1)
  · intro δ hd hh
    rw [law (-δ) δ (by linarith) (by linarith) (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    simp [signedPower, hd.le, not_le_of_gt (show -δ < 0 by linarith)]

#print axioms no_PI_of_thin_band
#print axioms no_PI_of_signedPower_interval_law
end SubLaakso.RawFailure
