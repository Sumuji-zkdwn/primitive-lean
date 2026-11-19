import Elastica.SecondVariation
import Elastica.Stationary
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Second variation with the fixed-position constraints

The augmented energy uses the same two endpoint-displacement integrals as the
first variation. Its derivatives below are derivatives of that actual functional.
-/

noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
namespace Elastica

/-- The Lagrange augmented energy for the two endpoint displacements. -/
def augmentedEnergy (ε θ : ℝ → ℝ) (ℓ lam μ : ℝ) : ℝ :=
  energy ε θ ℓ + lam * (∫ s in 0..ℓ, cos (θ s)) + μ * (∫ s in 0..ℓ, sin (θ s))

/-- Second parameter derivative for the actual integral, without imposing that
the argument of the density is a spatial derivative. -/
theorem hasDerivAt_deriv_integral_variation {ε κ v : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 2 ε) (hκ : Continuous κ) (hv : Continuous v) :
    HasDerivAt (deriv (fun t => ∫ s in 0..ℓ, ε (κ s + t * v s)))
      (∫ s in 0..ℓ, deriv (deriv ε) (κ s) * (v s) ^ 2) 0 := by
  have hd : deriv (fun t => ∫ s in 0..ℓ, ε (κ s + t * v s)) =
      fun t => ∫ s in 0..ℓ, deriv ε (κ s + t * v s) * v s := by
    funext t
    simpa only [mul_one] using
      (hasDerivAt_weighted_integral_variation (w := fun _ => 1) hℓ
        (hε.of_le (by norm_num)) hκ hv continuous_const t).deriv
  rw [hd]
  simpa only [zero_mul, add_zero, mul_assoc, ← pow_two] using
    (hasDerivAt_weighted_integral_variation (ε := deriv ε) (w := v)
      hℓ hε.deriv' hκ hv hv 0)

/-- Differentiating a sum twice when the first derivatives exist in a neighborhood. -/
theorem hasDerivAt_deriv_add {f g : ℝ → ℝ} {f₂ g₂ x : ℝ}
    (hf : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ f t)
    (hg : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ g t)
    (hf₂ : HasDerivAt (deriv f) f₂ x) (hg₂ : HasDerivAt (deriv g) g₂ x) :
    HasDerivAt (deriv (fun t => f t + g t)) (f₂ + g₂) x := by
  apply (hf₂.add hg₂).congr_of_eventuallyEq
  filter_upwards [hf, hg] with t hft hgt
  exact deriv_add hft hgt

/-- Constant multiplication commutes with the second derivative. -/
theorem hasDerivAt_deriv_const_mul {f : ℝ → ℝ} {f₂ x : ℝ}
    (hf : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ f t)
    (hf₂ : HasDerivAt (deriv f) f₂ x) (a : ℝ) :
    HasDerivAt (deriv (fun t => a * f t)) (a * f₂) x := by
  apply (hf₂.const_mul a).congr_of_eventuallyEq
  filter_upwards [hf] with t hft
  exact deriv_const_mul a hft

/-- The actual additive second variation of the Lagrange augmented energy. -/
theorem hasDerivAt_deriv_augmentedEnergy_variation {ε θ η : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 2 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η) (lam μ : ℝ) :
    HasDerivAt (deriv (fun t => augmentedEnergy ε (angleVariation θ η t) ℓ lam μ))
      (∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η s) ^ 2 -
        (lam * cos (θ s) + μ * sin (θ s)) * (η s) ^ 2) 0 := by
  let f := fun t => energy ε (angleVariation θ η t) ℓ
  let g := fun t => ∫ s in 0..ℓ, cos (θ s + t * η s)
  let h := fun t => ∫ s in 0..ℓ, sin (θ s + t * η s)
  have hf (t : ℝ) : DifferentiableAt ℝ f t :=
    (hasDerivAt_energy_variation_at hℓ (hε.of_le (by norm_num)) hθ hη t).differentiableAt
  have hg (t : ℝ) : DifferentiableAt ℝ g t := by
    have hg' := hasDerivAt_weighted_integral_variation (ε := cos) (w := fun _ => 1)
      hℓ contDiff_cos hθ.continuous hη.continuous continuous_const t
    simpa only [mul_one] using hg'.differentiableAt
  have hh (t : ℝ) : DifferentiableAt ℝ h t := by
    have hh' := hasDerivAt_weighted_integral_variation (ε := sin) (w := fun _ => 1)
      hℓ contDiff_sin hθ.continuous hη.continuous continuous_const t
    simpa only [mul_one] using hh'.differentiableAt
  have hf₂ := hasDerivAt_deriv_energy_variation hℓ hε hθ hη
  have hg₂ : HasDerivAt (deriv g) (∫ s in 0..ℓ, -cos (θ s) * (η s)^2) 0 := by
    simpa only [Real.deriv_cos', deriv.fun_neg, Real.deriv_sin] using
      (hasDerivAt_deriv_integral_variation hℓ (ε := cos) contDiff_cos hθ.continuous hη.continuous)
  have hh₂ : HasDerivAt (deriv h) (∫ s in 0..ℓ, -sin (θ s) * (η s)^2) 0 := by
    simpa only [Real.deriv_sin, Real.deriv_cos] using
      (hasDerivAt_deriv_integral_variation hℓ (ε := sin) contDiff_sin hθ.continuous hη.continuous)
  have hsum := hasDerivAt_deriv_add
    (Filter.Eventually.of_forall (fun t => (hf t).add ((hg t).const_mul lam)))
    (Filter.Eventually.of_forall (fun t => (hh t).const_mul μ))
    (hasDerivAt_deriv_add (Filter.Eventually.of_forall hf)
      (Filter.Eventually.of_forall (fun t => (hg t).const_mul lam)) hf₂
      (hasDerivAt_deriv_const_mul (Filter.Eventually.of_forall hg) hg₂ lam))
    (hasDerivAt_deriv_const_mul (Filter.Eventually.of_forall hh) hh₂ μ)
  have hε₂ : Continuous (deriv (deriv ε)) := hε.deriv'.continuous_deriv_one
  have hi₁ : IntervalIntegrable
      (fun s => deriv (deriv ε) (deriv θ s) * (deriv η s)^2) volume 0 ℓ :=
    ((hε₂.comp hθ.continuous_deriv_one).mul (hη.continuous_deriv_one.pow 2)).intervalIntegrable 0 ℓ
  have hi₂ : IntervalIntegrable (fun s => lam * (-cos (θ s) * (η s)^2)) volume 0 ℓ :=
    (continuous_const.mul ((Real.continuous_cos.comp hθ.continuous).neg.mul
      (hη.continuous.pow 2))).intervalIntegrable 0 ℓ
  have hi₃ : IntervalIntegrable (fun s => μ * (-sin (θ s) * (η s)^2)) volume 0 ℓ :=
    (continuous_const.mul ((Real.continuous_sin.comp hθ.continuous).neg.mul
      (hη.continuous.pow 2))).intervalIntegrable 0 ℓ
  have heq : (∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η s)^2) +
      lam * (∫ s in 0..ℓ, -cos (θ s) * (η s)^2) +
      μ * (∫ s in 0..ℓ, -sin (θ s) * (η s)^2) =
      ∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η s)^2 -
        (lam * cos (θ s) + μ * sin (θ s)) * (η s)^2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hi₁ hi₂,
      ← intervalIntegral.integral_add (hi₁.add hi₂) hi₃]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp
    ring
  rw [heq] at hsum
  exact hsum

/-- Scalar second derivative form of the augmented variation theorem. -/
theorem secondVariation_augmentedEnergy {ε θ η : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 2 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η) (lam μ : ℝ) :
    deriv (deriv (fun t => augmentedEnergy ε (angleVariation θ η t) ℓ lam μ)) 0 =
      ∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η s)^2 -
        (lam * cos (θ s) + μ * sin (θ s)) * (η s)^2 :=
  (hasDerivAt_deriv_augmentedEnergy_variation hℓ hε hθ hη lam μ).deriv

/-- Local differentiation under a finite integral. The hypotheses concern the
integrand and its actual pointwise derivative, not the integral derivative. -/
theorem hasDerivAt_integral_of_continuousOn_rectangle
    {F D : ℝ → ℝ → ℝ} {ℓ r t₀ : ℝ} (hℓ : 0 ≤ ℓ)
    (ht₀ : t₀ ∈ Ioo (-r) r)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc (-r) r ×ˢ Icc 0 ℓ))
    (hD : ContinuousOn (fun p : ℝ × ℝ => D p.1 p.2) (Icc (-r) r ×ˢ Icc 0 ℓ))
    (hd : ∀ t ∈ Ioo (-r) r, ∀ s ∈ Icc 0 ℓ, HasDerivAt (fun u => F u s) (D t s) t) :
    HasDerivAt (fun t => ∫ s in 0..ℓ, F t s) (∫ s in 0..ℓ, D t₀ s) t₀ := by
  have hint (t : ℝ) (ht : t ∈ Icc (-r) r) : IntervalIntegrable (F t) volume 0 ℓ := by
    apply ContinuousOn.intervalIntegrable_of_Icc hℓ
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨ht, hs⟩)
  have hdint (t : ℝ) (ht : t ∈ Icc (-r) r) : IntervalIntegrable (D t) volume 0 ℓ := by
    apply ContinuousOn.intervalIntegrable_of_Icc hℓ
    exact hD.comp (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨ht, hs⟩)
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc : IsCompact (Icc (-r) r)).prod
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) ℓ))).exists_bound_of_continuousOn hD
  have hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) (volume.restrict (Ioc 0 ℓ)) := by
    filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2] with t ht
    exact (hint t ⟨ht.1.le, ht.2.le⟩).1.aestronglyMeasurable
  have hbound : ∀ᵐ s ∂volume.restrict (Ioc 0 ℓ),
      ∀ t ∈ Ioo (-r) r, ‖D t s‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro t ht
    exact hC (t, s) ⟨⟨ht.1.le, ht.2.le⟩, ⟨hs.1.le, hs.2⟩⟩
  have hdiff : ∀ᵐ s ∂volume.restrict (Ioc 0 ℓ), ∀ t ∈ Ioo (-r) r,
      HasDerivAt (fun u => F u s) (D t s) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact fun t ht => hd t ht s ⟨hs.1.le, hs.2⟩
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds ht₀.1 ht₀.2) hmeas (hint t₀ ⟨ht₀.1.le, ht₀.2.le⟩).1
    (hdint t₀ ⟨ht₀.1.le, ht₀.2.le⟩).1.aestronglyMeasurable hbound (integrable_const C) hdiff
  simpa only [intervalIntegral.integral_of_le hℓ] using h.2

/-- Local second differentiation under the actual integral. -/
theorem hasDerivAt_deriv_integral_of_continuousOn_rectangle
    {F D D₂ : ℝ → ℝ → ℝ} {ℓ r : ℝ} (hℓ : 0 ≤ ℓ) (hr : 0 < r)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc (-r) r ×ˢ Icc 0 ℓ))
    (hD : ContinuousOn (fun p : ℝ × ℝ => D p.1 p.2) (Icc (-r) r ×ˢ Icc 0 ℓ))
    (hD₂ : ContinuousOn (fun p : ℝ × ℝ => D₂ p.1 p.2) (Icc (-r) r ×ˢ Icc 0 ℓ))
    (hd : ∀ t ∈ Ioo (-r) r, ∀ s ∈ Icc 0 ℓ, HasDerivAt (fun u => F u s) (D t s) t)
    (hd₂ : ∀ t ∈ Ioo (-r) r, ∀ s ∈ Icc 0 ℓ, HasDerivAt (fun u => D u s) (D₂ t s) t) :
    HasDerivAt (deriv (fun t => ∫ s in 0..ℓ, F t s)) (∫ s in 0..ℓ, D₂ 0 s) 0 := by
  have ht : (0 : ℝ) ∈ Ioo (-r) r := ⟨by linarith, hr⟩
  apply (hasDerivAt_integral_of_continuousOn_rectangle hℓ ht hD hD₂ hd₂).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t ht'
  exact (hasDerivAt_integral_of_continuousOn_rectangle hℓ ht' hF hD hd).deriv

/-- Chain and product rules under the integral, with actual pointwise time jets. -/
theorem hasDerivAt_deriv_density_integral
    {ε : ℝ → ℝ} {K V A : ℝ → ℝ → ℝ} {ℓ r : ℝ}
    (hℓ : 0 ≤ ℓ) (hr : 0 < r) (hε : ContDiff ℝ 2 ε)
    (hK : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Icc (-r) r ×ˢ Icc 0 ℓ))
    (hV : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) (Icc (-r) r ×ˢ Icc 0 ℓ))
    (hA : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (Icc (-r) r ×ˢ Icc 0 ℓ))
    (hKV : ∀ t ∈ Ioo (-r) r, ∀ s ∈ Icc 0 ℓ, HasDerivAt (fun u => K u s) (V t s) t)
    (hVA : ∀ t ∈ Ioo (-r) r, ∀ s ∈ Icc 0 ℓ, HasDerivAt (fun u => V u s) (A t s) t) :
    HasDerivAt (deriv (fun t => ∫ s in 0..ℓ, ε (K t s)))
      (∫ s in 0..ℓ, deriv (deriv ε) (K 0 s) * (V 0 s)^2 + deriv ε (K 0 s) * A 0 s) 0 := by
  have hε₁ : Continuous (deriv ε) := hε.continuous_deriv (by norm_num)
  have hε₂ : Continuous (deriv (deriv ε)) := hε.deriv'.continuous_deriv_one
  refine hasDerivAt_deriv_integral_of_continuousOn_rectangle
    (F := fun t s => ε (K t s)) (D := fun t s => deriv ε (K t s) * V t s)
    (D₂ := fun t s => deriv (deriv ε) (K t s) * (V t s)^2 + deriv ε (K t s) * A t s) hℓ hr
    (hε.continuous.comp_continuousOn hK)
    ((hε₁.comp_continuousOn hK).mul hV)
    (((hε₂.comp_continuousOn hK).mul (hV.pow 2)).add
      ((hε₁.comp_continuousOn hK).mul hA)) ?_ ?_
  · intro t ht s hs
    exact ((hε.differentiable (by norm_num)) (K t s)).hasDerivAt.comp t (hKV t ht s hs)
  · intro t ht s hs
    convert (((hε.deriv'.differentiable one_ne_zero) (K t s)).hasDerivAt.comp t
      (hKV t ht s hs)).mul (hVA t ht s hs) using 1
    all_goals first | rfl | (simp only [Function.comp_apply]; ring)

/-- Local C² correction coefficients have a common compact time neighborhood
on which their first two derivatives are continuous and their jets exist. -/
theorem exists_correction_radius {a b : ℝ → ℝ}
    (ha : ContDiffAt ℝ 2 a 0) (hb : ContDiffAt ℝ 2 b 0) :
    ∃ r > 0, ∀ t ∈ Icc (-r) r, ContDiffAt ℝ 2 a t ∧ ContDiffAt ℝ 2 b t := by
  have he := (ha.eventually (by norm_num)).and (hb.eventually (by norm_num))
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ / 2, by linarith, ?_⟩
  intro t ht
  apply hsub
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- Exact second derivative of a locally C² corrected integral family. The
acceleration terms are derived, not discarded or assumed to vanish. -/
theorem hasDerivAt_corrected_integral_and_deriv
    {ε κ v u w a b : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 2 ε)
    (hκ : Continuous κ) (hv : Continuous v) (hu : Continuous u) (hw : Continuous w)
    (ha : ContDiffAt ℝ 2 a 0) (hb : ContDiffAt ℝ 2 b 0)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (ha1 : deriv a 0 = 0) (hb1 : deriv b 0 = 0) :
    HasDerivAt (fun t => ∫ s in 0..ℓ, ε (κ s + t * v s + a t * u s + b t * w s))
      (∫ s in 0..ℓ, deriv ε (κ s) * v s) 0 ∧
    HasDerivAt (deriv (fun t => ∫ s in 0..ℓ,
      ε (κ s + t * v s + a t * u s + b t * w s)))
      (∫ s in 0..ℓ, deriv (deriv ε) (κ s) * (v s)^2 +
        deriv ε (κ s) * (deriv (deriv a) 0 * u s + deriv (deriv b) 0 * w s)) 0 := by
  obtain ⟨r, hr, hab⟩ := exists_correction_radius ha hb
  have ca : ContinuousOn a (Icc (-r) r) := fun t ht => (hab t ht).1.continuousAt.continuousWithinAt
  have cb : ContinuousOn b (Icc (-r) r) := fun t ht => (hab t ht).2.continuousAt.continuousWithinAt
  have ca1 : ContinuousOn (deriv a) (Icc (-r) r) := fun t ht =>
    ((hab t ht).1.derivWithin (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have cb1 : ContinuousOn (deriv b) (Icc (-r) r) := fun t ht =>
    ((hab t ht).2.derivWithin (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have ca2 : ContinuousOn (deriv (deriv a)) (Icc (-r) r) := fun t ht =>
    (((hab t ht).1.derivWithin (m := 1) (by norm_num)).derivWithin
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have cb2 : ContinuousOn (deriv (deriv b)) (Icc (-r) r) := fun t ht =>
    (((hab t ht).2.derivWithin (m := 1) (by norm_num)).derivWithin
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  let S := Icc (-r) r ×ˢ Icc (0 : ℝ) ℓ
  have cp {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-r) r)) :
      ContinuousOn (fun p : ℝ × ℝ => f p.1) S :=
    hf.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have cs {f : ℝ → ℝ} (hf : Continuous f) :
      ContinuousOn (fun p : ℝ × ℝ => f p.2) S := (hf.comp continuous_snd).continuousOn
  let K : ℝ → ℝ → ℝ := fun t s => κ s + t * v s + a t * u s + b t * w s
  let V : ℝ → ℝ → ℝ := fun t s => v s + deriv a t * u s + deriv b t * w s
  let A : ℝ → ℝ → ℝ := fun t s => deriv (deriv a) t * u s + deriv (deriv b) t * w s
  have hK : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) S :=
    (((cs hκ).add (continuous_fst.continuousOn.mul (cs hv))).add
      ((cp ca).mul (cs hu))).add ((cp cb).mul (cs hw))
  have hV : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) S :=
    ((cs hv).add ((cp ca1).mul (cs hu))).add ((cp cb1).mul (cs hw))
  have hA : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) S :=
    ((cp ca2).mul (cs hu)).add ((cp cb2).mul (cs hw))
  have hdK : ∀ t ∈ Ioo (-r) r, ∀ s ∈ Icc 0 ℓ, HasDerivAt (fun t => K t s) (V t s) t := by
    intro t ht s _
    have ha' := ((hab t ⟨ht.1.le, ht.2.le⟩).1.differentiableAt (by norm_num)).hasDerivAt
    have hb' := ((hab t ⟨ht.1.le, ht.2.le⟩).2.differentiableAt (by norm_num)).hasDerivAt
    convert ((((hasDerivAt_id t).mul_const (v s)).const_add (κ s)).add
      (ha'.mul_const (u s))).add (hb'.mul_const (w s)) using 1
    all_goals first | rfl | simp [V]
  have hdV : ∀ t ∈ Ioo (-r) r, ∀ s ∈ Icc 0 ℓ, HasDerivAt (fun t => V t s) (A t s) t := by
    intro t ht s _
    have ha' := (((hab t ⟨ht.1.le, ht.2.le⟩).1.derivWithin
      (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
    have hb' := (((hab t ⟨ht.1.le, ht.2.le⟩).2.derivWithin
      (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
    convert ((ha'.mul_const (u s)).const_add (v s)).add (hb'.mul_const (w s)) using 1
  constructor
  · have hf := hasDerivAt_integral_of_continuousOn_rectangle
      (F := fun t s => ε (K t s)) (D := fun t s => deriv ε (K t s) * V t s)
      hℓ (show (0 : ℝ) ∈ Ioo (-r) r from ⟨by linarith, hr⟩)
      (hε.continuous.comp_continuousOn hK)
      (((hε.continuous_deriv (by norm_num)).comp_continuousOn hK).mul hV)
      (fun t ht s hs => ((hε.differentiable (by norm_num)) (K t s)).hasDerivAt.comp t
        (hdK t ht s hs))
    simpa [K, V, ha0, hb0, ha1, hb1] using hf
  · simpa [K, V, A, ha0, hb0, ha1, hb1] using
      (hasDerivAt_deriv_density_integral hℓ hr hε hK hV hA hdK hdV)

/-- Second derivative projection of the full corrected integral calculation. -/
theorem hasDerivAt_deriv_corrected_integral
    {ε κ v u w a b : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 2 ε)
    (hκ : Continuous κ) (hv : Continuous v) (hu : Continuous u) (hw : Continuous w)
    (ha : ContDiffAt ℝ 2 a 0) (hb : ContDiffAt ℝ 2 b 0)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (ha1 : deriv a 0 = 0) (hb1 : deriv b 0 = 0) :
    HasDerivAt (deriv (fun t => ∫ s in 0..ℓ,
      ε (κ s + t * v s + a t * u s + b t * w s)))
      (∫ s in 0..ℓ, deriv (deriv ε) (κ s) * (v s)^2 +
        deriv ε (κ s) * (deriv (deriv a) 0 * u s + deriv (deriv b) 0 * w s)) 0 :=
  (hasDerivAt_corrected_integral_and_deriv hℓ hε hκ hv hu hw ha hb ha0 hb0 ha1 hb1).2

/-- Spatial differentiation of the actual corrected angle family. -/
theorem deriv_corrected_angle {θ η ξ₁ ξ₂ : ℝ → ℝ}
    (hθ : Differentiable ℝ θ) (hη : Differentiable ℝ η)
    (hξ₁ : Differentiable ℝ ξ₁) (hξ₂ : Differentiable ℝ ξ₂)
    (a b : ℝ → ℝ) (t s : ℝ) :
    deriv (fun x => θ x + t * η x + a t * ξ₁ x + b t * ξ₂ x) s =
      deriv θ s + t * deriv η s + a t * deriv ξ₁ s + b t * deriv ξ₂ s := by
  exact ((((hθ s).hasDerivAt.add ((hη s).hasDerivAt.const_mul t)).add
    ((hξ₁ s).hasDerivAt.const_mul (a t))).add ((hξ₂ s).hasDerivAt.const_mul (b t))).deriv

/-- First and second derivatives of the actual energy along a locally C²
corrected angle family. The second derivative retains its acceleration term. -/
theorem hasDerivAt_corrected_energy_and_deriv
    {ε θ η ξ₁ ξ₂ a b : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 2 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η)
    (hξ₁ : ContDiff ℝ 1 ξ₁) (hξ₂ : ContDiff ℝ 1 ξ₂)
    (ha : ContDiffAt ℝ 2 a 0) (hb : ContDiffAt ℝ 2 b 0)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (ha1 : deriv a 0 = 0) (hb1 : deriv b 0 = 0) :
    HasDerivAt (fun t => energy ε
      (fun s => θ s + t * η s + a t * ξ₁ s + b t * ξ₂ s) ℓ)
      (∫ s in 0..ℓ, deriv ε (deriv θ s) * deriv η s) 0 ∧
    HasDerivAt (deriv (fun t => energy ε
      (fun s => θ s + t * η s + a t * ξ₁ s + b t * ξ₂ s) ℓ))
      (∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η s)^2 +
        deriv ε (deriv θ s) *
          (deriv (deriv a) 0 * deriv ξ₁ s + deriv (deriv b) 0 * deriv ξ₂ s)) 0 := by
  simpa only [energy, deriv_corrected_angle (hθ.differentiable one_ne_zero)
    (hη.differentiable one_ne_zero) (hξ₁.differentiable one_ne_zero) (hξ₂.differentiable one_ne_zero)]
    using hasDerivAt_corrected_integral_and_deriv hℓ hε hθ.continuous_deriv_one
      hη.continuous_deriv_one hξ₁.continuous_deriv_one hξ₂.continuous_deriv_one
      ha hb ha0 hb0 ha1 hb1

/-- A function that is locally constant has zero actual second derivative. -/
theorem second_deriv_zero_of_eventually_const {f : ℝ → ℝ} {c x : ℝ}
    (h : f =ᶠ[𝓝 x] fun _ => c) : deriv (deriv f) x = 0 := by
  rw [h.deriv.deriv_eq]
  simp

/-- Exact endpoint constraints and augmented stationarity cancel the acceleration
of a corrected family. The remaining value is the constrained second variation. -/
theorem constrained_secondVariation_corrected
    {ε θ η a b : ℝ → ℝ} {ℓ lam μ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 2 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η)
    (ξ₁ ξ₂ : variationSpace ℓ)
    (ha : ContDiffAt ℝ 2 a 0) (hb : ContDiffAt ℝ 2 b 0)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (ha1 : deriv a 0 = 0) (hb1 : deriv b 0 = 0)
    (hx : (fun t => ∫ s in 0..ℓ,
      cos (θ s + t * η s + a t * ξ₁.val s + b t * ξ₂.val s)) =ᶠ[𝓝 0]
        fun _ => ∫ s in 0..ℓ, cos (θ s))
    (hy : (fun t => ∫ s in 0..ℓ,
      sin (θ s + t * η s + a t * ξ₁.val s + b t * ξ₂.val s)) =ᶠ[𝓝 0]
        fun _ => ∫ s in 0..ℓ, sin (θ s))
    (hstat : ∀ ζ : variationSpace ℓ,
      (∫ s in 0..ℓ, deriv ε (deriv θ s) * deriv ζ.val s) +
        lam * (∫ s in 0..ℓ, -sin (θ s) * ζ.val s) +
        μ * (∫ s in 0..ℓ, cos (θ s) * ζ.val s) = 0) :
    HasDerivAt (deriv (fun t => energy ε
      (fun s => θ s + t * η s + a t * ξ₁.val s + b t * ξ₂.val s) ℓ))
      (∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η s)^2 -
        (lam * cos (θ s) + μ * sin (θ s)) * (η s)^2) 0 := by
  let ζ : variationSpace ℓ := ⟨fun s =>
      deriv (deriv a) 0 * ξ₁.val s + deriv (deriv b) 0 * ξ₂.val s,
    ⟨(contDiff_const.mul ξ₁.property.1).add (contDiff_const.mul ξ₂.property.1),
      by simp [ξ₁.property.2.1, ξ₂.property.2.1],
      by simp [ξ₁.property.2.2, ξ₂.property.2.2]⟩⟩
  have hdζ (s : ℝ) : deriv ζ.val s =
      deriv (deriv a) 0 * deriv ξ₁.val s + deriv (deriv b) 0 * deriv ξ₂.val s :=
    (((ξ₁.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul (deriv (deriv a) 0)).add
      ((ξ₂.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul (deriv (deriv b) 0))).deriv
  have he := (hasDerivAt_corrected_energy_and_deriv hℓ hε hθ hη ξ₁.property.1 ξ₂.property.1
    ha hb ha0 hb0 ha1 hb1).2
  simp_rw [← hdζ] at he
  have hx₂ := (hasDerivAt_deriv_corrected_integral (ε := cos) hℓ contDiff_cos
    hθ.continuous hη.continuous ξ₁.property.1.continuous ξ₂.property.1.continuous
    ha hb ha0 hb0 ha1 hb1).deriv
  have hy₂ := (hasDerivAt_deriv_corrected_integral (ε := sin) hℓ contDiff_sin
    hθ.continuous hη.continuous ξ₁.property.1.continuous ξ₂.property.1.continuous
    ha hb ha0 hb0 ha1 hb1).deriv
  simp only [Real.deriv_cos', deriv.fun_neg, Real.deriv_sin] at hx₂
  simp only [Real.deriv_sin, Real.deriv_cos] at hy₂
  have hxI := hx₂.symm.trans (second_deriv_zero_of_eventually_const hx)
  have hyI := hy₂.symm.trans (second_deriv_zero_of_eventually_const hy)
  change (∫ s in 0..ℓ, -cos (θ s) * (η s)^2 + -sin (θ s) * ζ.val s) = 0 at hxI
  change (∫ s in 0..ℓ, -sin (θ s) * (η s)^2 + cos (θ s) * ζ.val s) = 0 at hyI
  have hM : Continuous (fun s => deriv ε (deriv θ s)) :=
    (hε.continuous_deriv (by norm_num)).comp hθ.continuous_deriv_one
  have hE : Continuous (fun s => deriv (deriv ε) (deriv θ s) * (deriv η s)^2) :=
    (hε.deriv'.continuous_deriv_one.comp hθ.continuous_deriv_one).mul
      (hη.continuous_deriv_one.pow 2)
  have hC : Continuous (fun s => -cos (θ s) * (η s)^2) :=
    (Real.continuous_cos.comp hθ.continuous).neg.mul (hη.continuous.pow 2)
  have hS : Continuous (fun s => -sin (θ s) * (η s)^2) :=
    (Real.continuous_sin.comp hθ.continuous).neg.mul (hη.continuous.pow 2)
  have hX : Continuous (fun s => -sin (θ s) * ζ.val s) :=
    (Real.continuous_sin.comp hθ.continuous).neg.mul ζ.property.1.continuous
  have hY : Continuous (fun s => cos (θ s) * ζ.val s) :=
    (Real.continuous_cos.comp hθ.continuous).mul ζ.property.1.continuous
  rw [intervalIntegral.integral_add (hC.intervalIntegrable 0 ℓ) (hX.intervalIntegrable 0 ℓ)] at hxI
  rw [intervalIntegral.integral_add (hS.intervalIntegrable 0 ℓ) (hY.intervalIntegrable 0 ℓ)] at hyI
  rw [intervalIntegral.integral_add
    (f := fun s => deriv (deriv ε) (deriv θ s) * (deriv η s)^2)
    (g := fun s => deriv ε (deriv θ s) * deriv ζ.val s)
    (hE.intervalIntegrable 0 ℓ)
    ((hM.mul ζ.property.1.continuous_deriv_one).intervalIntegrable 0 ℓ)] at he
  have hs := hstat ζ
  have heq : (∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η s)^2) +
      (∫ s in 0..ℓ, deriv ε (deriv θ s) * deriv ζ.val s) =
      ∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η s)^2 -
        (lam * cos (θ s) + μ * sin (θ s)) * (η s)^2 := by
    calc
      _ = (∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η s)^2) +
          lam * (∫ s in 0..ℓ, -cos (θ s) * (η s)^2) +
          μ * (∫ s in 0..ℓ, -sin (θ s) * (η s)^2) := by
        nlinarith [congrArg (fun x : ℝ => lam * x) hxI, congrArg (fun x : ℝ => μ * x) hyI]
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_add
            (f := fun s => deriv (deriv ε) (deriv θ s) * (deriv η s)^2)
            (g := fun s => lam * (-cos (θ s) * (η s)^2)) (hE.intervalIntegrable 0 ℓ)
            ((continuous_const.mul hC).intervalIntegrable 0 ℓ),
          ← intervalIntegral.integral_add
            (f := fun s => deriv (deriv ε) (deriv θ s) * (deriv η s)^2 +
              lam * (-cos (θ s) * (η s)^2))
            (g := fun s => μ * (-sin (θ s) * (η s)^2))
            ((hE.add (continuous_const.mul hC)).intervalIntegrable 0 ℓ)
            ((continuous_const.mul hS).intervalIntegrable 0 ℓ)]
        apply intervalIntegral.integral_congr
        intro s _
        dsimp
        ring
  rw [heq] at he
  exact he

end Elastica
