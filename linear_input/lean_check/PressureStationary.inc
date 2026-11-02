import Elastica

/-!
Area loading is imposed on the actual curve functional.  Stationarity below
uses actual parameter derivatives and the actual first derivatives of endpoint
displacements.  Neither a first-variation formula nor a curvature equation is
part of that predicate.
-/

noncomputable section
namespace LinearInputPressureStationary

open Real Set MeasureTheory Elastica

theorem contDiff_xCoord {θ : ℝ → ℝ} (hθ : Continuous θ) :
    ContDiff ℝ 1 (xCoord θ 0) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun s => (hasDerivAt_xCoord hθ 0 s).differentiableAt, ?_⟩
  have hd : deriv (xCoord θ 0) = fun s => cos (θ s) :=
    funext (deriv_xCoord hθ 0)
  rw [hd]
  exact Real.continuous_cos.comp hθ

theorem contDiff_yCoord {θ : ℝ → ℝ} (hθ : Continuous θ) :
    ContDiff ℝ 1 (yCoord θ 0) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun s => (hasDerivAt_yCoord hθ 0 s).differentiableAt, ?_⟩
  have hd : deriv (yCoord θ 0) = fun s => sin (θ s) :=
    funext (deriv_yCoord hθ 0)
  rw [hd]
  exact Real.continuous_sin.comp hθ

/-- The spatial weight in the actual area variation is C¹. -/
theorem contDiff_area_weight {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) :
    ContDiff ℝ 1 (fun s =>
      xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) :=
  ((contDiff_xCoord hθ.continuous).mul hθ.cos).add
    ((contDiff_yCoord hθ.continuous).mul hθ.sin)

/-- Two endpoint constraints give two force multipliers even with a spatial
loading term.  This is the finite-codimensional and integration-by-parts step. -/
theorem weighted_angleEquation_of_stationary {θ M w : ℝ → ℝ} {ℓ p : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ) (hM : ContDiff ℝ 2 M)
    (hw : ContDiff ℝ 1 w)
    (hstat : ∀ η : variationSpace ℓ,
      (∫ s in 0..ℓ, -sin (θ s) * η.val s) = 0 →
      (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0 →
      (∫ s in 0..ℓ, M s * deriv η.val s) +
        p * (∫ s in 0..ℓ, w s * η.val s) = 0) :
    ∃ lam μ : ℝ, ∀ s ∈ Ioo 0 ℓ,
      deriv M s = p * w s - lam * sin (θ s) + μ * cos (θ s) := by
  obtain ⟨lam, μ, hm⟩ := exists_multipliers_of_kernel
    (firstVariationLinear ℓ M hM.continuous +
      p • constraintLinear ℓ w hw.continuous)
    (constraintLinear ℓ (fun s => -sin (θ s)) hθ.sin.continuous.neg)
    (constraintLinear ℓ (fun s => cos (θ s)) hθ.cos.continuous) hstat
  have hq : ContDiff ℝ 1 (fun s =>
      p * w s + (-lam * sin (θ s) + μ * cos (θ s))) :=
    (contDiff_const.mul hw).add
      ((contDiff_const.mul hθ.sin).add (contDiff_const.mul hθ.cos))
  have hangle := residual_zero_of_augmented_stationary hℓ hM hq (by
    intro η
    have hi : (∫ s in 0..ℓ,
        (p * w s + (-lam * sin (θ s) + μ * cos (θ s))) * η.val s) =
        p * (∫ s in 0..ℓ, w s * η.val s) +
        lam * (∫ s in 0..ℓ, -sin (θ s) * η.val s) +
        μ * (∫ s in 0..ℓ, cos (θ s) * η.val s) := by
      have hadd : (∫ s in 0..ℓ,
          (p * w s + (-lam * sin (θ s) + μ * cos (θ s))) * η.val s) =
          ∫ s in 0..ℓ, p * w s * η.val s +
            (-lam * sin (θ s) + μ * cos (θ s)) * η.val s := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      rw [hadd]
      have hi₁ : IntervalIntegrable (fun s => p * w s * η.val s) volume 0 ℓ :=
        ((continuous_const.mul hw.continuous).mul η.property.1.continuous).intervalIntegrable _ _
      have hi₂ : IntervalIntegrable
          (fun s => (-lam * sin (θ s) + μ * cos (θ s)) * η.val s) volume 0 ℓ :=
        (((continuous_const.mul hθ.sin.continuous).add
          (continuous_const.mul hθ.cos.continuous)).mul
            η.property.1.continuous).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hi₁ hi₂]
      have hp : (∫ s in 0..ℓ, p * w s * η.val s) =
          p * (∫ s in 0..ℓ, w s * η.val s) := by
        simp_rw [mul_assoc]
        exact intervalIntegral.integral_const_mul _ _
      rw [hp, force_integral hθ.continuous η]
      ring
    rw [hi]
    have hh := hm η
    change (∫ s in 0..ℓ, M s * deriv η.val s) +
      p * (∫ s in 0..ℓ, w s * η.val s) +
      lam * (∫ s in 0..ℓ, -sin (θ s) * η.val s) +
      μ * (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0 at hh
    linarith)
  refine ⟨lam, μ, fun s hs => ?_⟩
  calc
    deriv M s = p * w s + (-lam * sin (θ s) + μ * cos (θ s)) := hangle s hs
    _ = _ := by ring

/-- Bending energy plus signed area with prescribed coefficient p. -/
def pressureEnergy (k p : ℝ) (θ : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  energy (fun q => k * q ^ 2 / 2) θ ℓ +
    p * LinearInputAreaVariation.area θ ℓ

/-- Actual linearized constrained stationarity, for fixed endpoint angles and
zero first derivatives of both endpoint displacements. -/
def Stationary (k p : ℝ) (θ : ℝ → ℝ) (ℓ : ℝ) : Prop :=
  ∀ η : variationSpace ℓ,
    deriv (fun t : ℝ => ∫ s in 0..ℓ, cos (θ s + t * η.val s)) 0 = 0 →
    deriv (fun t : ℝ => ∫ s in 0..ℓ, sin (θ s + t * η.val s)) 0 = 0 →
    deriv (fun t : ℝ => pressureEnergy k p (angleVariation θ η.val t) ℓ) 0 = 0

/-- Genuine differentiation of the full functional, using the independently
proved signed-area derivative.  Feasibility removes its boundary contribution. -/
theorem hasDerivAt_pressureEnergy_variation_feasible {k p ℓ : ℝ} {θ : ℝ → ℝ}
    (hℓ : 0 ≤ ℓ) (hθ : ContDiff ℝ 1 θ) (η : variationSpace ℓ)
    (hx : (∫ s in 0..ℓ, -sin (θ s) * η.val s) = 0)
    (hy : (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0) :
    HasDerivAt (fun t => pressureEnergy k p (angleVariation θ η.val t) ℓ)
      ((∫ s in 0..ℓ, k * deriv θ s * deriv η.val s) +
        p * (∫ s in 0..ℓ,
          (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) * η.val s)) 0 := by
  have he := hasDerivAt_energy_variation hℓ
    (show ContDiff ℝ 1 (fun q : ℝ => k * q ^ 2 / 2) by fun_prop) hθ η.property.1
  have hd (q : ℝ) : deriv (fun q : ℝ => k * q ^ 2 / 2) q = k * q :=
    (quadratic_density_hasDerivAt k q).deriv
  simp_rw [hd] at he
  have ha := LinearInputAreaVariation.hasDerivAt_area_variation_feasible
    hℓ hθ.continuous η.property.1.continuous hx hy
  exact he.add (ha.const_mul p)

/-- The integral characterization is a consequence of actual derivatives. -/
theorem stationary_iff_firstVariation {k p ℓ : ℝ} {θ : ℝ → ℝ}
    (hℓ : 0 ≤ ℓ) (hθ : ContDiff ℝ 1 θ) :
    Stationary k p θ ℓ ↔
      ∀ η : variationSpace ℓ,
        (∫ s in 0..ℓ, -sin (θ s) * η.val s) = 0 →
        (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0 →
        (∫ s in 0..ℓ, k * deriv θ s * deriv η.val s) +
          p * (∫ s in 0..ℓ,
            (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) * η.val s) = 0 := by
  unfold Stationary
  constructor <;> intro h η hx hy
  · have hdx := (hasDerivAt_horizontal_variation hℓ hθ.continuous
      η.property.1.continuous).deriv
    have hdy := (hasDerivAt_vertical_variation hℓ hθ.continuous
      η.property.1.continuous).deriv
    have he := (hasDerivAt_pressureEnergy_variation_feasible
      (k := k) (p := p) hℓ hθ η hx hy).deriv
    rw [← he]
    exact h η (hdx.trans hx) (hdy.trans hy)
  · have hdx := (hasDerivAt_horizontal_variation hℓ hθ.continuous
      η.property.1.continuous).deriv
    have hdy := (hasDerivAt_vertical_variation hℓ hθ.continuous
      η.property.1.continuous).deriv
    have hx' := hdx.symm.trans hx
    have hy' := hdy.symm.trans hy
    rw [(hasDerivAt_pressureEnergy_variation_feasible
      (k := k) (p := p) hℓ hθ η hx' hy').deriv]
    exact h η hx' hy'

/-- Actual stationarity of bending energy plus signed area gives the pressure
angle equation; the formula is a conclusion, not a hypothesis. -/
theorem stationary_angleEquation {k p ℓ : ℝ} {θ : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 3 θ)
    (hstat : Stationary k p θ ℓ) :
    ∃ lam μ : ℝ, ∀ s ∈ Ioo 0 ℓ,
      deriv (fun t => k * deriv θ t) s =
        p * (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) -
          lam * sin (θ s) + μ * cos (θ s) := by
  have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  exact weighted_angleEquation_of_stationary hℓ hθ1
    (contDiff_const.mul (hθ.deriv' (n := 2))) (contDiff_area_weight hθ1)
    ((stationary_iff_firstVariation hℓ.le hθ1).mp hstat)

/-- The forcing p in the curvature equation is derived from the actual area
term in the curve functional. -/
theorem stationary_curvature {k p ℓ : ℝ} {θ : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 3 θ)
    (hstat : Stationary k p θ ℓ) :
    ∃ σ : ℝ, ∀ s ∈ Ioo 0 ℓ,
      k * deriv (deriv (deriv θ)) s + k * (deriv θ s) ^ 3 / 2 -
        σ * deriv θ s = p := by
  obtain ⟨lam, μ, hangle⟩ := stationary_angleEquation hℓ hθ hstat
  apply LinearInputPressureCurvature.pressure_angle_curvature hθ
  intro s hs
  have hd := ((hθ.deriv' (n := 2)).differentiable (by norm_num) s).hasDerivAt.const_mul k
  exact hd.congr_deriv (hd.deriv.symm.trans (hangle s hs))

/-- End-to-end pressure connection: actual constrained stationarity of a curve
functional gives the quartic phase input u=p/k and its conserved energy. -/
theorem stationary_phase_energy {k p ℓ : ℝ} {θ : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hk : 0 < k) (hθ : ContDiff ℝ 3 θ)
    (hstat : Stationary k p θ ℓ) :
    ∃ σ c : ℝ, ∀ s ∈ Ioo 0 ℓ,
      LinearInputDesign.E (1 / 2) (-σ / k) (p / k) (deriv θ s)
        (deriv (deriv θ) s + sqrt 2 * deriv θ s) = c ∧
      HasDerivAt (deriv θ)
        (LinearInputGradient.gy (deriv θ s)
          (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s ∧
      HasDerivAt (fun t => deriv (deriv θ) t + sqrt 2 * deriv θ t)
        (-LinearInputGradient.gx (1 / 2) (-σ / k) (p / k) (deriv θ s)
          (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s := by
  obtain ⟨lam, μ, hangle⟩ := stationary_angleEquation hℓ hθ hstat
  exact LinearInputPressureCurvature.pressure_angle_eq_phase_energy hk hθ hangle

/-- Actual first-order stationarity with signed area additionally constrained.
This does not assert that every first-order feasible direction is realized by
an exactly area-preserving family, or that a minimizer exists. -/
def AreaStationary (k : ℝ) (θ : ℝ → ℝ) (ℓ : ℝ) : Prop :=
  ∀ η : variationSpace ℓ,
    deriv (fun t : ℝ => ∫ s in 0..ℓ, cos (θ s + t * η.val s)) 0 = 0 →
    deriv (fun t : ℝ => ∫ s in 0..ℓ, sin (θ s + t * η.val s)) 0 = 0 →
    deriv (fun t : ℝ => LinearInputAreaVariation.area (angleVariation θ η.val t) ℓ) 0 = 0 →
    deriv (fun t : ℝ => energy (fun q => k * q ^ 2 / 2)
      (angleVariation θ η.val t) ℓ) 0 = 0

/-- The pressure coefficient can be derived as an area multiplier.  No
independence assumption is needed for this implication from stationarity. -/
theorem areaStationary_exists_pressure {k ℓ : ℝ} {θ : ℝ → ℝ}
    (hℓ : 0 ≤ ℓ) (hθ : ContDiff ℝ 1 θ)
    (hstat : AreaStationary k θ ℓ) :
    ∃ p : ℝ, Stationary k p θ ℓ := by
  let w : ℝ → ℝ := fun s =>
    xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)
  have hw : Continuous w := (contDiff_area_weight hθ).continuous
  have hM : Continuous (fun s => k * deriv θ s) :=
    continuous_const.mul hθ.continuous_deriv_one
  obtain ⟨lam, μ, p, hm⟩ := LinearInputConstraints.exists_three_multipliers_of_kernel
    (firstVariationLinear ℓ (fun s => k * deriv θ s) hM)
    (constraintLinear ℓ (fun s => -sin (θ s)) hθ.sin.continuous.neg)
    (constraintLinear ℓ (fun s => cos (θ s)) hθ.cos.continuous)
    (constraintLinear ℓ w hw) (by
      intro η hx hy ha
      have hdx := (hasDerivAt_horizontal_variation hℓ hθ.continuous
        η.property.1.continuous).deriv
      have hdy := (hasDerivAt_vertical_variation hℓ hθ.continuous
        η.property.1.continuous).deriv
      have hda := (LinearInputAreaVariation.hasDerivAt_area_variation_feasible
        hℓ hθ.continuous η.property.1.continuous hx hy).deriv
      have he := (hasDerivAt_energy_variation hℓ
        (show ContDiff ℝ 1 (fun q : ℝ => k * q ^ 2 / 2) by fun_prop)
          hθ η.property.1).deriv
      have hd (q : ℝ) : deriv (fun q : ℝ => k * q ^ 2 / 2) q = k * q :=
        (quadratic_density_hasDerivAt k q).deriv
      simp_rw [hd] at he
      change (∫ s in 0..ℓ, k * deriv θ s * deriv η.val s) = 0
      rw [← he]
      exact hstat η (hdx.trans hx) (hdy.trans hy) (hda.trans ha))
  refine ⟨p, (stationary_iff_firstVariation hℓ hθ).mpr ?_⟩
  intro η hx hy
  have hh := hm η
  change (∫ s in 0..ℓ, k * deriv θ s * deriv η.val s) +
    lam * (∫ s in 0..ℓ, -sin (θ s) * η.val s) +
    μ * (∫ s in 0..ℓ, cos (θ s) * η.val s) +
    p * (∫ s in 0..ℓ, w s * η.val s) = 0 at hh
  simpa only [hx, hy, mul_zero, add_zero] using hh

/-- The area-constrained stationary curve has a pressure multiplier and hence
the corresponding forced quartic phase energy. -/
theorem areaStationary_phase_energy {k ℓ : ℝ} {θ : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hk : 0 < k) (hθ : ContDiff ℝ 3 θ)
    (hstat : AreaStationary k θ ℓ) :
    ∃ p σ c : ℝ, ∀ s ∈ Ioo 0 ℓ,
      LinearInputDesign.E (1 / 2) (-σ / k) (p / k) (deriv θ s)
        (deriv (deriv θ) s + sqrt 2 * deriv θ s) = c ∧
      HasDerivAt (deriv θ)
        (LinearInputGradient.gy (deriv θ s)
          (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s ∧
      HasDerivAt (fun t => deriv (deriv θ) t + sqrt 2 * deriv θ t)
        (-LinearInputGradient.gx (1 / 2) (-σ / k) (p / k) (deriv θ s)
          (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s := by
  obtain ⟨p, hp⟩ := areaStationary_exists_pressure hℓ.le (hθ.of_le (by norm_num)) hstat
  obtain ⟨σ, c, hc⟩ := stationary_phase_energy hℓ hk hθ hp
  exact ⟨p, σ, c, hc⟩

end LinearInputPressureStationary
