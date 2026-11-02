import Elastica.MinimumConditions

/-!
Actual C¹ local minima with exact endpoint and signed-area constraints.
The definition contains neither stationarity nor a variational derivative.
-/

noncomputable section
namespace LinearInputAreaMinimum

open Real Set MeasureTheory Filter Elastica
open scoped Topology

/-- A local minimum of quadratic bending energy among C¹ angles with exactly
the same endpoint data and signed area.  The C¹ neighborhood is the original
one used by the Elastica library. -/
def LocallyMinimizing (k : ℝ) (θ : ℝ → ℝ) (ℓ : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ →
    ψ 0 = θ 0 → ψ ℓ = θ ℓ →
    (∫ s in 0..ℓ, cos (ψ s)) = (∫ s in 0..ℓ, cos (θ s)) →
    (∫ s in 0..ℓ, sin (ψ s)) = (∫ s in 0..ℓ, sin (θ s)) →
    LinearInputAreaVariation.area ψ ℓ = LinearInputAreaVariation.area θ ℓ →
    (∀ s ∈ Icc 0 ℓ,
      |ψ s - θ s| < r ∧ |deriv ψ s - deriv θ s| < r) →
    energy (fun q => k * q ^ 2 / 2) θ ℓ ≤ energy (fun q => k * q ^ 2 / 2) ψ ℓ

/-- An exact family induces a scalar local minimum from the actual C¹
comparison hypothesis.  Local minimality of the scalar path is not assumed. -/
theorem locallyMinimizing_isLocalMin_corrected_family {θ : ℝ → ℝ} {k ℓ : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hmin : LocallyMinimizing k θ ℓ)
    (η ξ₁ ξ₂ ξ₃ : variationSpace ℓ) {a b c : ℝ → ℝ}
    (ha : ContinuousAt a 0) (hb : ContinuousAt b 0) (hc : ContinuousAt c 0)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (hc0 : c 0 = 0)
    (hexact : ∀ᶠ t in 𝓝 (0 : ℝ),
      (∫ s in 0..ℓ, cos
        (θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s + c t * ξ₃.val s)) =
        (∫ s in 0..ℓ, cos (θ s)) ∧
      (∫ s in 0..ℓ, sin
        (θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s + c t * ξ₃.val s)) =
        (∫ s in 0..ℓ, sin (θ s)) ∧
      LinearInputAreaVariation.area
        (fun s => θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s + c t * ξ₃.val s) ℓ =
          LinearInputAreaVariation.area θ ℓ) :
    IsLocalMin (fun t => energy (fun q => k * q ^ 2 / 2)
      (fun s => θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s + c t * ξ₃.val s) ℓ) 0 := by
  obtain ⟨r, hr, hminimal⟩ := hmin
  have hclose := LinearInputAreaFamily.corrected_family_C1_close hθ η ξ₁ ξ₂ ξ₃
    ha hb hc ha0 hb0 hc0 hr
  change ∀ᶠ t in 𝓝 (0 : ℝ),
    energy (fun q => k * q ^ 2 / 2)
      (fun s => θ s + 0 * η.val s + a 0 * ξ₁.val s + b 0 * ξ₂.val s + c 0 * ξ₃.val s) ℓ ≤ _
  simp only [ha0, hb0, hc0, zero_mul, add_zero]
  filter_upwards [hclose, hexact] with t ht hx
  apply hminimal
    (fun s => θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s + c t * ξ₃.val s)
  · exact (((hθ.add (contDiff_const.mul η.property.1)).add
      (contDiff_const.mul ξ₁.property.1)).add
        (contDiff_const.mul ξ₂.property.1)).add (contDiff_const.mul ξ₃.property.1)
  · simp only [η.property.2.1, ξ₁.property.2.1, ξ₂.property.2.1, ξ₃.property.2.1,
      mul_zero, add_zero]
  · simp only [η.property.2.2, ξ₁.property.2.2, ξ₂.property.2.2, ξ₃.property.2.2,
      mul_zero, add_zero]
  · exact hx.1
  · exact hx.2.1
  · exact hx.2.2
  · exact ht

/-- A true C¹ local minimum with exact signed area has actual linearized
area-constrained stationarity.  Constant-curvature curves are treated directly;
all other curves use a proved three-constraint implicit-function correction. -/
theorem locallyMinimizing_areaStationary {θ : ℝ → ℝ} {k ℓ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 3 θ) (hmin : LocallyMinimizing k θ ℓ) :
    LinearInputPressureStationary.AreaStationary k θ ℓ := by
  by_cases hconst : ∃ K : ℝ, ∀ s ∈ Ioo 0 ℓ, deriv θ s = K
  · obtain ⟨K, hK⟩ := hconst
    exact LinearInputAreaRegularity.areaStationary_of_constant_curvature hℓ hθ hK
  · intro η hx hy ha
    have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
    have hx' := (hasDerivAt_horizontal_variation hℓ.le hθ.continuous
      η.property.1.continuous).deriv.symm.trans hx
    have hy' := (hasDerivAt_vertical_variation hℓ.le hθ.continuous
      η.property.1.continuous).deriv.symm.trans hy
    have ha' := (LinearInputAreaVariation.hasDerivAt_area_variation_feasible
      hℓ.le hθ.continuous η.property.1.continuous hx' hy').deriv.symm.trans ha
    obtain ⟨ξ₁, ξ₂, ξ₃, a, b, c, hca, hcb, hcc, ha0, hb0, hc0, hda, hdb, hdc, hexact⟩ :=
      LinearInputAreaExactVariation.exists_exact_area_variation hℓ hθ hconst η hx' hy' ha'
    have hm := locallyMinimizing_isLocalMin_corrected_family hθ1 hmin η ξ₁ ξ₂ ξ₃
      hca.continuousAt hcb.continuousAt hcc.continuousAt ha0 hb0 hc0 hexact
    have hd := LinearInputAreaFamily.hasDerivAt_corrected_energy_feasible (k := k) hℓ.le hθ1
      η ξ₁ ξ₂ ξ₃ hda hdb hdc ha0 hb0 hc0
    have hz := hd.deriv.symm.trans hm.deriv_eq_zero
    have he := (hasDerivAt_energy_variation hℓ.le
      (show ContDiff ℝ 1 (fun q : ℝ => k * q ^ 2 / 2) by fun_prop)
        hθ1 η.property.1).deriv
    have hquad (q : ℝ) : deriv (fun q : ℝ => k * q ^ 2 / 2) q = k * q :=
      (quadratic_density_hasDerivAt k q).deriv
    simp_rw [hquad] at he
    exact he.trans hz

/-- On a fixed nonconstant-curvature minimizer the pressure multiplier is
unique.  Its nonzero value is not asserted. -/
theorem locallyMinimizing_existsUnique_pressure {θ : ℝ → ℝ} {k ℓ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 3 θ)
    (hnonconst : ¬ ∃ K : ℝ, ∀ s ∈ Ioo 0 ℓ, deriv θ s = K)
    (hmin : LocallyMinimizing k θ ℓ) :
    ∃! p : ℝ, LinearInputPressureStationary.Stationary k p θ ℓ := by
  obtain ⟨p, hp⟩ := LinearInputPressureStationary.areaStationary_exists_pressure
    hℓ.le (hθ.of_le (by norm_num)) (locallyMinimizing_areaStationary hℓ hθ hmin)
  refine ⟨p, hp, fun q hq => ?_⟩
  exact LinearInputAreaRegularity.pressure_coefficient_unique hℓ hθ hnonconst hq hp

/-- The pressure forcing is a conclusion of exact-area constrained local
minimality, with its coefficient supplied by the multiplier theorem. -/
theorem locallyMinimizing_curvature {θ : ℝ → ℝ} {k ℓ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 3 θ) (hmin : LocallyMinimizing k θ ℓ) :
    ∃ p σ : ℝ, ∀ s ∈ Ioo 0 ℓ,
      k * deriv (deriv (deriv θ)) s + k * (deriv θ s) ^ 3 / 2 -
        σ * deriv θ s = p := by
  obtain ⟨p, hp⟩ := LinearInputPressureStationary.areaStationary_exists_pressure
    hℓ.le (hθ.of_le (by norm_num)) (locallyMinimizing_areaStationary hℓ hθ hmin)
  obtain ⟨σ, hσ⟩ := LinearInputPressureStationary.stationary_curvature hℓ hθ hp
  exact ⟨p, σ, hσ⟩

/-- The complete connection begins with a genuine exact-area constrained
local minimum, and concludes with the actual forced arclength phase curve and
its conserved quartic energy.  No stationarity or pressure is supplied. -/
theorem locallyMinimizing_phase_energy {θ : ℝ → ℝ} {k ℓ : ℝ}
    (hℓ : 0 < ℓ) (hk : 0 < k) (hθ : ContDiff ℝ 3 θ)
    (hmin : LocallyMinimizing k θ ℓ) :
    ∃ p σ c : ℝ, ∀ s ∈ Ioo 0 ℓ,
      LinearInputDesign.E (1 / 2) (-σ / k) (p / k) (deriv θ s)
        (deriv (deriv θ) s + sqrt 2 * deriv θ s) = c ∧
      HasDerivAt (deriv θ)
        (LinearInputGradient.gy (deriv θ s)
          (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s ∧
      HasDerivAt (fun t => deriv (deriv θ) t + sqrt 2 * deriv θ t)
        (-LinearInputGradient.gx (1 / 2) (-σ / k) (p / k) (deriv θ s)
          (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s := by
  exact LinearInputPressureStationary.areaStationary_phase_energy hℓ hk hθ
    (locallyMinimizing_areaStationary hℓ hθ hmin)

end LinearInputAreaMinimum
