/-!
One choice of pressure and tension connects an actual area-constrained minimum
to its curvature equation and quartic phase energy.  The circle example checks
the hypotheses directly.  Physical-time feedback is a separate final theorem
with explicitly chosen initial data; it is not inferred from static minimality.
-/

noncomputable section
namespace LinearInputMainResult

open Real Set MeasureTheory Filter Elastica
open LinearInputDesign LinearInputGradient
open scoped Topology

/-- The same `p`, `sigma`, and `c` work throughout the entire variational-to-phase
chain.  The premise is actual local minimality; the pressure, equation, and
energy identity are conclusions.  No minimizing curve is asserted to exist. -/
theorem locallyMinimizing_pressure_curvature_phase {θ : ℝ → ℝ} {k ℓ : ℝ}
    (hℓ : 0 < ℓ) (hk : 0 < k) (hθ : ContDiff ℝ 3 θ)
    (hmin : LinearInputAreaMinimum.LocallyMinimizing k θ ℓ) :
    ∃ p σ c : ℝ,
      LinearInputPressureStationary.Stationary k p θ ℓ ∧
      ∀ s ∈ Ioo 0 ℓ,
        (k * deriv (deriv (deriv θ)) s + k * (deriv θ s) ^ 3 / 2 -
          σ * deriv θ s = p) ∧
        E (1 / 2) (-σ / k) (p / k) (deriv θ s)
          (deriv (deriv θ) s + sqrt 2 * deriv θ s) = c ∧
        HasDerivAt (deriv θ)
          (gy (deriv θ s) (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s ∧
        HasDerivAt (fun t => deriv (deriv θ) t + sqrt 2 * deriv θ t)
          (-gx (1 / 2) (-σ / k) (p / k) (deriv θ s)
            (deriv (deriv θ) s + sqrt 2 * deriv θ s)) s ∧
        (deriv (deriv θ) s) ^ 2 / 2 + (deriv θ s) ^ 4 / 8 -
          σ * (deriv θ s) ^ 2 / (2 * k) - (p / k) * deriv θ s = c := by
  have hs := LinearInputAreaMinimum.locallyMinimizing_areaStationary hℓ hθ hmin
  obtain ⟨p, hp⟩ := LinearInputPressureStationary.areaStationary_exists_pressure
    hℓ.le (hθ.of_le (by norm_num)) hs
  obtain ⟨σ, hσ⟩ := LinearInputPressureStationary.stationary_curvature hℓ hθ hp
  have hκ : ContDiff ℝ 2 (deriv θ) := hθ.deriv' (n := 2)
  have hf : ∀ s ∈ Ioo 0 ℓ,
      k * deriv (deriv (deriv θ)) s + k * (deriv θ s) ^ 3 / 2 -
        σ * deriv θ s = k * (p / k) := by
    intro s hs
    rw [hσ s hs]
    field_simp
  obtain ⟨c, hc⟩ := LinearInputCurvatureBridge.forced_energy_constant hk.ne' hκ hf
  refine ⟨p, σ, c, hp, fun s hs => ?_⟩
  obtain ⟨hx, hy⟩ := LinearInputCurvatureBridge.forced_phase_hasDerivAt hk.ne' hκ (hf s hs)
  refine ⟨hσ s hs, hc s hs, hx, hy, ?_⟩
  rw [← LinearInputCurvatureBridge.energy_shear k σ (p / k)]
  exact hc s hs

/-- The unit-curvature circle is a global comparison minimum among C1 angles
with the same lifted endpoint angles.  The square estimate proves this
directly, without any existence or stationarity assumption. -/
theorem circle_energy_minimum {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (h0 : ψ 0 = 0) (hend : ψ ℓ = ℓ) :
    energy (fun q : ℝ => q ^ 2 / 2) (fun s => s) ℓ ≤
      energy (fun q : ℝ => q ^ 2 / 2) ψ ℓ := by
  have hd := hψ.continuous_deriv_one
  have hleft : IntervalIntegrable (fun s => deriv ψ s - (1 / 2 : ℝ)) volume 0 ℓ :=
    (hd.sub continuous_const).intervalIntegrable 0 ℓ
  have hright : IntervalIntegrable (fun s => (deriv ψ s) ^ 2 / 2) volume 0 ℓ :=
    ((hd.pow 2).div_const 2).intervalIntegrable 0 ℓ
  have hi := intervalIntegral.integral_mono_on hℓ hleft hright
    (fun s _ => by nlinarith [sq_nonneg (deriv ψ s - 1)])
  rw [intervalIntegral.integral_sub (hd.intervalIntegrable 0 ℓ) intervalIntegrable_const,
    integral_curvature hψ, h0, hend] at hi
  simp [energy] at hi ⊢
  linarith

/-- Adding endpoint-position and area constraints preserves the circle's
comparison minimum.  The C1 neighborhood condition is therefore satisfied. -/
theorem circle_locallyMinimizing {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    LinearInputAreaMinimum.LocallyMinimizing 1 (fun s => s) ℓ := by
  refine ⟨1, by norm_num, ?_⟩
  intro ψ hψ h0 hend _ _ _ _
  simpa only [one_mul] using circle_energy_minimum hℓ hψ h0 hend

/-- For this constant-curvature example pressure is not unique: every p is
compatible with the endpoint-constrained first variation. -/
theorem circle_pressure_stationary {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (p : ℝ) :
    LinearInputPressureStationary.Stationary 1 p (fun s => s) ℓ := by
  apply (LinearInputPressureStationary.stationary_iff_firstVariation
    (θ := fun s : ℝ => s) hℓ contDiff_id).mpr
  intro η hx _
  have hX (s : ℝ) : xCoord (fun s => s) 0 s = sin s := by
    simpa using xCoord_affine 0 1 0 s (by norm_num)
  have hY (s : ℝ) : yCoord (fun s => s) 0 s = 1 - cos s := by
    simpa using yCoord_affine 0 1 0 s (by norm_num)
  have hw (s : ℝ) :
      xCoord (fun s => s) 0 s * cos s + yCoord (fun s => s) 0 s * sin s = sin s := by
    rw [hX, hY]
    ring
  have ha : (∫ s in 0..ℓ, sin s * η.val s) = 0 := by
    simpa only [neg_mul, intervalIntegral.integral_neg, neg_eq_zero] using hx
  simp only [deriv_id'', one_mul]
  simp_rw [hw]
  rw [integral_curvature η.property.1, η.property.2.1, η.property.2.2, ha]
  ring

/-- The circle's pressure force uses lam=p, mu=0 and its first integral is
sigma=1/2-p.  Thus p=1 and sigma=-1/2 are one consistent choice of multipliers,
not two unrelated witnesses of existence. -/
theorem circle_pressure_firstIntegral (p s : ℝ) :
    deriv (fun t => deriv (fun r : ℝ => r) t) s =
      p * (xCoord (fun r => r) 0 s * cos s + yCoord (fun r => r) 0 s * sin s) -
        p * sin s ∧
    (deriv (fun r : ℝ => r) s) ^ 2 / 2 -
      (p - p * yCoord (fun r => r) 0 s) * cos s -
      p * xCoord (fun r => r) 0 s * sin s = 1 / 2 - p := by
  have hX : xCoord (fun r => r) 0 s = sin s := by
    simpa using xCoord_affine 0 1 0 s (by norm_num)
  have hY : yCoord (fun r => r) 0 s = 1 - cos s := by
    simpa using yCoord_affine 0 1 0 s (by norm_num)
  rw [hX, hY]
  constructor
  · simp only [deriv_id'', deriv_const]
    ring
  · simp only [deriv_id'']
    nlinarith [congrArg (fun q : ℝ => p * q) (sin_sq_add_cos_sq s)]

/-- Explicit nonzero pressure example: k=1, p=1, sigma=-1/2, hence u=1.
The actual circular arc has curvature one, a stationary phase point, and
quartic energy -5/8.  The last conjunct gives the actual phase derivatives. -/
theorem circle_nonzero_input {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    LinearInputAreaMinimum.LocallyMinimizing 1 (fun s => s) ℓ ∧
    LinearInputPressureStationary.Stationary 1 1 (fun s => s) ℓ ∧
    (∀ s : ℝ,
      deriv (deriv (deriv (fun t : ℝ => t))) s +
        (deriv (fun t : ℝ => t) s) ^ 3 / 2 -
        (-1 / 2) * deriv (fun t : ℝ => t) s = 1) ∧
    E (1 / 2) (1 / 2) 1 1 (sqrt 2) = -5 / 8 ∧
    (∀ s : ℝ,
      HasDerivAt (fun _ : ℝ => (1 : ℝ)) (gy 1 (sqrt 2)) s ∧
      HasDerivAt (fun _ : ℝ => sqrt 2)
        (-gx (1 / 2) (1 / 2) 1 1 (sqrt 2)) s) := by
  refine ⟨circle_locallyMinimizing hℓ, circle_pressure_stationary hℓ 1,
    ?_, ?_, ?_⟩
  · intro s
    norm_num
  · norm_num [E, f]
  · intro s
    constructor
    · simpa [gy] using hasDerivAt_const s (1 : ℝ)
    · have hg : gx (1 / 2) (1 / 2) 1 1 (sqrt 2) = 0 := by
        unfold gx
        nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      simpa only [hg, neg_zero] using hasDerivAt_const s (sqrt 2)

/-- Exact square certificate for the same nonzero-input energy. -/
theorem example_energy_gap (x y : ℝ) :
    E (1 / 2) (1 / 2) 1 x y + 5 / 8 =
      (x - 1) ^ 2 * (x ^ 2 + 2 * x + 5) / 8 +
        (y - sqrt 2 * x) ^ 2 / 2 := by
  unfold E f
  ring

/-- All feedback initial-data identities use the very same quartic energy. -/
theorem example_initial_data :
    E (1 / 2) (1 / 2) 1 0 2 = 2 ∧
    gx (1 / 2) (1 / 2) 1 0 2 = -1 - 2 * sqrt 2 ∧
    gy 0 2 = 2 ∧
    LinearInputTrajectoryExistence.vectorField
      (1 / 2) (1 / 2) 1 1 1 (fun _ => 1) (0, 2) =
        (2 * sqrt 2 - 1, -3 - 2 * sqrt 2) := by
  refine ⟨by norm_num [E, f], ?_, by norm_num [gy], ?_⟩
  · unfold gx
    ring
  · unfold LinearInputTrajectoryExistence.vectorField E f gx gy
    apply Prod.ext <;> dsimp <;> ring

/-- Choosing physical-time feedback after the pressure parameters are fixed
gives a global injective solution above the explicit critical-energy ceiling.
The positive stiffness is supplied by the variational theorem; existence here
uses positivity of the normalized quartic coefficient, independently of its size. -/
theorem pressure_parameters_global_feedback {k p σ gamma target : ℝ}
    (_hk : 0 < k) {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (hgamma : 0 < gamma)
    (htarget : (max (σ / k) 0) ^ 2 / 6 < target)
    (z₀ : ℝ × ℝ) (hinit : target < E (1 / 2) (-σ / k) (p / k) z₀.1 z₀.2) :
    ∃ z : ℝ → ℝ × ℝ, z 0 = z₀ ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt z
        (LinearInputTrajectoryExistence.vectorField
          (1 / 2) (-σ / k) (p / k) gamma target b (z t)) t) ∧
      (∀ t : ℝ, 0 ≤ t → target < E (1 / 2) (-σ / k) (p / k) (z t).1 (z t).2) ∧
      StrictAntiOn (fun t => E (1 / 2) (-σ / k) (p / k) (z t).1 (z t).2)
        (Ici (0 : ℝ)) ∧
      InjOn z (Ici (0 : ℝ)) ∧
      Tendsto (fun t => E (1 / 2) (-σ / k) (p / k) (z t).1 (z t).2)
        atTop (𝓝 target) := by
  apply LinearInputGlobalConsequences.exists_global_injective_convergent_solution
    hb (by norm_num) hgamma ?_ z₀ hinit
  simpa only [neg_div, neg_neg, show (12 : ℝ) * (1 / 2) = 6 by norm_num] using htarget

/-- Separate chosen feedback for the same energy coefficients, with gamma=1,
target=1, b=1, and initial state (0,2).  Its initial energy is 2 and the
critical-energy ceiling is 0.  This trajectory is not the circle's arclength
phase curve, whose energy is -5/8. -/
theorem example_feedback_global :
    ∃ z : ℝ → ℝ × ℝ, z 0 = (0, 2) ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt z
        (LinearInputTrajectoryExistence.vectorField
          (1 / 2) (1 / 2) 1 1 1 (fun _ => 1) (z t)) t) ∧
      (∀ t : ℝ, 0 ≤ t → 1 < E (1 / 2) (1 / 2) 1 (z t).1 (z t).2) ∧
      StrictAntiOn (fun t => E (1 / 2) (1 / 2) 1 (z t).1 (z t).2) (Ici (0 : ℝ)) ∧
      InjOn z (Ici (0 : ℝ)) ∧
      Tendsto (fun t => E (1 / 2) (1 / 2) 1 (z t).1 (z t).2) atTop (𝓝 1) := by
  apply LinearInputGlobalConsequences.exists_global_injective_convergent_solution
    contDiff_const (by norm_num) (by norm_num) (by norm_num)
    ((0, 2) : ℝ × ℝ)
  norm_num [E, f]

end LinearInputMainResult
