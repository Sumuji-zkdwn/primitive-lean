/-!
# Round trip 10: loop family → similarity group → metric vs. topological invariants

Input: round 9 (the loop `γ_c`, energy density `k κ²/2`). Translation (similarity
geometry): `θ_c(s) = θ_1(c s)` is the baseline angle scaling `θ(s / a)` with `a = 1/c`.
Back-translation: the explicit segment energy `2 k c tanh(c ℓ)` agrees with the baseline
law `energy_scaling_quadratic` (energy ∝ 1/a), it stays below `2 k c`, while the total
turning `2π` is independent of `c` — a topological invariant beside a metric one.
-/

noncomputable section
namespace RoundTrip10
open Real Filter Topology RoundTrip07 RoundTrip08

/-- (Holds for every real `c`, including `c = 0` with Lean's `1/0 = 0`.) -/
theorem kink_scaling (c : ℝ) : kink c = fun s => kink 1 (s / (1 / c)) := by
  funext s
  unfold kink
  congr 2
  field_simp

/-- Curvature scaling read through the baseline `curvature_angle_scaling`. -/
theorem soliton_scaling_from_baseline (c s : ℝ) :
    soliton c s = soliton 1 (s / (1 / c)) / (1 / c) := by
  have h := Elastica.curvature_angle_scaling (θ := kink 1)
    (fun x => (hasDerivAt_kink 1 x).differentiableAt) (1 / c) s
  rw [← kink_scaling c, curvature_kink, curvature_kink] at h
  exact h

theorem hasDerivAt_energyAntideriv (k c u : ℝ) :
    HasDerivAt (fun t => 2 * k * c * (sinh (c * t) / cosh (c * t)))
      (k * soliton c u ^ 2 / 2) u := by
  have hl : HasDerivAt (fun t => c * t) c u := (hasDerivAt_id u).const_mul c |>.congr_deriv (by simp)
  have hs := (hasDerivAt_sinh (c * u)).comp u hl
  have hch := (hasDerivAt_cosh (c * u)).comp u hl
  have h := (hs.div hch (cosh_pos _).ne').const_mul (2 * k * c)
  convert h using 1
  unfold soliton
  simp only [Function.comp]
  have hc0 : cosh (c * u) ≠ 0 := (cosh_pos _).ne'
  have h1 : cosh (c * u) * c * cosh (c * u) - sinh (c * u) * (sinh (c * u) * c) = c := by
    linear_combination c * cosh_sq (c * u)
  rw [h1]
  field_simp

/-- Exact elastic energy of the loop on `[0, ℓ]`. -/
theorem energy_kink (k c ℓ : ℝ) :
    Elastica.energy (fun q => k * q ^ 2 / 2) (kink c) ℓ =
      2 * k * c * (sinh (c * ℓ) / cosh (c * ℓ)) := by
  unfold Elastica.energy
  rw [deriv_kink]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_energyAntideriv k c u)
    (by
      apply Continuous.intervalIntegrable
      exact continuous_const.mul (((contDiff_soliton c).continuous).pow 2) |>.div_const 2)]
  simp

/-- The baseline scaling law, applied to the loop family. -/
theorem energy_scaling_baseline (k : ℝ) {c : ℝ} (hc : 0 < c) (ℓ : ℝ) :
    Elastica.energy (fun q => k * q ^ 2 / 2) (kink c) (ℓ / c) =
      c * Elastica.energy (fun q => k * q ^ 2 / 2) (kink 1) ℓ := by
  have h := Elastica.energy_scaling_quadratic (θ := kink 1)
    (fun x => (hasDerivAt_kink 1 x).differentiableAt) (one_div_pos.mpr hc) k ℓ
  rw [← kink_scaling c, show 1 / c * ℓ = ℓ / c by ring] at h
  rw [h]
  field_simp

/-- Consistency of the two routes (explicit integral vs. baseline scaling theorem). -/
theorem energy_routes_agree (k : ℝ) {c : ℝ} (hc : 0 < c) (ℓ : ℝ) :
    2 * k * c * (sinh (c * (ℓ / c)) / cosh (c * (ℓ / c))) =
      c * (2 * k * 1 * (sinh (1 * ℓ) / cosh (1 * ℓ))) := by
  rw [← energy_kink, ← energy_kink, energy_scaling_baseline k hc]

/-- Metric invariant bounded by `2kc` (`k, c > 0`). -/
theorem energy_kink_lt {k c : ℝ} (hk : 0 < k) (hc : 0 < c) (ℓ : ℝ) :
    Elastica.energy (fun q => k * q ^ 2 / 2) (kink c) ℓ < 2 * k * c := by
  rw [energy_kink]
  have := (div_lt_one (cosh_pos (c * ℓ))).2 (sinh_lt_cosh (c * ℓ))
  have hkc : 0 < 2 * k * c := by positivity
  nlinarith

/-- Topological invariant: the tangent turns from `0` to `2π`, for every `c > 0`. -/
theorem kink_tendsto_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (kink c) atTop (𝓝 (2 * π)) := by
  have he : Tendsto (fun s => exp (c * s)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hc)
  have ha := (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp he
  have := ha.const_mul 4
  unfold kink
  convert this using 2
  ring

theorem kink_tendsto_atBot {c : ℝ} (hc : 0 < c) :
    Tendsto (kink c) atBot (𝓝 0) := by
  have he : Tendsto (fun s => exp (c * s)) atBot (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hc)
  have ha := ((continuous_arctan.tendsto 0).comp he).const_mul 4
  unfold kink
  simpa [arctan_zero] using ha

end RoundTrip10
