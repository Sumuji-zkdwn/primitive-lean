import Elastica.Examples
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp

/-!
Normalized powers and the logarithm, used as an optional constitutive law on
positive curvature.  The density below is an additional choice, not a consequence
of the general elastica definition or an empirical model of perception.

All derivative statements specify the positive-curvature domain.  In particular,
the logarithmic formulas are not asserted to be globally C³ densities on ℝ,
as required by the existing global classical-equation theorem.
-/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace Elastica

/-- The normalized power family, with its logarithmic value at exponent zero.
Its mathematical domain in the theorems below is `0 < z`. -/
def powerLog (p z : ℝ) : ℝ :=
  if p = 0 then log z else (z ^ p - 1) / p

@[simp] theorem powerLog_zero (z : ℝ) : powerLog 0 z = log z := by
  simp [powerLog]

@[simp] theorem powerLog_one (p : ℝ) : powerLog p 1 = 0 := by
  by_cases hp : p = 0 <;> simp [powerLog, hp]

/-- Every exponent gives the same first-order normalization at `z = 1`. -/
theorem hasDerivAt_powerLog {p z : ℝ} (hz : 0 < z) :
    HasDerivAt (powerLog p) (z ^ (p - 1)) z := by
  by_cases hp : p = 0
  · subst p
    unfold powerLog
    simpa [Real.rpow_neg_one] using Real.hasDerivAt_log hz.ne'
  · unfold powerLog
    simp only [hp, ite_false]
    convert ((Real.hasDerivAt_rpow_const (p := p) (Or.inl hz.ne')).sub_const 1).div_const p using 1
    field_simp

theorem deriv_powerLog {p z : ℝ} (hz : 0 < z) :
    deriv (powerLog p) z = z ^ (p - 1) :=
  (hasDerivAt_powerLog hz).deriv

theorem deriv_powerLog_pos {p z : ℝ} (hz : 0 < z) :
    0 < deriv (powerLog p) z := by
  rw [deriv_powerLog hz]
  exact Real.rpow_pos_of_pos hz _

/-- The exact transported multiplication law; at exponent zero it is logarithmic
additivity. This identity is not an identification of two empirical response laws. -/
theorem powerLog_mul (p : ℝ) {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    powerLog p (z * w) = powerLog p z + powerLog p w + p * powerLog p z * powerLog p w := by
  by_cases hp : p = 0
  · subst p
    simp [powerLog, Real.log_mul hz.ne' hw.ne']
  · simp only [powerLog, hp, ite_false]
    rw [Real.mul_rpow hz.le hw.le]
    field_simp
    ring

/-- The normalized power response really tends to the logarithm as its exponent
tends to zero, including the explicitly defined value at zero. -/
theorem continuousAt_powerLog_exponent_zero {z : ℝ} (hz : 0 < z) :
    ContinuousAt (fun p => powerLog p z) 0 := by
  have hd : HasDerivAt (fun p : ℝ => z ^ p) (log z) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) z).rpow (hasDerivAt_id 0) hz
  convert hd.continuousAt_div using 1
  funext p
  by_cases hp : p = 0
  · subst p
    simp [powerLog]
  · simp [powerLog, hp]

theorem tendsto_powerLog_exponent_zero {z : ℝ} (hz : 0 < z) :
    Tendsto (fun p => powerLog p z) (𝓝 0) (𝓝 (log z)) := by
  simpa using (continuousAt_powerLog_exponent_zero hz).tendsto

/-- A potential normalized to vanish at the positive reference curvature `κ₀`.
The special exponents zero and minus one are the actual logarithmic primitives.
The density's derivative equals `K * powerLog p (κ / κ₀)` only on `κ > 0`. -/
def powerLogDensity (p K κ₀ κ : ℝ) : ℝ :=
  if p = 0 then K * (κ * log (κ / κ₀) - κ + κ₀)
  else if p = -1 then K * (κ - κ₀ - κ₀ * log (κ / κ₀))
  else K * κ₀ / p * (((κ / κ₀) ^ (p + 1) - 1) / (p + 1) - (κ / κ₀ - 1))

@[simp] theorem powerLogDensity_zero (K κ₀ κ : ℝ) :
    powerLogDensity 0 K κ₀ κ = K * (κ * log (κ / κ₀) - κ + κ₀) := by
  simp [powerLogDensity]

@[simp] theorem powerLogDensity_neg_one (K κ₀ κ : ℝ) :
    powerLogDensity (-1) K κ₀ κ = K * (κ - κ₀ - κ₀ * log (κ / κ₀)) := by
  norm_num [powerLogDensity]

theorem powerLogDensity_reference (p K : ℝ) {κ₀ : ℝ} (hκ₀ : 0 < κ₀) :
    powerLogDensity p K κ₀ κ₀ = 0 := by
  by_cases hp : p = 0
  · simp [powerLogDensity, hp, hκ₀.ne']
  · by_cases hp' : p = -1 <;> simp [powerLogDensity, hp, hp', hκ₀.ne']

private theorem hasDerivAt_log_ratio {κ₀ κ : ℝ} (hκ₀ : 0 < κ₀) (hκ : 0 < κ) :
    HasDerivAt (fun q : ℝ => log (q / κ₀)) (1 / κ) κ := by
  convert ((hasDerivAt_id κ).div_const κ₀).log (div_ne_zero hκ.ne' hκ₀.ne') using 1
  all_goals dsimp
  field_simp

/-- Actual differentiation of the displayed potential, including both exceptional
exponents.  The response formula is proved, not supplied as a hypothesis. -/
theorem hasDerivAt_powerLogDensity (p K : ℝ) {κ₀ κ : ℝ}
    (hκ₀ : 0 < κ₀) (hκ : 0 < κ) :
    HasDerivAt (powerLogDensity p K κ₀) (K * powerLog p (κ / κ₀)) κ := by
  unfold powerLogDensity
  have hz : 0 < κ / κ₀ := div_pos hκ hκ₀
  by_cases hp : p = 0
  · subst p
    simp only [powerLog_zero]
    convert ((((hasDerivAt_id κ).mul (hasDerivAt_log_ratio hκ₀ hκ)).sub
      (hasDerivAt_id κ)).add_const κ₀).const_mul K using 1
    all_goals dsimp
    field_simp; ring
  · by_cases hp' : p = -1
    · subst p
      simp only [show (-1 : ℝ) ≠ 0 by norm_num, ite_false]
      convert (((hasDerivAt_id κ).sub_const κ₀).sub
        ((hasDerivAt_log_ratio hκ₀ hκ).const_mul κ₀)).const_mul K using 1
      all_goals first | rfl | (simp only [powerLog, ite_eq_right hp, Real.rpow_neg_one, inv_div]; ring)
    · have hp1 : p + 1 ≠ 0 := by intro h; apply hp'; linarith
      simp only [hp, hp', ite_false, powerLog]
      have hd := ((((hasDerivAt_id κ).div_const κ₀).rpow_const
        (p := p + 1) (Or.inl hz.ne')).sub_const 1).div_const (p + 1)
      convert (hd.sub (((hasDerivAt_id κ).div_const κ₀).sub_const 1)).const_mul
        (K * κ₀ / p) using 1
      all_goals dsimp
      rw [show p + 1 - 1 = p by ring]
      field_simp

/-- The actual second derivative of the potential remains positive for every
real response exponent when the reference curvature and scale are positive. -/
theorem hasDerivAt_deriv_powerLogDensity (p K : ℝ) {κ₀ κ : ℝ}
    (hκ₀ : 0 < κ₀) (hκ : 0 < κ) :
    HasDerivAt (deriv (powerLogDensity p K κ₀))
      (K / κ₀ * (κ / κ₀) ^ (p - 1)) κ := by
  have he : deriv (powerLogDensity p K κ₀) =ᶠ[𝓝 κ]
      fun q => K * powerLog p (q / κ₀) := by
    filter_upwards [eventually_gt_nhds hκ] with q hq
    exact (hasDerivAt_powerLogDensity p K hκ₀ hq).deriv
  have hd := ((hasDerivAt_powerLog (p := p) (div_pos hκ hκ₀)).comp κ
    ((hasDerivAt_id κ).div_const κ₀)).const_mul K
  have hd' : HasDerivAt (fun q => K * powerLog p (q / κ₀))
      (K / κ₀ * (κ / κ₀) ^ (p - 1)) κ := by
    convert hd using 1
    all_goals first | rfl | ring
  exact hd'.congr_of_eventuallyEq he

theorem second_deriv_powerLogDensity_pos (p : ℝ) {K κ₀ κ : ℝ}
    (hK : 0 < K) (hκ₀ : 0 < κ₀) (hκ : 0 < κ) :
    0 < deriv (deriv (powerLogDensity p K κ₀)) κ := by
  rw [(hasDerivAt_deriv_powerLogDensity p K hκ₀ hκ).deriv]
  exact mul_pos (div_pos hK hκ₀) (Real.rpow_pos_of_pos (div_pos hκ hκ₀) _)

/-- Exponent one recovers a classical quadratic density plus an affine term.
This polynomial identity extends to all signed curvatures. -/
theorem powerLogDensity_one (K : ℝ) {κ₀ : ℝ} (hκ₀ : 0 < κ₀) (κ : ℝ) :
    powerLogDensity 1 K κ₀ κ = (K / κ₀) * κ ^ 2 / 2 - K * κ + K * κ₀ / 2 := by
  norm_num [powerLogDensity, Real.rpow_two]
  field_simp; ring

/-- The affine part changes the actual curve energy only by the fixed lifted
endpoint angles and length, using the existing affine-density integral theorem. -/
theorem energy_powerLogDensity_one {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ)
    (K : ℝ) {κ₀ : ℝ} (hκ₀ : 0 < κ₀) (ℓ : ℝ) :
    energy (powerLogDensity 1 K κ₀) θ ℓ =
      energy (fun q => (K / κ₀) * q ^ 2 / 2) θ ℓ -
        K * (θ ℓ - θ 0) + K * κ₀ / 2 * ℓ := by
  have he : powerLogDensity 1 K κ₀ =
      fun q => (K / κ₀) * q ^ 2 / 2 + (-K) * q + K * κ₀ / 2 := by
    funext q
    rw [powerLogDensity_one K hκ₀]
    ring
  rw [he, energy_affine_density (by fun_prop) hθ]
  ring

/-- On fixed endpoint-angle data, exponent one compares curves in exactly the
same order as the classical quadratic bending energy. -/
theorem energy_powerLogDensity_one_le_iff {θ ψ : ℝ → ℝ}
    (hθ : ContDiff ℝ 1 θ) (hψ : ContDiff ℝ 1 ψ)
    (K : ℝ) {κ₀ : ℝ} (hκ₀ : 0 < κ₀) (ℓ : ℝ)
    (h0 : θ 0 = ψ 0) (hend : θ ℓ = ψ ℓ) :
    energy (powerLogDensity 1 K κ₀) θ ℓ ≤ energy (powerLogDensity 1 K κ₀) ψ ℓ ↔
      energy (fun q => (K / κ₀) * q ^ 2 / 2) θ ℓ ≤
        energy (fun q => (K / κ₀) * q ^ 2 / 2) ψ ℓ := by
  rw [energy_powerLogDensity_one hθ K hκ₀,
    energy_powerLogDensity_one hψ K hκ₀, h0, hend]
  exact add_le_add_iff_right _ |>.trans (sub_le_sub_iff_right _)

end Elastica
