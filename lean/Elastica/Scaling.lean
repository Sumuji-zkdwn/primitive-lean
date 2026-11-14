import Elastica.Geometry
import Elastica.Variation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp

/-!
# Positive similarities of reconstructed curves

For a positive scale `a`, the angle at the new arc-length parameter `s` is
`θ (s / a)`.  The results below derive its curvature, coordinates, and actual
integral energy.  Initial positions, terminal positions, and the length are all
scaled; this transports boundary data rather than preserving a single fixed
boundary-value problem.  A power law for the energy requires the separately
stated homogeneity hypothesis on the density.
-/

noncomputable section
open MeasureTheory

namespace Elastica

/-- Reparametrization by a constant scale preserves the stated smoothness. -/
theorem contDiff_angle_scaling {θ : ℝ → ℝ} {n : WithTop ℕ∞}
    (hθ : ContDiff ℝ n θ) (a : ℝ) :
    ContDiff ℝ n (fun s => θ (s / a)) :=
  hθ.comp (contDiff_id.div_const a)

/-- Chain rule for the angle at the rescaled arc-length parameter. -/
theorem hasDerivAt_angle_scaling {θ : ℝ → ℝ} {a κ s : ℝ}
    (hθ : HasDerivAt θ κ (s / a)) :
    HasDerivAt (fun t => θ (t / a)) (κ / a) s := by
  simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using
    hθ.comp s ((hasDerivAt_id s).div_const a)

theorem deriv_angle_scaling {θ : ℝ → ℝ} (hθ : Differentiable ℝ θ)
    (a s : ℝ) :
    deriv (fun t => θ (t / a)) s = deriv θ (s / a) / a :=
  (hasDerivAt_angle_scaling (hθ (s / a)).hasDerivAt).deriv

/-- Signed curvature scales by the reciprocal of a positive similarity. -/
theorem curvature_angle_scaling {θ : ℝ → ℝ} (hθ : Differentiable ℝ θ)
    (a s : ℝ) :
    curvature (fun t => θ (t / a)) s = curvature θ (s / a) / a :=
  deriv_angle_scaling hθ a s

/-- The lifted initial and terminal tangent angles are unchanged. -/
theorem angle_scaling_endpoints (θ : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (ℓ : ℝ) :
    (fun s => θ (s / a)) 0 = θ 0 ∧
      (fun s => θ (s / a)) (a * ℓ) = θ ℓ := by
  simp [ha.ne']

/-- The actual horizontal reconstruction is multiplied by the scale. -/
theorem xCoord_scaling (θ : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (x₀ s : ℝ) :
    xCoord (fun t => θ (t / a)) (a * x₀) (a * s) = a * xCoord θ x₀ s := by
  unfold xCoord
  rw [intervalIntegral.integral_comp_div (fun t => Real.cos (θ t)) ha.ne']
  simp [ha.ne', smul_eq_mul, mul_add]

/-- The actual vertical reconstruction is multiplied by the scale. -/
theorem yCoord_scaling (θ : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (y₀ s : ℝ) :
    yCoord (fun t => θ (t / a)) (a * y₀) (a * s) = a * yCoord θ y₀ s := by
  unfold yCoord
  rw [intervalIntegral.integral_comp_div (fun t => Real.sin (θ t)) ha.ne']
  simp [ha.ne', smul_eq_mul, mul_add]

/-- A C¹ curve with prescribed boundary data yields a C¹ curve for the scaled
length and positions, with exactly the same real endpoint-angle lifts. -/
theorem scaled_boundary_data {θ : ℝ → ℝ} {a ℓ x₀ y₀ x₁ y₁ α β : ℝ}
    (ha : 0 < a) (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ)
    (hx : xCoord θ x₀ ℓ = x₁) (hy : yCoord θ y₀ ℓ = y₁)
    (hα : θ 0 = α) (hβ : θ ℓ = β) :
    0 < a * ℓ ∧ ContDiff ℝ 1 (fun s => θ (s / a)) ∧
      xCoord (fun s => θ (s / a)) (a * x₀) (a * ℓ) = a * x₁ ∧
      yCoord (fun s => θ (s / a)) (a * y₀) (a * ℓ) = a * y₁ ∧
      (fun s => θ (s / a)) 0 = α ∧
      (fun s => θ (s / a)) (a * ℓ) = β := by
  refine ⟨mul_pos ha hℓ, contDiff_angle_scaling hθ a, ?_, ?_, ?_, ?_⟩
  · rw [xCoord_scaling θ ha, hx]
  · rw [yCoord_scaling θ ha, hy]
  · simpa only [zero_div] using hα
  · simpa [ha.ne'] using hβ

/-- General density transformation, obtained from the chain rule and change of
variables in the actual interval integral.  No homogeneity is assumed. -/
theorem energy_scaling {ε θ : ℝ → ℝ} (hθ : Differentiable ℝ θ)
    {a : ℝ} (ha : 0 < a) (ℓ : ℝ) :
    energy ε (fun s => θ (s / a)) (a * ℓ) =
      a * ∫ s in 0..ℓ, ε (deriv θ s / a) := by
  unfold energy
  simp_rw [deriv_angle_scaling hθ]
  simpa [ha.ne', smul_eq_mul] using
    (intervalIntegral.integral_comp_div (fun s => ε (deriv θ s / a))
      (a := 0) (b := a * ℓ) ha.ne')

/-- A density multiplier at the chosen scale induces the energy multiplier
`a * c`.  The density hypothesis is separate from the general scaling identity. -/
theorem energy_scaling_of_density_factor {ε θ : ℝ → ℝ}
    (hθ : Differentiable ℝ θ) {a c : ℝ} (ha : 0 < a)
    (hε : ∀ q, ε (q / a) = c * ε q) (ℓ : ℝ) :
    energy ε (fun s => θ (s / a)) (a * ℓ) = (a * c) * energy ε θ ℓ := by
  rw [energy_scaling hθ ha]
  simp_rw [hε]
  rw [intervalIntegral.integral_const_mul]
  simp only [energy, mul_assoc]

/-- A density homogeneous of real degree `m` under positive scaling gives the
energy law `a^(1-m)`.  Homogeneity is an additional hypothesis, not a consequence
of the general smooth-density definition. -/
theorem energy_scaling_of_homogeneous {ε θ : ℝ → ℝ}
    (hθ : Differentiable ℝ θ) {a m : ℝ} (ha : 0 < a)
    (hε : ∀ t : ℝ, 0 < t → ∀ q : ℝ, ε (t * q) = t ^ m * ε q) (ℓ : ℝ) :
    energy ε (fun s => θ (s / a)) (a * ℓ) = a ^ (1 - m) * energy ε θ ℓ := by
  have hf : ∀ q, ε (q / a) = (a⁻¹) ^ m * ε q := by
    intro q
    simpa only [div_eq_mul_inv, mul_comm q] using hε a⁻¹ (inv_pos.mpr ha) q
  rw [energy_scaling_of_density_factor hθ ha hf ℓ]
  rw [Real.inv_rpow ha.le m, Real.rpow_sub ha 1 m, Real.rpow_one]
  rfl

/-- The classical quadratic curvature density has reciprocal energy scaling.
The identity holds for every coefficient `k`; positivity is not needed here. -/
theorem energy_scaling_quadratic {θ : ℝ → ℝ} (hθ : Differentiable ℝ θ)
    {a : ℝ} (ha : 0 < a) (k ℓ : ℝ) :
    energy (fun q => k * q ^ 2 / 2) (fun s => θ (s / a)) (a * ℓ) =
      energy (fun q => k * q ^ 2 / 2) θ ℓ / a := by
  have hf : ∀ q : ℝ, k * (q / a) ^ 2 / 2 = (a⁻¹) ^ 2 * (k * q ^ 2 / 2) := by
    intro q
    simp only [div_eq_mul_inv, mul_pow]
    ring
  rw [energy_scaling_of_density_factor hθ ha hf ℓ]
  field_simp

end Elastica
