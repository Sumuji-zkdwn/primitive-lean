import Elastica.AffineEquivalence
import Elastica.ScalingMinima

/-! A three-stage composition: exponent-one response to quadratic density,
positive similarity of the constrained problem, and back to the same response.
The reference curvature is fixed. The response density is not homogeneous;
the extra terms in the energy depend only on the boundary data. -/

noncomputable section
namespace Elastica

/-- Fixed K and reference curvature still give equivalent C¹ local-minimum
problems under similarity, even though this density itself is not homogeneous. -/
theorem locallyMinimizing_powerLogDensity_one_scaling_iff {θ : ℝ → ℝ}
    {a ℓ κ₀ : ℝ} (ha : 0 < a) (hθ : ContDiff ℝ 1 θ)
    (K : ℝ) (hκ₀ : 0 < κ₀) :
    LocallyMinimizing (powerLogDensity 1 K κ₀) (fun s => θ (s / a)) (a * ℓ) ↔
      LocallyMinimizing (powerLogDensity 1 K κ₀) θ ℓ := by
  exact (locallyMinimizing_powerLogDensity_one_iff (contDiff_angle_scaling hθ a) K hκ₀).trans
    ((locallyMinimizing_scaling_iff_quadratic ha hθ (K / κ₀)).trans
      (locallyMinimizing_powerLogDensity_one_iff hθ K hκ₀).symm)

/-- The exact scaling law includes boundary constants. It is not the
homogeneous scaling law of the quadratic representative alone. -/
theorem energy_powerLogDensity_one_scaling {θ : ℝ → ℝ} {a κ₀ : ℝ}
    (ha : 0 < a) (hθ : ContDiff ℝ 1 θ) (K : ℝ) (hκ₀ : 0 < κ₀) (ℓ : ℝ) :
    energy (powerLogDensity 1 K κ₀) (fun s => θ (s / a)) (a * ℓ) =
      energy (powerLogDensity 1 K κ₀) θ ℓ / a +
      K * (1 / a - 1) * (θ ℓ - θ 0) + K * κ₀ / 2 * (a - 1 / a) * ℓ := by
  rw [energy_powerLogDensity_one (contDiff_angle_scaling hθ a) K hκ₀,
    energy_scaling_quadratic (hθ.differentiable one_ne_zero) ha,
    energy_powerLogDensity_one hθ K hκ₀]
  simp only [zero_div, mul_div_cancel_left₀ ℓ ha.ne']
  ring

end Elastica
