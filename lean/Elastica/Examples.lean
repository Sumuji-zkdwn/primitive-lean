import Elastica.Variation
import Elastica.Geometry

/-!
# Exact examples and symmetry checks

These statements evaluate the actual integral energy, including the fundamental
theorem of calculus in the affine-density identity. They are not merely algebraic
identities in independent symbols for the energy and curvature.
-/

noncomputable section
open MeasureTheory
namespace Elastica

/-- A constant tangent angle has zero curvature and constant energy density. -/
theorem energy_const (ε : ℝ → ℝ) (α ℓ : ℝ) :
    energy ε (fun _ => α) ℓ = ℓ * ε 0 := by
  simp [energy]

/-- An affine tangent angle has constant signed curvature, hence this exact energy. -/
theorem energy_affine (ε : ℝ → ℝ) (α c ℓ : ℝ) :
    energy ε (fun s => α + c * s) ℓ = ℓ * ε c := by
  unfold energy
  simp_rw [show ∀ s : ℝ, deriv (fun u => α + c * u) s = c from
    fun s => curvature_affine α c s]
  simp

/-- The linear curvature term integrates to the difference of the lifted end angles. -/
theorem integral_curvature {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) (ℓ : ℝ) :
    (∫ s in 0..ℓ, deriv θ s) = θ ℓ - θ 0 := by
  exact intervalIntegral.integral_deriv_eq_sub
    (fun s _ => hθ.differentiable one_ne_zero s)
    (hθ.continuous_deriv_one.intervalIntegrable 0 ℓ)

/-- Straight lines and circular arcs have zero actual first variation under
fixed-end-angle variations. This proves stationarity, not minimum energy. -/
theorem hasDerivAt_energy_affine_fixed_end_variation {ε η : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 1 ε) (hη : ContDiff ℝ 1 η)
    (h0 : η 0 = 0) (hend : η ℓ = 0) (α c : ℝ) :
    HasDerivAt
      (fun t => energy ε (angleVariation (fun s => α + c * s) η t) ℓ) 0 0 := by
  have h := hasDerivAt_energy_variation (θ := fun s => α + c * s) hℓ hε
    (contDiff_const.add (contDiff_const.mul contDiff_id)) hη
  have hi : (∫ s in 0..ℓ, deriv ε (deriv (fun u => α + c * u) s) * deriv η s) = 0 := by
    simp_rw [show ∀ s : ℝ, deriv (fun u => α + c * u) s = c from
      fun s => curvature_affine α c s]
    rw [intervalIntegral.integral_const_mul, integral_curvature hη]
    simp [h0, hend]
  simpa only [hi] using h

/-- Adding `a κ + b` to the density changes the actual energy only by boundary data. -/
theorem energy_affine_density {ε θ : ℝ → ℝ} (hε : Continuous ε)
    (hθ : ContDiff ℝ 1 θ) (a b ℓ : ℝ) :
    energy (fun q => ε q + a * q + b) θ ℓ =
      energy ε θ ℓ + a * (θ ℓ - θ 0) + b * ℓ := by
  have he : IntervalIntegrable (fun s => ε (deriv θ s)) volume 0 ℓ :=
    (hε.comp hθ.continuous_deriv_one).intervalIntegrable 0 ℓ
  have ha : IntervalIntegrable (fun s => a * deriv θ s) volume 0 ℓ :=
    (continuous_const.mul hθ.continuous_deriv_one).intervalIntegrable 0 ℓ
  unfold energy
  rw [intervalIntegral.integral_add (he.add ha) intervalIntegrable_const,
    intervalIntegral.integral_add he ha, intervalIntegral.integral_const_mul,
    integral_curvature hθ]
  simp [mul_comm]

/-- For a fixed angle branch and length, the affine-density correction is the
same for any two curves sharing both lifted endpoint angles. -/
theorem affine_density_shift_same_end_angles {ε θ ψ : ℝ → ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (hψ : ContDiff ℝ 1 ψ)
    (a b ℓ : ℝ) (h0 : θ 0 = ψ 0) (hℓ : θ ℓ = ψ ℓ) :
    energy (fun q => ε q + a * q + b) θ ℓ - energy ε θ ℓ =
      energy (fun q => ε q + a * q + b) ψ ℓ - energy ε ψ ℓ := by
  rw [energy_affine_density hε hθ, energy_affine_density hε hψ, h0, hℓ]
  ring

/-- An exact failure of reflection invariance for a density that is not even. -/
theorem reflection_counterexample :
    energy (fun q : ℝ => q) (fun s : ℝ => s) 1 = 1 ∧
    energy (fun q : ℝ => q) (fun s : ℝ => -s) 1 = -1 := by
  simp [energy]

/-- Evenness of the density is sufficient for reflection invariance of the energy. -/
theorem energy_reflection_of_even {ε : ℝ → ℝ} (hε : ∀ q, ε (-q) = ε q)
    (θ : ℝ → ℝ) (ℓ : ℝ) :
    energy ε (fun s => -θ s) ℓ = energy ε θ ℓ := by
  unfold energy
  apply intervalIntegral.integral_congr
  intro s _
  change ε (deriv (fun u => -θ u) s) = ε (deriv θ s)
  rw [show deriv (fun u => -θ u) s = -deriv θ s from deriv.neg]
  exact hε _

/-- A rigid rotation adds a constant to the angle and preserves energy for any density. -/
theorem energy_rotation (ε θ : ℝ → ℝ) (α ℓ : ℝ) :
    energy ε (fun s => θ s + α) ℓ = energy ε θ ℓ := by
  simp only [energy, deriv_add_const]

end Elastica
