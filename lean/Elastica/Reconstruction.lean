import Elastica.Geometry
import Elastica.Variation
import Mathlib.Analysis.Calculus.MeanValue

/-!
# What signed curvature retains

For the existing arc-length reconstruction, equality of signed curvature implies
that the real tangent angles differ by one constant.  This gives the explicit
rotation-and-translation relation between the reconstructed curves.  With an
initial angle and initial point fixed, the reconstructed curve is unique.

This introduces no update operation, observation protocol, or new state model.
-/

noncomputable section
open Real Set MeasureTheory
open scoped Interval
namespace Elastica

/-- Equal signed curvature on the interior fixes the difference of tangent angles
throughout the closed interval, including both endpoints. -/
theorem angle_sub_eq_initial_of_curvature_eq {θ ψ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ) (hψ : ContDiff ℝ 1 ψ)
    (hκ : ∀ s ∈ Ioo 0 ℓ, curvature ψ s = curvature θ s) :
    ∀ s ∈ Icc 0 ℓ, ψ s - θ s = ψ 0 - θ 0 := by
  have hd : ∀ s ∈ Ioo 0 ℓ, HasDerivAt (fun t => ψ t - θ t) 0 s := by
    intro s hs
    have hk : deriv ψ s = deriv θ s := hκ s hs
    simpa only [hk, sub_self] using
      ((hψ.differentiable one_ne_zero s).hasDerivAt.sub
        (hθ.differentiable one_ne_zero s).hasDerivAt)
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo (0 : ℝ) ℓ).isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv)
  have hcc : EqOn (fun s => ψ s - θ s) (fun _ => c) (Icc 0 ℓ) := by
    have heq : EqOn (fun s => ψ s - θ s) (fun _ => c) (Ioo 0 ℓ) := hc
    simpa only [closure_Ioo hℓ.ne] using
      heq.closure (hψ.continuous.sub hθ.continuous) continuous_const
  intro s hs
  exact (hcc hs).trans (hcc ⟨le_rfl, hℓ.le⟩).symm

/-- Initial real angle plus the curvature function determines the angle lift. -/
theorem angle_eq_of_curvature_eq_initial {θ ψ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ) (hψ : ContDiff ℝ 1 ψ)
    (hκ : ∀ s ∈ Ioo 0 ℓ, curvature ψ s = curvature θ s)
    (h₀ : ψ 0 = θ 0) :
    ∀ s ∈ Icc 0 ℓ, ψ s = θ s := by
  intro s hs
  have h := angle_sub_eq_initial_of_curvature_eq hℓ hθ hψ hκ s hs
  rw [h₀, sub_self] at h
  exact sub_eq_zero.mp h

/-- The coordinate reconstruction only reads the angle on its integration interval. -/
theorem xCoord_eq_of_angle_eq {θ ψ : ℝ → ℝ} {ℓ s : ℝ}
    (h : EqOn ψ θ (Icc 0 ℓ)) (hs : s ∈ Icc 0 ℓ) (x₀ : ℝ) :
    xCoord ψ x₀ s = xCoord θ x₀ s := by
  unfold xCoord
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hs.1] at ht
  change cos (ψ t) = cos (θ t)
  rw [h ⟨ht.1, ht.2.trans hs.2⟩]

theorem yCoord_eq_of_angle_eq {θ ψ : ℝ → ℝ} {ℓ s : ℝ}
    (h : EqOn ψ θ (Icc 0 ℓ)) (hs : s ∈ Icc 0 ℓ) (y₀ : ℝ) :
    yCoord ψ y₀ s = yCoord θ y₀ s := by
  unfold yCoord
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hs.1] at ht
  change sin (ψ t) = sin (θ t)
  rw [h ⟨ht.1, ht.2.trans hs.2⟩]

/-- Fixed initial point and initial real angle remove the remaining freedom. -/
theorem reconstruction_eq_of_curvature_eq_initial {θ ψ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ) (hψ : ContDiff ℝ 1 ψ)
    (hκ : ∀ s ∈ Ioo 0 ℓ, curvature ψ s = curvature θ s)
    (h₀ : ψ 0 = θ 0) (x₀ y₀ : ℝ) :
    ∀ s ∈ Icc 0 ℓ,
      xCoord ψ x₀ s = xCoord θ x₀ s ∧ yCoord ψ y₀ s = yCoord θ y₀ s := by
  intro s hs
  have ha := angle_eq_of_curvature_eq_initial hℓ hθ hψ hκ h₀
  exact ⟨xCoord_eq_of_angle_eq ha hs x₀, yCoord_eq_of_angle_eq ha hs y₀⟩

/-- Adding a constant angle rotates the displacement through that angle. -/
theorem xCoord_add_angle {θ : ℝ → ℝ} (hθ : Continuous θ)
    (α x₀ y₀ x₁ s : ℝ) :
    xCoord (fun u => θ u + α) x₁ s - x₁ =
      cos α * (xCoord θ x₀ s - x₀) - sin α * (yCoord θ y₀ s - y₀) := by
  unfold xCoord yCoord
  simp only [add_sub_cancel_left, cos_add]
  rw [intervalIntegral.integral_sub
    (f := fun u => cos (θ u) * cos α) (g := fun u => sin (θ u) * sin α)
    (μ := volume) (a := 0) (b := s)
    (((Real.continuous_cos.comp hθ).mul continuous_const).intervalIntegrable 0 s)
    (((Real.continuous_sin.comp hθ).mul continuous_const).intervalIntegrable 0 s),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  ring

theorem yCoord_add_angle {θ : ℝ → ℝ} (hθ : Continuous θ)
    (α x₀ y₀ y₁ s : ℝ) :
    yCoord (fun u => θ u + α) y₁ s - y₁ =
      sin α * (xCoord θ x₀ s - x₀) + cos α * (yCoord θ y₀ s - y₀) := by
  unfold xCoord yCoord
  simp only [add_sub_cancel_left, sin_add]
  rw [intervalIntegral.integral_add
    (f := fun u => sin (θ u) * cos α) (g := fun u => cos (θ u) * sin α)
    (μ := volume) (a := 0) (b := s)
    (((Real.continuous_sin.comp hθ).mul continuous_const).intervalIntegrable 0 s)
    (((Real.continuous_cos.comp hθ).mul continuous_const).intervalIntegrable 0 s),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  ring

/-- Equal signed curvature gives an explicit orientation-preserving rigid motion.
Here α is exactly the difference of the two chosen initial angle lifts. -/
theorem reconstruction_rotation_of_curvature_eq {θ ψ : ℝ → ℝ} {ℓ α : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ) (hψ : ContDiff ℝ 1 ψ)
    (hκ : ∀ s ∈ Ioo 0 ℓ, curvature ψ s = curvature θ s)
    (hα : α = ψ 0 - θ 0) (x₀ y₀ x₁ y₁ : ℝ) :
    ∀ s ∈ Icc 0 ℓ,
      xCoord ψ x₁ s - x₁ =
        cos α * (xCoord θ x₀ s - x₀) - sin α * (yCoord θ y₀ s - y₀) ∧
      yCoord ψ y₁ s - y₁ =
        sin α * (xCoord θ x₀ s - x₀) + cos α * (yCoord θ y₀ s - y₀) := by
  have ha : EqOn ψ (fun s => θ s + α) (Icc 0 ℓ) := by
    intro s hs
    have h := angle_sub_eq_initial_of_curvature_eq hℓ hθ hψ hκ s hs
    rw [← hα] at h
    linarith
  intro s hs
  rw [xCoord_eq_of_angle_eq ha hs x₁, yCoord_eq_of_angle_eq ha hs y₁]
  exact ⟨xCoord_add_angle hθ.continuous α x₀ y₀ x₁ s,
    yCoord_add_angle hθ.continuous α x₀ y₀ y₁ s⟩

/-- Since the density reads only signed curvature, equal curvature gives equal energy.
No evenness, convexity, or regularity assumption on the density is needed here. -/
theorem energy_eq_of_curvature_eq {θ ψ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ) (hψ : ContDiff ℝ 1 ψ)
    (hκ : ∀ s ∈ Ioo 0 ℓ, curvature ψ s = curvature θ s) (ε : ℝ → ℝ) :
    energy ε ψ ℓ = energy ε θ ℓ := by
  have hcc : EqOn (deriv ψ) (deriv θ) (Icc 0 ℓ) := by
    have heq : EqOn (deriv ψ) (deriv θ) (Ioo 0 ℓ) := hκ
    simpa only [closure_Ioo hℓ.ne] using
      heq.closure hψ.continuous_deriv_one hθ.continuous_deriv_one
  unfold energy
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hℓ.le] at hs
  change ε (deriv ψ s) = ε (deriv θ s)
  rw [hcc hs]

end Elastica
