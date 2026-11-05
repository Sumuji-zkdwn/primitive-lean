import Elastica.Geometry

/-!
# A moving arc-length curve with independent rotation and time inputs

The parameter `s` is arc length along the planar curve. The parameter `t`
is time and contributes only the prescribed constant translation `v * t`.
The angle `α` is fixed independently of `t`; this file postulates no
dynamical law for either angle or translation.
-/

noncomputable section

namespace Elastica

/-- Horizontal coordinate after rotating the reconstructed curve and translating
its initial point at constant horizontal velocity. -/
def movingX (θ : ℝ → ℝ) (x₀ vₓ α s t : ℝ) : ℝ :=
  x₀ + vₓ * t + xCoord (fun u => θ u + α) 0 s

/-- Vertical coordinate after rotating the reconstructed curve and translating
its initial point at constant vertical velocity. -/
def movingY (θ : ℝ → ℝ) (y₀ vᵧ α s t : ℝ) : ℝ :=
  y₀ + vᵧ * t + yCoord (fun u => θ u + α) 0 s

/-- Moving the time input does not change the rotation angle or the arc-length
profile: the coordinate displacement is exactly velocity times elapsed time. -/
theorem movingX_time_displacement (θ : ℝ → ℝ) (x₀ vₓ α s t₀ t₁ : ℝ) :
    movingX θ x₀ vₓ α s t₁ - movingX θ x₀ vₓ α s t₀ =
      vₓ * (t₁ - t₀) := by
  unfold movingX
  ring

theorem movingY_time_displacement (θ : ℝ → ℝ) (y₀ vᵧ α s t₀ t₁ : ℝ) :
    movingY θ y₀ vᵧ α s t₁ - movingY θ y₀ vᵧ α s t₀ =
      vᵧ * (t₁ - t₀) := by
  unfold movingY
  ring

theorem hasDerivAt_movingX_arcLength {θ : ℝ → ℝ} (hθ : Continuous θ)
    (x₀ vₓ α s t : ℝ) :
    HasDerivAt (fun r => movingX θ x₀ vₓ α r t)
      (Real.cos (θ s + α)) s := by
  have h := (hasDerivAt_xCoord (hθ.add continuous_const) 0 s).const_add
    (x₀ + vₓ * t)
  simpa [movingX] using h

theorem hasDerivAt_movingY_arcLength {θ : ℝ → ℝ} (hθ : Continuous θ)
    (y₀ vᵧ α s t : ℝ) :
    HasDerivAt (fun r => movingY θ y₀ vᵧ α r t)
      (Real.sin (θ s + α)) s := by
  have h := (hasDerivAt_yCoord (hθ.add continuous_const) 0 s).const_add
    (y₀ + vᵧ * t)
  simpa [movingY] using h

/-- Rotation preserves the unit-speed property of the arc-length reconstruction. -/
theorem movingCurve_unit_speed_squared {θ : ℝ → ℝ} (hθ : Continuous θ)
    (x₀ y₀ vₓ vᵧ α s t : ℝ) :
    (deriv (fun r => movingX θ x₀ vₓ α r t) s) ^ 2 +
      (deriv (fun r => movingY θ y₀ vᵧ α r t) s) ^ 2 = 1 := by
  rw [(hasDerivAt_movingX_arcLength hθ x₀ vₓ α s t).deriv,
      (hasDerivAt_movingY_arcLength hθ y₀ vᵧ α s t).deriv]
  exact Real.cos_sq_add_sin_sq (θ s + α)

/-- The time derivative is the prescribed translation velocity, independently
of the arc-length and rotation inputs. -/
theorem hasDerivAt_movingX_time (θ : ℝ → ℝ) (x₀ vₓ α s t : ℝ) :
    HasDerivAt (fun r => movingX θ x₀ vₓ α s r) vₓ t := by
  have hlin : HasDerivAt (fun r : ℝ => vₓ * r) vₓ t :=
    (hasDerivAt_id t).const_mul vₓ
  convert hlin.const_add (x₀ + xCoord (fun u => θ u + α) 0 s) using 1 <;>
    simp only [movingX] <;> ring

theorem hasDerivAt_movingY_time (θ : ℝ → ℝ) (y₀ vᵧ α s t : ℝ) :
    HasDerivAt (fun r => movingY θ y₀ vᵧ α s r) vᵧ t := by
  have hlin : HasDerivAt (fun r : ℝ => vᵧ * r) vᵧ t :=
    (hasDerivAt_id t).const_mul vᵧ
  convert hlin.const_add (y₀ + yCoord (fun u => θ u + α) 0 s) using 1 <;>
    simp only [movingY] <;> ring

/-- Squared translation distance equals squared elapsed time exactly when the
velocity vector has unit norm. -/
theorem moving_translation_distance_eq_time_sq
    (θ : ℝ → ℝ) (x₀ y₀ vₓ vᵧ α s t₀ t₁ : ℝ)
    (hvelocity : vₓ ^ 2 + vᵧ ^ 2 = 1) :
    (movingX θ x₀ vₓ α s t₁ - movingX θ x₀ vₓ α s t₀) ^ 2 +
      (movingY θ y₀ vᵧ α s t₁ - movingY θ y₀ vᵧ α s t₀) ^ 2 =
      (t₁ - t₀) ^ 2 := by
  rw [movingX_time_displacement, movingY_time_displacement]
  nlinarith [hvelocity]

end Elastica
