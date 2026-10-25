import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Reconstruction from a tangent angle

The curve is reconstructed by integrating `(cos θ, sin θ)`.  Coordinates avoid
unnecessary vector-space conventions, while the squared speed and determinant
below are exactly the usual Euclidean quantities in an oriented plane.

The global hypotheses on `θ : ℝ → ℝ` provide a convenient smooth extension of
the angle on `[0, ℓ]`; no claim of minimal regularity is made.
-/

noncomputable section

open MeasureTheory

namespace Elastica

/-- First coordinate of the arc-length reconstruction, with initial value `x₀`. -/
def xCoord (θ : ℝ → ℝ) (x₀ s : ℝ) : ℝ :=
  x₀ + ∫ u in (0 : ℝ)..s, Real.cos (θ u)

/-- Second coordinate of the arc-length reconstruction, with initial value `y₀`. -/
def yCoord (θ : ℝ → ℝ) (y₀ s : ℝ) : ℝ :=
  y₀ + ∫ u in (0 : ℝ)..s, Real.sin (θ u)

/-- Signed curvature in the continuous real-valued angle lift. -/
def curvature (θ : ℝ → ℝ) : ℝ → ℝ := deriv θ

@[simp] theorem xCoord_zero (θ : ℝ → ℝ) (x₀ : ℝ) : xCoord θ x₀ 0 = x₀ := by
  simp [xCoord]

@[simp] theorem yCoord_zero (θ : ℝ → ℝ) (y₀ : ℝ) : yCoord θ y₀ 0 = y₀ := by
  simp [yCoord]

theorem hasDerivAt_xCoord {θ : ℝ → ℝ} (hθ : Continuous θ) (x₀ s : ℝ) :
    HasDerivAt (xCoord θ x₀) (Real.cos (θ s)) s := by
  exact (((Real.continuous_cos.comp hθ).integral_hasStrictDerivAt 0 s).hasDerivAt.const_add x₀)

theorem hasDerivAt_yCoord {θ : ℝ → ℝ} (hθ : Continuous θ) (y₀ s : ℝ) :
    HasDerivAt (yCoord θ y₀) (Real.sin (θ s)) s := by
  exact (((Real.continuous_sin.comp hθ).integral_hasStrictDerivAt 0 s).hasDerivAt.const_add y₀)

theorem deriv_xCoord {θ : ℝ → ℝ} (hθ : Continuous θ) (x₀ s : ℝ) :
    deriv (xCoord θ x₀) s = Real.cos (θ s) :=
  (hasDerivAt_xCoord hθ x₀ s).deriv

theorem deriv_yCoord {θ : ℝ → ℝ} (hθ : Continuous θ) (y₀ s : ℝ) :
    deriv (yCoord θ y₀) s = Real.sin (θ s) :=
  (hasDerivAt_yCoord hθ y₀ s).deriv

/-- The reconstructed curve has Euclidean speed one. -/
theorem unit_speed_squared {θ : ℝ → ℝ} (hθ : Continuous θ) (x₀ y₀ s : ℝ) :
    (deriv (xCoord θ x₀) s)^2 + (deriv (yCoord θ y₀) s)^2 = 1 := by
  rw [deriv_xCoord hθ, deriv_yCoord hθ]
  exact Real.cos_sq_add_sin_sq _

theorem hasDerivAt_deriv_xCoord {θ : ℝ → ℝ} (hθ : Continuous θ)
    {κ s : ℝ} (hθ' : HasDerivAt θ κ s) (x₀ : ℝ) :
    HasDerivAt (deriv (xCoord θ x₀)) (-Real.sin (θ s) * κ) s := by
  have hx : deriv (xCoord θ x₀) = fun u => Real.cos (θ u) :=
    funext (deriv_xCoord hθ x₀)
  rw [hx]
  exact hθ'.cos

theorem hasDerivAt_deriv_yCoord {θ : ℝ → ℝ} (hθ : Continuous θ)
    {κ s : ℝ} (hθ' : HasDerivAt θ κ s) (y₀ : ℝ) :
    HasDerivAt (deriv (yCoord θ y₀)) (Real.cos (θ s) * κ) s := by
  have hy : deriv (yCoord θ y₀) = fun u => Real.sin (θ u) :=
    funext (deriv_yCoord hθ y₀)
  rw [hy]
  exact hθ'.sin

/-- For the unit-speed reconstruction, `x' y'' - y' x'' = θ'`. -/
theorem signed_curvature_determinant {θ : ℝ → ℝ} (hθ : Continuous θ)
    {κ s : ℝ} (hθ' : HasDerivAt θ κ s) (x₀ y₀ : ℝ) :
    deriv (xCoord θ x₀) s * deriv (deriv (yCoord θ y₀)) s -
      deriv (yCoord θ y₀) s * deriv (deriv (xCoord θ x₀)) s = κ := by
  rw [deriv_xCoord hθ, deriv_yCoord hθ,
    (hasDerivAt_deriv_xCoord hθ hθ' x₀).deriv,
    (hasDerivAt_deriv_yCoord hθ hθ' y₀).deriv]
  calc
    _ = (Real.cos (θ s)^2 + Real.sin (θ s)^2) * κ := by ring
    _ = κ := by rw [Real.cos_sq_add_sin_sq]; simp

theorem signed_curvature_eq_deriv {θ : ℝ → ℝ} (hθ : Differentiable ℝ θ)
    (x₀ y₀ s : ℝ) :
    deriv (xCoord θ x₀) s * deriv (deriv (yCoord θ y₀)) s -
      deriv (yCoord θ y₀) s * deriv (deriv (xCoord θ x₀)) s = curvature θ s :=
  signed_curvature_determinant hθ.continuous (hθ s).hasDerivAt x₀ y₀

/-- A constant angle reconstructs a straight line. -/
theorem xCoord_const (α x₀ s : ℝ) :
    xCoord (fun _ => α) x₀ s = x₀ + s * Real.cos α := by
  simp [xCoord]

theorem yCoord_const (α y₀ s : ℝ) :
    yCoord (fun _ => α) y₀ s = y₀ + s * Real.sin α := by
  simp [yCoord]

@[simp] theorem curvature_const (α s : ℝ) : curvature (fun _ => α) s = 0 := by
  simp [curvature]

/-- The linear angle of a circular arc has the specified constant signed curvature. -/
theorem curvature_affine (α κ s : ℝ) :
    curvature (fun u => α + κ * u) s = κ := by
  simpa [curvature] using ((hasDerivAt_id s).const_mul κ |>.const_add α).deriv

/-- A nonzero affine angle reconstructs the classical circular arc. -/
theorem xCoord_affine (α κ x₀ s : ℝ) (hκ : κ ≠ 0) :
    xCoord (fun u => α + κ * u) x₀ s =
      x₀ + (Real.sin (α + κ * s) - Real.sin α) / κ := by
  have hd (u : ℝ) :
      HasDerivAt (fun v => Real.sin (α + κ * v) / κ)
        (Real.cos (α + κ * u)) u := by
    simpa [hκ] using
      (((hasDerivAt_id u).const_mul κ |>.const_add α).sin.div_const κ)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := s) (fun u _ => hd u)
    ((Real.continuous_cos.comp
      (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable 0 s)
  unfold xCoord
  rw [hi]
  simp only [mul_zero, add_zero]
  ring

theorem yCoord_affine (α κ y₀ s : ℝ) (hκ : κ ≠ 0) :
    yCoord (fun u => α + κ * u) y₀ s =
      y₀ + (Real.cos α - Real.cos (α + κ * s)) / κ := by
  have hd (u : ℝ) :
      HasDerivAt (fun v => -Real.cos (α + κ * v) / κ)
        (Real.sin (α + κ * u)) u := by
    simpa [hκ] using
      ((((hasDerivAt_id u).const_mul κ |>.const_add α).cos.neg).div_const κ)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := s) (fun u _ => hd u)
    ((Real.continuous_sin.comp
      (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable 0 s)
  unfold yCoord
  rw [hi]
  simp only [mul_zero, add_zero]
  ring

/-- A necessary endpoint condition. In particular an x-displacement greater than
the length cannot be attained, irrespective of tangent boundary conditions. -/
theorem abs_x_displacement_le (θ : ℝ → ℝ) (x₀ ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    |xCoord θ x₀ ℓ - x₀| ≤ ℓ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := ℓ) (C := (1 : ℝ))
    (f := fun u => Real.cos (θ u))
    (fun u _ => by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (θ u))
  simpa [xCoord, Real.norm_eq_abs, abs_of_nonneg hℓ] using h

theorem abs_y_displacement_le (θ : ℝ → ℝ) (y₀ ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    |yCoord θ y₀ ℓ - y₀| ≤ ℓ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := ℓ) (C := (1 : ℝ))
    (f := fun u => Real.sin (θ u))
    (fun u _ => by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (θ u))
  simpa [yCoord, Real.norm_eq_abs, abs_of_nonneg hℓ] using h

theorem impossible_x_endpoint {x₀ x₁ ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hfar : ℓ < |x₁ - x₀|) : ¬ ∃ θ : ℝ → ℝ, xCoord θ x₀ ℓ = x₁ := by
  rintro ⟨θ, hθ⟩
  have h := abs_x_displacement_le θ x₀ ℓ hℓ
  rw [hθ] at h
  exact (not_lt_of_ge h) hfar

end Elastica
