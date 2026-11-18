import Elastica.Geometry
import Mathlib.Tactic.Ring

/-!
# Intrinsic height carries curvature

`intrinsicHeight θ s t` is the signed displacement from the point at `s` to the
point at `t`, measured against the normal at `s` of the *same* unit-speed
Elastica curve. It is not an absolute vertical coordinate and does not add
curvature as an externally chosen correction.

The first derivative in `t` vanishes at the base point, while the second
derivative *is* the already-defined signed curvature `Elastica.curvature θ s`.
Two consecutive displacements do not add as scalar heights: the second part
must first be rotated through the intervening tangent turn.
-/

noncomputable section

namespace Elastica

/-- Longitudinal displacement in the tangent frame attached at `s`. -/
def intrinsicTangent (θ : ℝ → ℝ) (s t : ℝ) : ℝ :=
  Real.cos (θ s) * (xCoord θ 0 t - xCoord θ 0 s) +
    Real.sin (θ s) * (yCoord θ 0 t - yCoord θ 0 s)

/-- Signed normal height relative to the *moving tangent frame* at `s`. -/
def intrinsicHeight (θ : ℝ → ℝ) (s t : ℝ) : ℝ :=
  Real.cos (θ s) * (yCoord θ 0 t - yCoord θ 0 s) -
    Real.sin (θ s) * (xCoord θ 0 t - xCoord θ 0 s)

@[simp] theorem intrinsicHeight_self (θ : ℝ → ℝ) (s : ℝ) :
    intrinsicHeight θ s s = 0 := by
  simp [intrinsicHeight]

@[simp] theorem intrinsicTangent_self (θ : ℝ → ℝ) (s : ℝ) :
    intrinsicTangent θ s s = 0 := by
  simp [intrinsicTangent]

/-- Differentiate the actually integrated reconstruction. -/
theorem hasDerivAt_intrinsicHeight {θ : ℝ → ℝ} (hθ : Continuous θ)
    (s t : ℝ) :
    HasDerivAt (intrinsicHeight θ s)
      (Real.cos (θ s) * Real.sin (θ t) -
       Real.sin (θ s) * Real.cos (θ t)) t := by
  have hy : HasDerivAt (fun v => yCoord θ 0 v - yCoord θ 0 s)
      (Real.sin (θ t)) t :=
    (hasDerivAt_yCoord hθ 0 t).sub_const (yCoord θ 0 s)
  have hx : HasDerivAt (fun v => xCoord θ 0 v - xCoord θ 0 s)
      (Real.cos (θ t)) t :=
    (hasDerivAt_xCoord hθ 0 t).sub_const (xCoord θ 0 s)
  simpa only [intrinsicHeight] using
    (hy.const_mul (Real.cos (θ s))).sub (hx.const_mul (Real.sin (θ s)))

theorem deriv_intrinsicHeight {θ : ℝ → ℝ} (hθ : Continuous θ)
    (s t : ℝ) :
    deriv (intrinsicHeight θ s) t =
      Real.cos (θ s) * Real.sin (θ t) -
      Real.sin (θ s) * Real.cos (θ t) :=
  (hasDerivAt_intrinsicHeight hθ s t).deriv

/-- Every intrinsic height has zero first derivative at its own base point. -/
theorem deriv_intrinsicHeight_self {θ : ℝ → ℝ} (hθ : Continuous θ)
    (s : ℝ) : deriv (intrinsicHeight θ s) s = 0 := by
  rw [deriv_intrinsicHeight hθ s s]
  ring

/-- Signed curvature is the second derivative of intrinsic normal height
at its base point, using the existing `curvature = deriv θ`. -/
theorem intrinsicHeight_second_deriv_eq_curvature {θ : ℝ → ℝ}
    (hθ : Continuous θ) {s κ : ℝ} (hθ' : HasDerivAt θ κ s) :
    deriv (deriv (intrinsicHeight θ s)) s = κ := by
  have heq : deriv (intrinsicHeight θ s) =
      (fun t => Real.cos (θ s) * Real.sin (θ t) -
        Real.sin (θ s) * Real.cos (θ t)) :=
    funext (deriv_intrinsicHeight hθ s)
  have hd : HasDerivAt
      (fun t => Real.cos (θ s) * Real.sin (θ t) -
        Real.sin (θ s) * Real.cos (θ t))
      (Real.cos (θ s) * (Real.cos (θ s) * κ) -
        Real.sin (θ s) * (-Real.sin (θ s) * κ)) s := by
    exact ((hθ'.sin).const_mul (Real.cos (θ s))).sub
      ((hθ'.cos).const_mul (Real.sin (θ s)))
  rw [heq, hd.deriv]
  calc
    _ = (Real.cos (θ s)^2 + Real.sin (θ s)^2) * κ := by ring
    _ = κ := by rw [Real.cos_sq_add_sin_sq]; ring

/-- Curvature is recovered from intrinsic height, not added as a separate
measurement. -/
theorem curvature_from_intrinsicHeight {θ : ℝ → ℝ}
    (hθ : Differentiable ℝ θ) (s : ℝ) :
    curvature θ s = deriv (deriv (intrinsicHeight θ s)) s := by
  symm
  exact intrinsicHeight_second_deriv_eq_curvature hθ.continuous
    (hθ s).hasDerivAt

/-- Equal intrinsic-height functions at a basepoint force equal curvature. -/
theorem same_intrinsicHeight_implies_same_curvature {θ ψ : ℝ → ℝ}
    (hθ : Differentiable ℝ θ) (hψ : Differentiable ℝ ψ) (s : ℝ)
    (heq : intrinsicHeight θ s = intrinsicHeight ψ s) :
    curvature θ s = curvature ψ s := by
  rw [curvature_from_intrinsicHeight hθ,
      curvature_from_intrinsicHeight hψ, heq]

/-- At an attachment, rotate the second displacement into the first frame:
scalar intrinsic heights cannot simply be added. -/
theorem intrinsicHeight_compose (θ : ℝ → ℝ) (s t u : ℝ) :
    intrinsicHeight θ s u =
      intrinsicHeight θ s t +
        Real.sin (θ t - θ s) * intrinsicTangent θ t u +
        Real.cos (θ t - θ s) * intrinsicHeight θ t u := by
  unfold intrinsicHeight intrinsicTangent
  rw [Real.sin_sub, Real.cos_sub]
  have hunit := Real.cos_sq_add_sin_sq (θ t)
  calc
    _ = Real.cos (θ s) * (yCoord θ 0 t - yCoord θ 0 s) -
        Real.sin (θ s) * (xCoord θ 0 t - xCoord θ 0 s) +
        (Real.cos (θ t)^2 + Real.sin (θ t)^2) *
          (Real.cos (θ s) * (yCoord θ 0 u - yCoord θ 0 t) -
           Real.sin (θ s) * (xCoord θ 0 u - xCoord θ 0 t)) := by
      rw [hunit]
      ring
    _ = _ := by ring

end Elastica
