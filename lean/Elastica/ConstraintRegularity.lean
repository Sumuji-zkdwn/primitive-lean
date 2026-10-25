import Elastica.Stationary
import Elastica.Reconstruction

/-! Regularity of the two endpoint-position constraints.  Nonstraightness is
expressed by a nonzero curvature at an interior point.  The weighted-square
argument proves independence, then ordinary linear duality gives two normalized
correction directions.  No rank assumption is postulated. -/

noncomputable section
open Real Set MeasureTheory
open scoped Topology
namespace Elastica

/-- A C¹ angle which is not constant on the curve has nonzero curvature somewhere
in its interior. -/
theorem exists_nonzero_curvature_of_nonconstant {θ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ)
    (hne : ¬ ∀ s ∈ Icc 0 ℓ, θ s = θ 0) :
    ∃ s ∈ Ioo 0 ℓ, deriv θ s ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  exact angle_eq_of_curvature_eq_initial (θ := fun _ => θ 0) (ψ := θ)
    hℓ contDiff_const hθ (by simpa [curvature] using h) rfl

/-- The endpoint-displacement differentials are independent on fixed-end
variations whenever the curve is not straight. -/
theorem constraint_coefficients_zero {θ : ℝ → ℝ} {ℓ a b : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ)
    (hne : ∃ s ∈ Ioo 0 ℓ, deriv θ s ≠ 0)
    (h : ∀ η : variationSpace ℓ,
      a * (∫ s in 0..ℓ, -sin (θ s) * η.val s) +
      b * (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0) : a = 0 ∧ b = 0 := by
  let q : ℝ → ℝ := fun s => -a * sin (θ s) + b * cos (θ s)
  have hq : ContDiff ℝ 1 q := (contDiff_const.mul hθ.sin).add
    (contDiff_const.mul hθ.cos)
  let η : variationSpace ℓ := ⟨fun s => s * (ℓ - s) * q s,
    ⟨(contDiff_id.mul (contDiff_const.sub contDiff_id)).mul hq, by simp, by simp⟩⟩
  have hz : (∫ s in 0..ℓ, s * (ℓ - s) * (q s) ^ 2) = 0 := by
    have hh := h η
    rw [← force_integral hθ.continuous η] at hh
    convert hh using 1
    apply intervalIntegral.integral_congr
    intro s _
    change s * (ℓ - s) * (q s) ^ 2 = q s * (s * (ℓ - s) * q s)
    ring
  have hzero := residual_zero_of_weighted_square_integral hℓ hq.continuous hz
  obtain ⟨s, hs, hκ⟩ := hne
  have heq : q =ᶠ[nhds s] fun _ => 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht using hzero t ht
  have hd0 : HasDerivAt q 0 s := (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq heq
  have hd : HasDerivAt q
      ((-a * cos (θ s) - b * sin (θ s)) * deriv θ s) s := by
    convert (((hθ.differentiable one_ne_zero s).hasDerivAt.sin.const_mul (-a)).add
      ((hθ.differentiable one_ne_zero s).hasDerivAt.cos.const_mul b)) using 1
    dsimp [q]
    ring
  have hcoef : -a * cos (θ s) - b * sin (θ s) = 0 :=
    (mul_eq_zero.mp (hd.unique hd0)).resolve_right hκ
  have hv : -a * sin (θ s) + b * cos (θ s) = 0 := hzero s hs
  have htrig := sin_sq_add_cos_sq (θ s)
  constructor
  · calc
      a = a * ((sin (θ s)) ^ 2 + (cos (θ s)) ^ 2) := by rw [htrig, mul_one]
      _ = -sin (θ s) * (-a * sin (θ s) + b * cos (θ s)) -
          cos (θ s) * (-a * cos (θ s) - b * sin (θ s)) := by ring
      _ = 0 := by rw [hv, hcoef]; ring
  · calc
      b = b * ((sin (θ s)) ^ 2 + (cos (θ s)) ^ 2) := by rw [htrig, mul_one]
      _ = cos (θ s) * (-a * sin (θ s) + b * cos (θ s)) -
          sin (θ s) * (-a * cos (θ s) - b * sin (θ s)) := by ring
      _ = 0 := by rw [hv, hcoef]; ring

/-- Two fixed-end C¹ variations can independently correct the two endpoint
coordinates.  This is the concrete rank conclusion used by the implicit
function construction. -/
theorem exists_normalized_constraint_directions {θ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ)
    (hne : ∃ s ∈ Ioo 0 ℓ, deriv θ s ≠ 0) :
    ∃ ξ₁ ξ₂ : variationSpace ℓ,
      (∫ s in 0..ℓ, -sin (θ s) * ξ₁.val s) = 1 ∧
      (∫ s in 0..ℓ, cos (θ s) * ξ₁.val s) = 0 ∧
      (∫ s in 0..ℓ, -sin (θ s) * ξ₂.val s) = 0 ∧
      (∫ s in 0..ℓ, cos (θ s) * ξ₂.val s) = 1 := by
  let cx := constraintLinear ℓ (fun s => -sin (θ s))
    (Real.continuous_sin.comp hθ.continuous).neg
  let cy := constraintLinear ℓ (fun s => cos (θ s))
    (Real.continuous_cos.comp hθ.continuous)
  let c : variationSpace ℓ →ₗ[ℝ] ℝ × ℝ := cx.prod cy
  have hev (f : (ℝ × ℝ) →ₗ[ℝ] ℝ) (x y : ℝ) :
      f (x, y) = f (1, 0) * x + f (0, 1) * y := by
    have hp : (x, y) = x • (1, 0) + y • (0, 1) := by ext <;> simp
    rw [hp, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  have ha : (LinearMap.range c).dualAnnihilator = ⊥ := by
    apply le_antisymm _ bot_le
    intro f hf
    rw [Submodule.mem_dualAnnihilator] at hf
    have hab : f (1, 0) = 0 ∧ f (0, 1) = 0 := by
      apply constraint_coefficients_zero hℓ hθ hne
      intro η
      have hfc : f (c η) = 0 := hf (c η) ⟨η, rfl⟩
      change f (cx η, cy η) = 0 at hfc
      rw [hev] at hfc
      exact hfc
    change f = 0
    apply LinearMap.ext
    intro p
    change f (p.1, p.2) = 0
    rw [hev, hab.1, hab.2]
    ring
  have hsurj : Function.Surjective c :=
    LinearMap.range_eq_top.mp (Submodule.dualAnnihilator_eq_bot_iff.mp ha)
  obtain ⟨ξ₁, h₁⟩ := hsurj (1, 0)
  obtain ⟨ξ₂, h₂⟩ := hsurj (0, 1)
  exact ⟨ξ₁, ξ₂, congrArg Prod.fst h₁, congrArg Prod.snd h₁,
    congrArg Prod.fst h₂, congrArg Prod.snd h₂⟩

end Elastica
