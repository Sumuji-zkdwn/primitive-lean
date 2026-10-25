import Elastica.Geometry
import Elastica.Variation
import Mathlib.Tactic.Linarith

/-!
# Restriction and comparison of smooth curve pieces

These results use the existing angle and energy definitions.  They compare
already C¹ angle functions and do not postulate that arbitrary pieces admit a
smooth gluing.  Exterior agreement and the two middle displacement integrals
are the explicit conditions for replacing a middle piece without changing the
boundary data.  The energy difference is then exactly the middle difference.
-/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology

namespace Elastica

/-- Three consecutive oriented interval integrals give the original integral.
In applications the cuts satisfy `0 ≤ a ≤ b ≤ ℓ`; the identity itself needs no
ordering assumption. -/
theorem integral_split_three {f : ℝ → ℝ} (hf : Continuous f) (a b ℓ : ℝ) :
    (∫ s in 0..ℓ, f s) =
      (∫ s in 0..a, f s) + (∫ s in a..b, f s) + (∫ s in b..ℓ, f s) := by
  rw [intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a b),
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 b) (hf.intervalIntegrable b ℓ)]

/-- The actual curvature energy splits into the three pieces. -/
theorem energy_split_three {ε θ : ℝ → ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (a b ℓ : ℝ) :
    energy ε θ ℓ =
      (∫ s in 0..a, ε (deriv θ s)) +
      (∫ s in a..b, ε (deriv θ s)) +
      (∫ s in b..ℓ, ε (deriv θ s)) :=
  integral_split_three (hε.comp hθ.continuous_deriv_one) a b ℓ

/-- The horizontal displacement of any subarc is its tangent integral. -/
theorem xCoord_sub_eq_integral {θ : ℝ → ℝ} (hθ : Continuous θ)
    (x₀ a b : ℝ) :
    xCoord θ x₀ b - xCoord θ x₀ a = ∫ s in a..b, cos (θ s) := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (f := fun s => cos (θ s))
    ((continuous_cos.comp hθ).intervalIntegrable 0 a)
    ((continuous_cos.comp hθ).intervalIntegrable a b)
  unfold xCoord
  linarith

/-- The vertical displacement of any subarc is its tangent integral. -/
theorem yCoord_sub_eq_integral {θ : ℝ → ℝ} (hθ : Continuous θ)
    (y₀ a b : ℝ) :
    yCoord θ y₀ b - yCoord θ y₀ a = ∫ s in a..b, sin (θ s) := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (f := fun s => sin (θ s))
    ((continuous_sin.comp hθ).intervalIntegrable 0 a)
    ((continuous_sin.comp hθ).intervalIntegrable a b)
  unfold yCoord
  linarith

/-- Position reconstruction splits at exactly the same cut locations as energy. -/
theorem xCoord_split_three {θ : ℝ → ℝ} (hθ : Continuous θ) (x₀ a b ℓ : ℝ) :
    xCoord θ x₀ ℓ = x₀ +
      ((∫ s in 0..a, cos (θ s)) + (∫ s in a..b, cos (θ s)) +
        (∫ s in b..ℓ, cos (θ s))) := by
  unfold xCoord
  exact congrArg (fun z : ℝ => x₀ + z)
    (integral_split_three (f := fun s => cos (θ s)) (continuous_cos.comp hθ) a b ℓ)

theorem yCoord_split_three {θ : ℝ → ℝ} (hθ : Continuous θ) (y₀ a b ℓ : ℝ) :
    yCoord θ y₀ ℓ = y₀ +
      ((∫ s in 0..a, sin (θ s)) + (∫ s in a..b, sin (θ s)) +
        (∫ s in b..ℓ, sin (θ s))) := by
  unfold yCoord
  exact congrArg (fun z : ℝ => y₀ + z)
    (integral_split_three (f := fun s => sin (θ s)) (continuous_sin.comp hθ) a b ℓ)

/-- Agreement of two C¹ angles on a closed interval implies agreement of
their density integrals. Derivative agreement is derived, not assumed.
Degenerate intervals are included. -/
theorem density_integral_eq_of_angle_eqOn {ε θ φ : ℝ → ℝ} {a b : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hφ : ContDiff ℝ 1 φ) (hab : a ≤ b)
    (hEq : EqOn θ φ (Icc a b)) :
    (∫ s in a..b, ε (deriv θ s)) = ∫ s in a..b, ε (deriv φ s) := by
  rcases hab.eq_or_lt with hab | hab
  · subst b
    simp
  have hd : EqOn (deriv θ) (deriv φ) (Ioo a b) := by
    intro s hs
    have he : θ =ᶠ[𝓝 s] φ := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      exact hEq ⟨ht.1.le, ht.2.le⟩
    exact he.deriv_eq
  have hdc : EqOn (deriv θ) (deriv φ) (Icc a b) := by
    have hc := hd.closure hθ.continuous_deriv_one hφ.continuous_deriv_one
    simpa only [closure_Ioo hab.ne] using hc
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hab.le] at hs
  exact congrArg ε (hdc hs)

/-- Two already smooth curves with the same exterior angles have the same
boundary angles and positions when both middle displacement integrals match.
The theorem does not construct a gluing from arbitrary angle pieces. -/
theorem boundary_eq_of_middle_integrals {θ φ : ℝ → ℝ} {a b ℓ : ℝ}
    (hθ : Continuous θ) (hφ : Continuous φ)
    (ha : 0 ≤ a) (_hab : a ≤ b) (hb : b ≤ ℓ)
    (hleft : EqOn θ φ (Icc 0 a)) (hright : EqOn θ φ (Icc b ℓ))
    (hx : (∫ s in a..b, cos (θ s)) = ∫ s in a..b, cos (φ s))
    (hy : (∫ s in a..b, sin (θ s)) = ∫ s in a..b, sin (φ s))
    (x₀ y₀ : ℝ) :
    θ 0 = φ 0 ∧ θ ℓ = φ ℓ ∧
      xCoord θ x₀ ℓ = xCoord φ x₀ ℓ ∧ yCoord θ y₀ ℓ = yCoord φ y₀ ℓ := by
  have hcos_left : (∫ s in 0..a, cos (θ s)) = ∫ s in 0..a, cos (φ s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ha] at hs
    exact congrArg cos (hleft hs)
  have hsin_left : (∫ s in 0..a, sin (θ s)) = ∫ s in 0..a, sin (φ s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ha] at hs
    exact congrArg sin (hleft hs)
  have hcos_right : (∫ s in b..ℓ, cos (θ s)) = ∫ s in b..ℓ, cos (φ s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hb] at hs
    exact congrArg cos (hright hs)
  have hsin_right : (∫ s in b..ℓ, sin (θ s)) = ∫ s in b..ℓ, sin (φ s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hb] at hs
    exact congrArg sin (hright hs)
  refine ⟨hleft ⟨le_rfl, ha⟩, hright ⟨hb, le_rfl⟩, ?_, ?_⟩
  · rw [xCoord_split_three hθ x₀ a b ℓ, xCoord_split_three hφ x₀ a b ℓ,
      hcos_left, hx, hcos_right]
  · rw [yCoord_split_three hθ y₀ a b ℓ, yCoord_split_three hφ y₀ a b ℓ,
      hsin_left, hy, hsin_right]

/-- A smooth middle replacement changes the total energy by exactly the middle
integral difference. The angle agreement outside implies derivative agreement. -/
theorem energy_sub_eq_middle_of_outer_angle_eq {ε θ φ : ℝ → ℝ} {a b ℓ : ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (hφ : ContDiff ℝ 1 φ)
    (ha : 0 ≤ a) (_hab : a ≤ b) (hb : b ≤ ℓ)
    (hleft : EqOn θ φ (Icc 0 a)) (hright : EqOn θ φ (Icc b ℓ)) :
    energy ε φ ℓ - energy ε θ ℓ =
      (∫ s in a..b, ε (deriv φ s)) - (∫ s in a..b, ε (deriv θ s)) := by
  have hl := density_integral_eq_of_angle_eqOn (ε := ε) hθ hφ ha hleft
  have hr := density_integral_eq_of_angle_eqOn (ε := ε) hθ hφ hb hright
  rw [energy_split_three hε hθ a b ℓ, energy_split_three hε hφ a b ℓ, hl, hr]
  ring

/-- Under the same smooth exterior data, energy comparison is exactly comparison
of the middle integrals. No minimizer existence is asserted. -/
theorem energy_le_iff_middle_integral_le {ε θ φ : ℝ → ℝ} {a b ℓ : ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (hφ : ContDiff ℝ 1 φ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ℓ)
    (hleft : EqOn θ φ (Icc 0 a)) (hright : EqOn θ φ (Icc b ℓ)) :
    energy ε φ ℓ ≤ energy ε θ ℓ ↔
      (∫ s in a..b, ε (deriv φ s)) ≤ ∫ s in a..b, ε (deriv θ s) := by
  have h := energy_sub_eq_middle_of_outer_angle_eq hε hθ hφ ha hab hb hleft hright
  constructor <;> intro hh <;> linarith

end Elastica
