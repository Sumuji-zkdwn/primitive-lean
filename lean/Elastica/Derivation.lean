import Elastica.Variation
import Elastica.Stationary
import Elastica.Equations

/-! The end-to-end connection. Stationarity is stated using derivatives of the
actual energy and endpoint displacement integrals; their formulas are theorems.
This is linearized constrained stationarity, not an existence or minimizer theorem.
-/

noncomputable section
open Real Set MeasureTheory
namespace Elastica

/-- Stationarity for all C¹ fixed-angle variations whose endpoint displacement
derivatives vanish. It does not say the additive variation preserves endpoints
for nonzero t. Smoothness assumptions are supplied by the main theorem. -/
def Stationary (ε θ : ℝ → ℝ) (ℓ : ℝ) : Prop :=
  ∀ η : variationSpace ℓ,
    deriv (fun t : ℝ => ∫ s in 0..ℓ, cos (θ s + t * η.val s)) 0 = 0 →
    deriv (fun t : ℝ => ∫ s in 0..ℓ, sin (θ s + t * η.val s)) 0 = 0 →
    deriv (fun t : ℝ => energy ε (angleVariation θ η.val t) ℓ) 0 = 0

/-- The integral characterization follows from genuine parameter derivatives. -/
theorem stationary_iff_firstVariation {ε θ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 1 ε) (hθ : ContDiff ℝ 1 θ) :
    Stationary ε θ ℓ ↔
      ∀ η : variationSpace ℓ,
        (∫ s in 0..ℓ, -sin (θ s) * η.val s) = 0 →
        (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0 →
        (∫ s in 0..ℓ, deriv ε (deriv θ s) * deriv η.val s) = 0 := by
  unfold Stationary
  constructor <;> intro h η hx hy
  · have hx' := (hasDerivAt_horizontal_variation hℓ hθ.continuous η.property.1.continuous).deriv
    have hy' := (hasDerivAt_vertical_variation hℓ hθ.continuous η.property.1.continuous).deriv
    have he := (hasDerivAt_energy_variation hℓ hε hθ η.property.1).deriv
    rw [← he]
    exact h η (hx'.trans hx) (hy'.trans hy)
  · have hx' := (hasDerivAt_horizontal_variation hℓ hθ.continuous η.property.1.continuous).deriv
    have hy' := (hasDerivAt_vertical_variation hℓ hθ.continuous η.property.1.continuous).deriv
    have he := (hasDerivAt_energy_variation hℓ hε hθ η.property.1).deriv
    rw [he]
    exact h η (hx'.symm.trans hx) (hy'.symm.trans hy)

/-- Main theorem: genuine linearized constrained stationarity produces force
multipliers, the angle equation, one first-integral constant and the curvature
equation. No rank, convexity, evenness or nonzero curvature is assumed. -/
theorem stationary_angle_firstIntegral_curvature
    {ε θ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hε : ContDiff ℝ 3 ε) (hθ : ContDiff ℝ 3 θ)
    (hstat : Stationary ε θ ℓ) :
    ∃ lam μ σ : ℝ, ∀ s ∈ Ioo 0 ℓ,
      (deriv (fun t => deriv ε (deriv θ t)) s =
        -lam * sin (θ s) + μ * cos (θ s)) ∧
      (deriv θ s * deriv ε (deriv θ s) - ε (deriv θ s) -
        lam * cos (θ s) - μ * sin (θ s) = σ) ∧
      (deriv (deriv (fun t => deriv ε (deriv θ t))) s +
        (deriv θ s) ^ 2 * deriv ε (deriv θ s) -
        deriv θ s * ε (deriv θ s) - σ * deriv θ s = 0) := by
  have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  have hε1 : ContDiff ℝ 1 ε := hε.of_le (by norm_num)
  have hκ : ContDiff ℝ 2 (deriv θ) := hθ.deriv' (n := 2)
  have hε' : ContDiff ℝ 2 (deriv ε) := hε.deriv' (n := 2)
  have hM : ContDiff ℝ 2 (fun t => deriv ε (deriv θ t)) := hε'.comp hκ
  obtain ⟨lam, μ, hAngle⟩ := angleEquation_of_stationary hℓ hθ1 hM
    ((stationary_iff_firstVariation hℓ.le hε1 hθ1).mp hstat)
  obtain ⟨σ, hσ⟩ := smooth_angle_firstIntegral_and_curvature hθ hε hAngle
  exact ⟨lam, μ, σ, fun s hs => ⟨hAngle s hs, hσ s hs⟩⟩

end Elastica
