import Elastica.Examples
import Elastica.PowerLogResponse
import Elastica.MinimumConditions

/-!
# Affine density changes and the exponent-one classical problem

The existing boundary-energy identity transports the actual C¹ constrained
local-minimum predicate and actual first-variation stationarity.  Applying these
transports to exponent one connects the optional power/log response to the
classical elastica equations.  Fixed real-valued endpoint angles are essential.
No existence, sign of curvature, or sufficiency claim is made.
-/

noncomputable section
open Real Set MeasureTheory
namespace Elastica

/-- Adding an affine function of signed curvature preserves the same C¹
constrained local minima, including the same neighborhood radius. -/
theorem locallyMinimizing_affine_density_iff {ε θ : ℝ → ℝ} {ℓ : ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (a b : ℝ) :
    LocallyMinimizing (fun q => ε q + a * q + b) θ ℓ ↔
      LocallyMinimizing ε θ ℓ := by
  have he (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
      (h0 : ψ 0 = θ 0) (hend : ψ ℓ = θ ℓ) :
      energy (fun q => ε q + a * q + b) θ ℓ ≤
          energy (fun q => ε q + a * q + b) ψ ℓ ↔
        energy ε θ ℓ ≤ energy ε ψ ℓ := by
    rw [energy_affine_density hε hθ, energy_affine_density hε hψ, h0, hend]
    exact (add_le_add_iff_right _).trans (add_le_add_iff_right _)
  constructor <;> rintro ⟨r, hr, hm⟩ <;> refine ⟨r, hr, ?_⟩ <;>
    intro ψ hψ h0 hend hx hy hclose
  · exact (he ψ hψ h0 hend).mp (hm ψ hψ h0 hend hx hy hclose)
  · exact (he ψ hψ h0 hend).mpr (hm ψ hψ h0 hend hx hy hclose)

/-- Along every fixed-angle variation the actual energy functions differ by a
constant.  Thus affine density changes preserve actual derivative stationarity;
no first-variation formula is introduced as a hypothesis. -/
theorem stationary_affine_density_iff {ε θ : ℝ → ℝ} {ℓ : ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (a b : ℝ) :
    Stationary (fun q => ε q + a * q + b) θ ℓ ↔ Stationary ε θ ℓ := by
  have he (η : variationSpace ℓ) :
      (fun t => energy (fun q => ε q + a * q + b) (angleVariation θ η.val t) ℓ) =
        (fun t => energy ε (angleVariation θ η.val t) ℓ +
          (a * (θ ℓ - θ 0) + b * ℓ)) := by
    funext t
    have hvar : ContDiff ℝ 1 (angleVariation θ η.val t) :=
      hθ.add (contDiff_const.mul η.property.1)
    rw [energy_affine_density hε hvar]
    simp only [angleVariation, η.property.2.1, η.property.2.2, mul_zero, add_zero]
    ring
  unfold Stationary
  simp_rw [he, deriv_add_const]

/-- Exponent one gives exactly the classical quadratic C¹ local-minimum
problem, on all signed curvatures and with the original endpoint constraints. -/
theorem locallyMinimizing_powerLogDensity_one_iff {θ : ℝ → ℝ} {ℓ κ₀ : ℝ}
    (hθ : ContDiff ℝ 1 θ) (K : ℝ) (hκ₀ : 0 < κ₀) :
    LocallyMinimizing (powerLogDensity 1 K κ₀) θ ℓ ↔
      LocallyMinimizing (fun q => (K / κ₀) * q ^ 2 / 2) θ ℓ := by
  have he : powerLogDensity 1 K κ₀ =
      fun q => (K / κ₀) * q ^ 2 / 2 + (-K) * q + K * κ₀ / 2 := by
    funext q
    rw [powerLogDensity_one K hκ₀]
    ring
  rw [he]
  exact locallyMinimizing_affine_density_iff (by fun_prop) hθ (-K) (K * κ₀ / 2)

/-- The exponent-one response and the corresponding quadratic density have
the same stationary angles under the original linearized endpoint constraints. -/
theorem stationary_powerLogDensity_one_iff {θ : ℝ → ℝ} {ℓ κ₀ : ℝ}
    (hθ : ContDiff ℝ 1 θ) (K : ℝ) (hκ₀ : 0 < κ₀) :
    Stationary (powerLogDensity 1 K κ₀) θ ℓ ↔
      Stationary (fun q => (K / κ₀) * q ^ 2 / 2) θ ℓ := by
  have he : powerLogDensity 1 K κ₀ =
      fun q => (K / κ₀) * q ^ 2 / 2 + (-K) * q + K * κ₀ / 2 := by
    funext q
    rw [powerLogDensity_one K hκ₀]
    ring
  rw [he]
  exact stationary_affine_density_iff (by fun_prop) hθ (-K) (K * κ₀ / 2)

/-- A nonstraight C³ local minimum for the exponent-one response satisfies the
classical angle, first-integral, and curvature equations with stiffness `K / κ₀`.
The hypotheses are on the actual constrained energy; no stationarity or equation
is supplied.  The first-integral constant is that of the quadratic representative. -/
theorem locallyMinimizing_powerLogDensity_one_classical_equations
    {θ : ℝ → ℝ} {ℓ κ₀ : ℝ} (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 3 θ)
    (hne : ¬ ∀ s ∈ Icc 0 ℓ, θ s = θ 0) (K : ℝ) (hκ₀ : 0 < κ₀)
    (hmin : LocallyMinimizing (powerLogDensity 1 K κ₀) θ ℓ) :
    ∃ lam μ σ : ℝ, ∀ s ∈ Ioo 0 ℓ,
      ((K / κ₀) * deriv (deriv θ) s = -lam * sin (θ s) + μ * cos (θ s)) ∧
      ((K / κ₀) * (deriv θ s) ^ 2 / 2 -
        lam * cos (θ s) - μ * sin (θ s) = σ) ∧
      ((K / κ₀) * deriv (deriv (deriv θ)) s +
        (K / κ₀) * (deriv θ s) ^ 3 / 2 - σ * deriv θ s = 0) := by
  have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  have hκ : ContDiff ℝ 2 (deriv θ) := hθ.deriv' (n := 2)
  have hmin' := (locallyMinimizing_powerLogDensity_one_iff hθ1 K hκ₀).mp hmin
  obtain ⟨lam, μ, σ, heq⟩ :=
    locallyMinimizing_angle_firstIntegral_curvature hℓ (by fun_prop) hθ hne hmin'
  have hmoment : (fun t => deriv (fun q : ℝ => (K / κ₀) * q ^ 2 / 2) (deriv θ t)) =
      (fun t => (K / κ₀) * deriv θ t) := by
    funext t
    exact (quadratic_density_hasDerivAt (K / κ₀) (deriv θ t)).deriv
  refine ⟨lam, μ, σ, ?_⟩
  intro s hs
  obtain ⟨hangle, hfirst, hcurve⟩ := heq s hs
  refine ⟨?_, ?_, quadratic_curvature_equation hκ hcurve⟩
  · rw [hmoment] at hangle
    rw [((hκ.differentiable (by norm_num) s).hasDerivAt.const_mul (K / κ₀)).deriv]
      at hangle
    exact hangle
  · rw [(quadratic_density_hasDerivAt (K / κ₀) (deriv θ s)).deriv] at hfirst
    nlinarith [hfirst]

end Elastica
