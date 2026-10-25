import Elastica.ExactVariation
import Elastica.LocalMinimum
import Elastica.ConstrainedSecondVariation
import Elastica.Derivation
import Elastica.ScalarMinimum

/-! End-to-end necessary conditions for C¹ constrained local minima.  Exact
constraint realization, actual energy differentiation, and the local-minimum
comparison are all proved in the imported modules. -/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace Elastica

/-- A genuine C¹ local minimum at a nonstraight curve satisfies the original
stationarity predicate, which is stated using actual parameter derivatives. -/
theorem locallyMinimizing_stationary_of_nonstraight {ε θ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hε : ContDiff ℝ 2 ε) (hθ : ContDiff ℝ 1 θ)
    (hne : ∃ s ∈ Ioo 0 ℓ, deriv θ s ≠ 0)
    (hmin : LocallyMinimizing ε θ ℓ) : Stationary ε θ ℓ := by
  apply (stationary_iff_firstVariation hℓ.le (hε.of_le (by norm_num)) hθ).mpr
  intro η hx hy
  obtain ⟨ξ₁, ξ₂, a, b, ha, hb, ha0, hb0, ha1, hb1, hexact⟩ :=
    exists_exact_endpoint_variation hℓ hθ hne η hx hy
  have hm := locallyMinimizing_isLocalMin_corrected_family hθ hmin η ξ₁ ξ₂
    ha.continuousAt hb.continuousAt ha0 hb0 hexact
  have hd := (hasDerivAt_corrected_energy_and_deriv hℓ.le hε hθ η.property.1
    ξ₁.property.1 ξ₂.property.1 ha hb ha0 hb0 ha1.deriv hb1.deriv).1
  exact hd.deriv.symm.trans hm.deriv_eq_zero

/-- The existing angle, first-integral and curvature equations now follow
from a true constrained local minimum; no stationarity hypothesis is supplied. -/
theorem locallyMinimizing_angle_firstIntegral_curvature
    {ε θ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hε : ContDiff ℝ 3 ε) (hθ : ContDiff ℝ 3 θ)
    (hne : ¬ ∀ s ∈ Icc 0 ℓ, θ s = θ 0)
    (hmin : LocallyMinimizing ε θ ℓ) :
    ∃ lam μ σ : ℝ, ∀ s ∈ Ioo 0 ℓ,
      (deriv (fun t => deriv ε (deriv θ t)) s =
        -lam * sin (θ s) + μ * cos (θ s)) ∧
      (deriv θ s * deriv ε (deriv θ s) - ε (deriv θ s) -
        lam * cos (θ s) - μ * sin (θ s) = σ) ∧
      (deriv (deriv (fun t => deriv ε (deriv θ t))) s +
        (deriv θ s) ^ 2 * deriv ε (deriv θ s) -
        deriv θ s * ε (deriv θ s) - σ * deriv θ s = 0) := by
  have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  exact stationary_angle_firstIntegral_curvature hℓ hε hθ
    (locallyMinimizing_stationary_of_nonstraight hℓ (hε.of_le (by norm_num)) hθ1
      (exists_nonzero_curvature_of_nonconstant hℓ hθ1 hne) hmin)

/-- Every linearized feasible direction at a nonstraight local minimum has
nonnegative constrained second variation, for any stationary multipliers. -/
theorem locallyMinimizing_secondVariation_nonneg
    {ε θ : ℝ → ℝ} {ℓ lam μ : ℝ}
    (hℓ : 0 < ℓ) (hε : ContDiff ℝ 2 ε) (hθ : ContDiff ℝ 1 θ)
    (hne : ∃ s ∈ Ioo 0 ℓ, deriv θ s ≠ 0)
    (hmin : LocallyMinimizing ε θ ℓ)
    (hm : ∀ ζ : variationSpace ℓ,
      (∫ s in 0..ℓ, deriv ε (deriv θ s) * deriv ζ.val s) +
        lam * (∫ s in 0..ℓ, -sin (θ s) * ζ.val s) +
        μ * (∫ s in 0..ℓ, cos (θ s) * ζ.val s) = 0)
    (η : variationSpace ℓ)
    (hx : (∫ s in 0..ℓ, -sin (θ s) * η.val s) = 0)
    (hy : (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0) :
    0 ≤ ∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η.val s)^2 -
      (lam * cos (θ s) + μ * sin (θ s)) * (η.val s)^2 := by
  obtain ⟨ξ₁, ξ₂, a, b, ha, hb, ha0, hb0, ha1, hb1, hexact⟩ :=
    exists_exact_endpoint_variation hℓ hθ hne η hx hy
  have hpath := locallyMinimizing_isLocalMin_corrected_family hθ hmin η ξ₁ ξ₂
    ha.continuousAt hb.continuousAt ha0 hb0 hexact
  have hd := (hasDerivAt_corrected_energy_and_deriv hℓ.le hε hθ η.property.1
    ξ₁.property.1 ξ₂.property.1 ha hb ha0 hb0 ha1.deriv hb1.deriv).1
  have hsecond := constrained_secondVariation_corrected hℓ.le hε hθ η.property.1
    ξ₁ ξ₂ ha hb ha0 hb0 ha1.deriv hb1.deriv
    (hexact.mono fun _ h => h.1) (hexact.mono fun _ h => h.2) hm
  exact second_derivative_nonneg_of_local_min hpath hd.continuousAt hsecond

/-- Complete necessary-condition theorem. A nonstraight C¹ constrained local
minimum with the original C³ data has one choice of multipliers that satisfies
all three classical equations and the constrained second-variation inequality.
Neither stationarity, exact variation realization, nor rank is assumed. -/
theorem locallyMinimizing_necessary_conditions
    {ε θ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hε : ContDiff ℝ 3 ε) (hθ : ContDiff ℝ 3 θ)
    (hne : ¬ ∀ s ∈ Icc 0 ℓ, θ s = θ 0)
    (hmin : LocallyMinimizing ε θ ℓ) :
    ∃ lam μ σ : ℝ,
      (∀ s ∈ Ioo 0 ℓ,
        (deriv (fun t => deriv ε (deriv θ t)) s =
          -lam * sin (θ s) + μ * cos (θ s)) ∧
        (deriv θ s * deriv ε (deriv θ s) - ε (deriv θ s) -
          lam * cos (θ s) - μ * sin (θ s) = σ) ∧
        (deriv (deriv (fun t => deriv ε (deriv θ t))) s +
          (deriv θ s) ^ 2 * deriv ε (deriv θ s) -
          deriv θ s * ε (deriv θ s) - σ * deriv θ s = 0)) ∧
      (∀ η : variationSpace ℓ,
        (∫ s in 0..ℓ, -sin (θ s) * η.val s) = 0 →
        (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0 →
        0 ≤ ∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η.val s)^2 -
          (lam * cos (θ s) + μ * sin (θ s)) * (η.val s)^2) := by
  have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  have hε1 : ContDiff ℝ 1 ε := hε.of_le (by norm_num)
  have hε2 : ContDiff ℝ 2 ε := hε.of_le (by norm_num)
  have hn := exists_nonzero_curvature_of_nonconstant hℓ hθ1 hne
  have hstat := locallyMinimizing_stationary_of_nonstraight hℓ hε2 hθ1 hn hmin
  have hM : ContDiff ℝ 2 (fun t => deriv ε (deriv θ t)) :=
    (hε.deriv' (n := 2)).comp (hθ.deriv' (n := 2))
  obtain ⟨lam, μ, hm⟩ := stationary_multipliers hθ.continuous hM.continuous
    ((stationary_iff_firstVariation hℓ.le hε1 hθ1).mp hstat)
  have hAngle : ∀ s ∈ Ioo 0 ℓ,
      deriv (fun t => deriv ε (deriv θ t)) s = -lam * sin (θ s) + μ * cos (θ s) := by
    apply residual_zero_of_augmented_stationary hℓ hM
      ((contDiff_const.mul hθ1.sin).add (contDiff_const.mul hθ1.cos))
    intro η
    rw [force_integral hθ.continuous η]
    linarith [hm η]
  obtain ⟨σ, hσ⟩ := smooth_angle_firstIntegral_and_curvature hθ hε hAngle
  refine ⟨lam, μ, σ, (fun s hs => ⟨hAngle s hs, hσ s hs⟩), ?_⟩
  exact locallyMinimizing_secondVariation_nonneg hℓ hε2 hθ1 hn hmin hm

end Elastica
