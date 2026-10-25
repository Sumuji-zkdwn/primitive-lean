import Elastica.ExponentialWeight
import Elastica.PowerLogResponse
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Compose the existing positive weight with the existing normalized response.
The response is applied to the whole functional's weight, not to curvature.
Thus no positive-curvature hypothesis is introduced. -/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace Elastica

/-- At exponent zero, the composed representation recovers the energy exactly. -/
theorem powerLog_zero_exponentialWeight (β : ℝ) (ε θ : ℝ → ℝ) (ℓ : ℝ) :
    powerLog 0 (exponentialWeight β ε θ ℓ) = -β * energy ε θ ℓ := by
  rw [powerLog_zero, log_exponentialWeight]

/-- The positive weight makes the existing exponent-zero limit applicable to
every energy value, regardless of the sign of the curvature or the density. -/
theorem tendsto_powerLog_exponentialWeight_zero (β : ℝ) (ε θ : ℝ → ℝ) (ℓ : ℝ) :
    Tendsto (fun p => powerLog p (exponentialWeight β ε θ ℓ)) (𝓝 0)
      (𝓝 (-β * energy ε θ ℓ)) := by
  simpa only [log_exponentialWeight] using
    tendsto_powerLog_exponent_zero (exponentialWeight_pos β ε θ ℓ)

/-- Chain the two already proved derivatives and simplify the positive factor. -/
theorem hasDerivAt_powerLog_exp_neg_mul {f : ℝ → ℝ} {x d : ℝ}
    (p β : ℝ) (hf : HasDerivAt f d x) :
    HasDerivAt (fun t => powerLog p (exp (-β * f t)))
      (-β * exp (-p * β * f x) * d) x := by
  have he : exp (-β * f x) ^ (p - 1) * exp (-β * f x) =
      exp (-p * β * f x) := by
    rw [rpow_def_of_pos (exp_pos _), log_exp, ← exp_add]
    congr 1
    ring
  convert (hasDerivAt_powerLog (p := p) (exp_pos (-β * f x))).comp x
    (hasDerivAt_exp_neg_mul β hf) using 1
  calc
    -β * exp (-p * β * f x) * d =
        -β * (exp (-β * f x) ^ (p - 1) * exp (-β * f x)) * d := by rw [he]
    _ = _ := by ring

/-- All real response exponents reverse energy order when β is positive. -/
theorem strictAnti_powerLog_exp_neg_mul (p : ℝ) {β : ℝ} (hβ : 0 < β) :
    StrictAnti (fun x : ℝ => powerLog p (exp (-β * x))) := by
  apply strictAnti_of_deriv_neg
  intro x
  have hd : HasDerivAt (fun t : ℝ => powerLog p (exp (-β * t)))
      (-β * exp (-p * β * x) * 1) x := by
    simpa only [id_eq] using hasDerivAt_powerLog_exp_neg_mul p β (hasDerivAt_id x)
  rw [hd.deriv]
  simpa only [mul_one] using mul_neg_of_neg_of_pos (neg_neg_of_pos hβ) (exp_pos _)

/-- Exact comparison on the same curves, with no regularity requirement for
this order-theoretic identity. -/
theorem energy_le_iff_powerLog_exponentialWeight_le (p : ℝ) {β : ℝ}
    (hβ : 0 < β) (ε θ ψ : ℝ → ℝ) (ℓ : ℝ) :
    energy ε θ ℓ ≤ energy ε ψ ℓ ↔
      powerLog p (exponentialWeight β ε ψ ℓ) ≤
        powerLog p (exponentialWeight β ε θ ℓ) := by
  exact (strictAnti_powerLog_exp_neg_mul p hβ).le_iff_ge.symm

/-- Compose with the existing constrained C¹ neighborhood, retaining all
endpoint data rather than replacing it by an unconstrained scalar problem. -/
theorem locallyMinimizing_iff_powerLog_weight_local_maximum (p : ℝ) {β : ℝ}
    (hβ : 0 < β) (ε θ : ℝ → ℝ) (ℓ : ℝ) :
    LocallyMinimizing ε θ ℓ ↔
      ∃ r : ℝ, 0 < r ∧ ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ →
        ψ 0 = θ 0 → ψ ℓ = θ ℓ →
        (∫ s in 0..ℓ, cos (ψ s)) = (∫ s in 0..ℓ, cos (θ s)) →
        (∫ s in 0..ℓ, sin (ψ s)) = (∫ s in 0..ℓ, sin (θ s)) →
        (∀ s ∈ Icc 0 ℓ,
          |ψ s - θ s| < r ∧ |deriv ψ s - deriv θ s| < r) →
        powerLog p (exponentialWeight β ε ψ ℓ) ≤
          powerLog p (exponentialWeight β ε θ ℓ) := by
  simp only [LocallyMinimizing, energy_le_iff_powerLog_exponentialWeight_le p hβ]

/-- Actual differentiation along the existing angle variation. -/
theorem hasDerivAt_powerLog_weight_variation {ε θ η : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 1 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η) (p β : ℝ) :
    HasDerivAt (fun t => powerLog p
      (exponentialWeight β ε (angleVariation θ η t) ℓ))
      (-β * exp (-p * β * energy ε θ ℓ) *
        (∫ s in 0..ℓ, deriv ε (deriv θ s) * deriv η s)) 0 := by
  have hzero : angleVariation θ η 0 = θ := by
    funext s
    simp only [angleVariation, zero_mul, add_zero]
  simpa only [exponentialWeight, hzero] using
    hasDerivAt_powerLog_exp_neg_mul p β (hasDerivAt_energy_variation hℓ hε hθ hη)

/-- Vanishing of the actual first variation is unchanged for every exponent. -/
theorem powerLog_weight_variation_stationary_iff {ε θ η : ℝ → ℝ} {ℓ β : ℝ}
    (hβ : β ≠ 0) (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 1 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η) (p : ℝ) :
    deriv (fun t => powerLog p
      (exponentialWeight β ε (angleVariation θ η t) ℓ)) 0 = 0 ↔
      deriv (fun t => energy ε (angleVariation θ η t) ℓ) 0 = 0 := by
  rw [(hasDerivAt_powerLog_weight_variation hℓ hε hθ hη p β).deriv,
    (hasDerivAt_energy_variation hℓ hε hθ hη).deriv]
  simp only [mul_eq_zero, neg_eq_zero, hβ, exp_ne_zero, false_or]

/-- Interval composition transports through the already established product
identity for normalized powers; p=0 reduces to additive negative energy. -/
theorem powerLog_exponentialWeight_split {ε θ : ℝ → ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (p β a ℓ : ℝ) :
    powerLog p (exponentialWeight β ε θ ℓ) =
      powerLog p (exponentialWeight β ε θ a) +
      powerLog p (exp (-β * (∫ s in a..ℓ, ε (deriv θ s)))) +
      p * powerLog p (exponentialWeight β ε θ a) *
        powerLog p (exp (-β * (∫ s in a..ℓ, ε (deriv θ s)))) := by
  rw [exponentialWeight_split hε hθ β a ℓ]
  exact powerLog_mul p (exponentialWeight_pos β ε θ a) (exp_pos _)

end Elastica
