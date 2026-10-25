import Elastica.Composition
import Elastica.Derivation
import Elastica.LocalMinimum
import Elastica.ConstrainedSecondVariation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exponential representation of the whole curvature energy

The exponential is applied after integration.  It does not replace the density
by its exponential.  For positive `β`, additive interval composition becomes
multiplication and comparisons reverse on exactly the same feasible set.
All variation statements concern actual parameter derivatives.  In particular,
the second-derivative identity on an exact constrained family uses the existing
calculation of that family's curvature energy, including its acceleration.
No probability measure, dynamics, positivity of the density, or minimizer
existence is asserted.
-/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology

namespace Elastica

/-- A positive representation of the whole energy; this is not a new density. -/
def exponentialWeight (β : ℝ) (ε θ : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  exp (-β * energy ε θ ℓ)

theorem exponentialWeight_pos (β : ℝ) (ε θ : ℝ → ℝ) (ℓ : ℝ) :
    0 < exponentialWeight β ε θ ℓ := exp_pos _

theorem log_exponentialWeight (β : ℝ) (ε θ : ℝ → ℝ) (ℓ : ℝ) :
    log (exponentialWeight β ε θ ℓ) = -β * energy ε θ ℓ := log_exp _

/-- No sign condition on the energy is needed to recover it by a logarithm. -/
theorem energy_eq_neg_log_exponentialWeight {β : ℝ} (hβ : β ≠ 0)
    (ε θ : ℝ → ℝ) (ℓ : ℝ) :
    energy ε θ ℓ = -log (exponentialWeight β ε θ ℓ) / β := by
  rw [log_exponentialWeight]
  field_simp

/-- Adjacent intervals compose multiplicatively. Oriented integrals make the
identity valid without an ordering hypothesis on the cut. -/
theorem exponentialWeight_split {ε θ : ℝ → ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (β a ℓ : ℝ) :
    exponentialWeight β ε θ ℓ =
      exponentialWeight β ε θ a * exp (-β * (∫ s in a..ℓ, ε (deriv θ s))) := by
  have hc := hε.comp hθ.continuous_deriv_one
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a ℓ)
  simp only [Function.comp_apply] at he
  unfold exponentialWeight energy
  rw [← he, mul_add, exp_add]

/-- The existing three-piece energy decomposition gives three multiplicative factors. -/
theorem exponentialWeight_split_three {ε θ : ℝ → ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (β a b ℓ : ℝ) :
    exponentialWeight β ε θ ℓ =
      exp (-β * (∫ s in 0..a, ε (deriv θ s))) *
      exp (-β * (∫ s in a..b, ε (deriv θ s))) *
      exp (-β * (∫ s in b..ℓ, ε (deriv θ s))) := by
  rw [exponentialWeight, energy_split_three hε hθ a b ℓ]
  rw [mul_add, mul_add, exp_add, exp_add]

theorem exp_neg_mul_le_exp_neg_mul_iff {β x y : ℝ} (hβ : 0 < β) :
    exp (-β * x) ≤ exp (-β * y) ↔ y ≤ x := by
  rw [exp_le_exp]
  constructor <;> intro h <;> nlinarith

theorem exp_neg_mul_lt_exp_neg_mul_iff {β x y : ℝ} (hβ : 0 < β) :
    exp (-β * x) < exp (-β * y) ↔ y < x := by
  rw [exp_lt_exp]
  constructor <;> intro h <;> nlinarith

/-- The same curves are compared, with the order reversed. -/
theorem energy_le_iff_exponentialWeight_le {β : ℝ} (hβ : 0 < β)
    (ε θ ψ : ℝ → ℝ) (ℓ : ℝ) :
    energy ε θ ℓ ≤ energy ε ψ ℓ ↔
      exponentialWeight β ε ψ ℓ ≤ exponentialWeight β ε θ ℓ :=
  (exp_neg_mul_le_exp_neg_mul_iff hβ).symm

theorem energy_lt_iff_exponentialWeight_lt {β : ℝ} (hβ : 0 < β)
    (ε θ ψ : ℝ → ℝ) (ℓ : ℝ) :
    energy ε θ ℓ < energy ε ψ ℓ ↔
      exponentialWeight β ε ψ ℓ < exponentialWeight β ε θ ℓ :=
  (exp_neg_mul_lt_exp_neg_mul_iff hβ).symm

/-- Global extrema correspond on any one fixed feasible set. -/
theorem energy_minimum_iff_exponentialWeight_maximum {β : ℝ} (hβ : 0 < β)
    (ε θ : ℝ → ℝ) (ℓ : ℝ) (S : Set (ℝ → ℝ)) :
    (∀ ψ ∈ S, energy ε θ ℓ ≤ energy ε ψ ℓ) ↔
      (∀ ψ ∈ S, exponentialWeight β ε ψ ℓ ≤ exponentialWeight β ε θ ℓ) := by
  simp only [energy_le_iff_exponentialWeight_le hβ]

/-- Local extrema also correspond, including on a restricted feasible set. -/
theorem isLocalMinOn_iff_isLocalMaxOn_exp_neg_mul
    {α : Type*} [TopologicalSpace α] {β : ℝ} (hβ : 0 < β)
    (f : α → ℝ) (S : Set α) (x : α) :
    IsLocalMinOn f S x ↔ IsLocalMaxOn (fun y => exp (-β * f y)) S x := by
  change (∀ᶠ y in 𝓝[S] x, f x ≤ f y) ↔
    (∀ᶠ y in 𝓝[S] x, exp (-β * f y) ≤ exp (-β * f x))
  simp only [exp_neg_mul_le_exp_neg_mul_iff hβ]

/-- The original C¹ constrained neighborhood and boundary conditions are retained. -/
theorem locallyMinimizing_iff_exponentialWeight_local_maximum
    {β : ℝ} (hβ : 0 < β) (ε θ : ℝ → ℝ) (ℓ : ℝ) :
    LocallyMinimizing ε θ ℓ ↔
      ∃ r : ℝ, 0 < r ∧ ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ →
        ψ 0 = θ 0 → ψ ℓ = θ ℓ →
        (∫ s in 0..ℓ, cos (ψ s)) = (∫ s in 0..ℓ, cos (θ s)) →
        (∫ s in 0..ℓ, sin (ψ s)) = (∫ s in 0..ℓ, sin (θ s)) →
        (∀ s ∈ Icc 0 ℓ,
          |ψ s - θ s| < r ∧ |deriv ψ s - deriv θ s| < r) →
        exponentialWeight β ε ψ ℓ ≤ exponentialWeight β ε θ ℓ := by
  simp only [LocallyMinimizing, energy_le_iff_exponentialWeight_le hβ]

/-- Chain rule for an actual scalar parameter derivative. -/
theorem hasDerivAt_exp_neg_mul {f : ℝ → ℝ} {x d : ℝ}
    (β : ℝ) (hf : HasDerivAt f d x) :
    HasDerivAt (fun t => exp (-β * f t)) (-β * exp (-β * f x) * d) x := by
  convert (hf.const_mul (-β)).exp using 1
  ring

/-- The logarithmic inverse transports actual differentiability back to the energy. -/
theorem differentiableAt_exp_neg_mul_iff {f : ℝ → ℝ} {x β : ℝ}
    (hβ : β ≠ 0) :
    DifferentiableAt ℝ (fun t => exp (-β * f t)) x ↔ DifferentiableAt ℝ f x := by
  constructor
  · intro hw
    have h := (hw.log (exp_ne_zero _)).const_mul (-(β⁻¹))
    simpa only [log_exp, neg_mul_neg, ← mul_assoc, inv_mul_cancel₀ hβ, one_mul] using h
  · intro hf
    exact (hasDerivAt_exp_neg_mul β hf.hasDerivAt).differentiableAt

/-- Stationarity equivalence is about actual derivatives, not an assumed formula. -/
theorem hasDerivAt_exp_neg_mul_zero_iff {f : ℝ → ℝ} {x β : ℝ}
    (hβ : β ≠ 0) :
    HasDerivAt (fun t => exp (-β * f t)) 0 x ↔ HasDerivAt f 0 x := by
  constructor
  · intro hw
    have hf := (differentiableAt_exp_neg_mul_iff hβ).mp hw.differentiableAt
    have he := (hasDerivAt_exp_neg_mul β hf.hasDerivAt).unique hw
    have hd : deriv f x = 0 := by
      rcases mul_eq_zero.mp he with h | h
      · exact False.elim ((mul_ne_zero (neg_ne_zero.mpr hβ) (exp_ne_zero _)) h)
      · exact h
    simpa only [hd] using hf.hasDerivAt
  · intro hf
    simpa only [mul_zero] using hasDerivAt_exp_neg_mul β hf

/-- The total derivative formula also holds where the inner function is not
differentiable: the logarithmic inverse forces both total derivatives to be zero. -/
theorem deriv_exp_neg_mul {f : ℝ → ℝ} {β : ℝ} (hβ : β ≠ 0) (x : ℝ) :
    deriv (fun t => exp (-β * f t)) x = -β * exp (-β * f x) * deriv f x := by
  by_cases hf : DifferentiableAt ℝ f x
  · exact (hasDerivAt_exp_neg_mul β hf.hasDerivAt).deriv
  · have hw : ¬ DifferentiableAt ℝ (fun t => exp (-β * f t)) x :=
      fun h => hf ((differentiableAt_exp_neg_mul_iff hβ).mp h)
    simp only [deriv_zero_of_not_differentiableAt hf,
      deriv_zero_of_not_differentiableAt hw, mul_zero]

theorem deriv_exp_neg_mul_eq_zero_iff {f : ℝ → ℝ} {β : ℝ}
    (hβ : β ≠ 0) (x : ℝ) :
    deriv (fun t => exp (-β * f t)) x = 0 ↔ deriv f x = 0 := by
  rw [deriv_exp_neg_mul hβ]
  simp only [mul_eq_zero, neg_eq_zero, hβ, exp_ne_zero, false_or]

/-- Actual scalar second derivative, requiring only the two stated derivative
facts at the point. The extra square term is retained away from stationarity. -/
theorem hasDerivAt_deriv_exp_neg_mul {f : ℝ → ℝ} {x d q β : ℝ}
    (hβ : β ≠ 0) (hf : HasDerivAt f d x) (hsecond : HasDerivAt (deriv f) q x) :
    HasDerivAt (deriv (fun t => exp (-β * f t)))
      (β ^ 2 * exp (-β * f x) * d ^ 2 - β * exp (-β * f x) * q) x := by
  have he : deriv (fun t => exp (-β * f t)) =
      fun t => -β * exp (-β * f t) * deriv f t :=
    funext (deriv_exp_neg_mul hβ)
  rw [he]
  convert ((hasDerivAt_exp_neg_mul β hf).const_mul (-β)).mul hsecond using 1
  rw [hf.deriv]
  ring

/-- At a stationary point the second derivative changes by the negative factor
`-β * exp (-β * f x)` when `β > 0`. No minimality is assumed. -/
theorem hasDerivAt_deriv_exp_neg_mul_of_stationary {f : ℝ → ℝ} {x q β : ℝ}
    (hβ : β ≠ 0) (hf : HasDerivAt f 0 x) (hsecond : HasDerivAt (deriv f) q x) :
    HasDerivAt (deriv (fun t => exp (-β * f t)))
      (-β * exp (-β * f x) * q) x := by
  simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_sub, neg_mul] using
    hasDerivAt_deriv_exp_neg_mul hβ hf hsecond

/-- The first derivative uses the already proved differentiation of the actual energy. -/
theorem hasDerivAt_exponentialWeight_variation {ε θ η : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 1 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η) (β : ℝ) :
    HasDerivAt (fun t => exponentialWeight β ε (angleVariation θ η t) ℓ)
      (-β * exponentialWeight β ε θ ℓ *
        (∫ s in 0..ℓ, deriv ε (deriv θ s) * deriv η s)) 0 := by
  have hzero : angleVariation θ η 0 = θ := by
    funext s
    simp only [angleVariation, zero_mul, add_zero]
  simpa only [exponentialWeight, hzero] using
    hasDerivAt_exp_neg_mul β (hasDerivAt_energy_variation hℓ hε hθ hη)

/-- Stationarity along each actual energy variation is unchanged for nonzero `β`. -/
theorem exponentialWeight_variation_stationary_iff {β : ℝ} (hβ : β ≠ 0)
    (ε θ η : ℝ → ℝ) (ℓ : ℝ) :
    HasDerivAt (fun t => exponentialWeight β ε (angleVariation θ η t) ℓ) 0 0 ↔
      HasDerivAt (fun t => energy ε (angleVariation θ η t) ℓ) 0 0 :=
  hasDerivAt_exp_neg_mul_zero_iff hβ

/-- The existing stationarity predicate uses the same fixed-angle directions and
the same two linearized displacement constraints after the change of representation. -/
theorem stationary_iff_exponentialWeight_stationary {β : ℝ} (hβ : β ≠ 0)
    (ε θ : ℝ → ℝ) (ℓ : ℝ) :
    Stationary ε θ ℓ ↔
      ∀ η : variationSpace ℓ,
        deriv (fun t : ℝ => ∫ s in 0..ℓ, cos (θ s + t * η.val s)) 0 = 0 →
        deriv (fun t : ℝ => ∫ s in 0..ℓ, sin (θ s + t * η.val s)) 0 = 0 →
        deriv (fun t => exponentialWeight β ε (angleVariation θ η.val t) ℓ) 0 = 0 := by
  simp only [Stationary, exponentialWeight, deriv_exp_neg_mul_eq_zero_iff hβ]

/-- The full second derivative along the actual additive angle family. This
family need not preserve endpoint positions; hence the square term is retained. -/
theorem hasDerivAt_deriv_exponentialWeight_variation
    {ε θ η : ℝ → ℝ} {ℓ β : ℝ} (hβ : β ≠ 0)
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 2 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η) :
    HasDerivAt (deriv (fun t => exponentialWeight β ε (angleVariation θ η t) ℓ))
      (β ^ 2 * exponentialWeight β ε θ ℓ *
          (∫ s in 0..ℓ, deriv ε (deriv θ s) * deriv η s) ^ 2 -
        β * exponentialWeight β ε θ ℓ *
          (∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η s) ^ 2)) 0 := by
  have hzero : angleVariation θ η 0 = θ := by
    funext s
    simp only [angleVariation, zero_mul, add_zero]
  simpa only [exponentialWeight, hzero] using hasDerivAt_deriv_exp_neg_mul hβ
    (hasDerivAt_energy_variation hℓ (hε.of_le (by norm_num)) hθ hη)
    (hasDerivAt_deriv_energy_variation hℓ hε hθ hη)

/-- Any actual stationary energy path, in particular an exact admissible family,
has the stated weighted second derivative. The input `hsecond` is a derivative
of the actual energy path, not a separately defined quadratic expression. -/
theorem hasDerivAt_deriv_exponentialWeight_family_of_stationary
    {ε : ℝ → ℝ} {Θ : ℝ → ℝ → ℝ} {ℓ x q β : ℝ} (hβ : β ≠ 0)
    (hfirst : HasDerivAt (fun t => energy ε (Θ t) ℓ) 0 x)
    (hsecond : HasDerivAt (deriv (fun t => energy ε (Θ t) ℓ)) q x) :
    HasDerivAt (deriv (fun t => exponentialWeight β ε (Θ t) ℓ))
      (-β * exponentialWeight β ε (Θ x) ℓ * q) x :=
  hasDerivAt_deriv_exp_neg_mul_of_stationary hβ hfirst hsecond

/-- On the existing exact constrained corrected family, stationarity removes
both the first-derivative square and the acceleration terms. The constrained
second variation is therefore multiplied by `-β * exponentialWeight β ε θ ℓ`.
The exact displacement hypotheses are used to derive first-order feasibility;
that feasibility is not separately assumed. -/
theorem constrained_secondVariation_exponentialWeight_corrected
    {ε θ a b : ℝ → ℝ} {ℓ lam μ β : ℝ} (hβ : β ≠ 0)
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 2 ε) (hθ : ContDiff ℝ 1 θ)
    (η ξ₁ ξ₂ : variationSpace ℓ)
    (ha : ContDiffAt ℝ 2 a 0) (hb : ContDiffAt ℝ 2 b 0)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (ha1 : deriv a 0 = 0) (hb1 : deriv b 0 = 0)
    (hx : (fun t => ∫ s in 0..ℓ,
      cos (θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s)) =ᶠ[𝓝 0]
        fun _ => ∫ s in 0..ℓ, cos (θ s))
    (hy : (fun t => ∫ s in 0..ℓ,
      sin (θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s)) =ᶠ[𝓝 0]
        fun _ => ∫ s in 0..ℓ, sin (θ s))
    (hstat : ∀ ζ : variationSpace ℓ,
      (∫ s in 0..ℓ, deriv ε (deriv θ s) * deriv ζ.val s) +
        lam * (∫ s in 0..ℓ, -sin (θ s) * ζ.val s) +
        μ * (∫ s in 0..ℓ, cos (θ s) * ζ.val s) = 0) :
    HasDerivAt (deriv (fun t => exponentialWeight β ε
      (fun s => θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s) ℓ))
      (-β * exponentialWeight β ε θ ℓ *
        (∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η.val s)^2 -
          (lam * cos (θ s) + μ * sin (θ s)) * (η.val s)^2)) 0 := by
  have hdx := (hasDerivAt_corrected_integral_and_deriv (ε := cos) hℓ contDiff_cos
    hθ.continuous η.property.1.continuous ξ₁.property.1.continuous ξ₂.property.1.continuous
    ha hb ha0 hb0 ha1 hb1).1
  have hdy := (hasDerivAt_corrected_integral_and_deriv (ε := sin) hℓ contDiff_sin
    hθ.continuous η.property.1.continuous ξ₁.property.1.continuous ξ₂.property.1.continuous
    ha hb ha0 hb0 ha1 hb1).1
  have hxI : (∫ s in 0..ℓ, -sin (θ s) * η.val s) = 0 := by
    have h := hdx.deriv
    rw [hx.deriv_eq] at h
    simpa only [Real.deriv_cos, deriv_const] using h.symm
  have hyI : (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0 := by
    have h := hdy.deriv
    rw [hy.deriv_eq] at h
    simpa only [Real.deriv_sin, deriv_const] using h.symm
  have hz : (∫ s in 0..ℓ, deriv ε (deriv θ s) * deriv η.val s) = 0 := by
    simpa only [hxI, hyI, mul_zero, add_zero] using hstat η
  have he := (hasDerivAt_corrected_energy_and_deriv hℓ hε hθ η.property.1
    ξ₁.property.1 ξ₂.property.1 ha hb ha0 hb0 ha1 hb1).1
  rw [hz] at he
  have hsecond := constrained_secondVariation_corrected hℓ hε hθ η.property.1
    ξ₁ ξ₂ ha hb ha0 hb0 ha1 hb1 hx hy hstat
  have h := hasDerivAt_deriv_exponentialWeight_family_of_stationary hβ he hsecond
  simpa only [ha0, hb0, zero_mul, add_zero] using h

end Elastica
