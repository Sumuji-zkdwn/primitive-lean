import Elastica.Stationary
import Elastica.Variation
import Mathlib.Topology.Order.LocalExtr

/-!
# C¹ local minima and exact finite-parameter families

The local-minimum hypothesis compares the actual curvature energy on C¹ angles
with the same lifted endpoint angles and exact endpoint displacement integrals.
The neighborhood controls both the angle and its derivative on the compact
interval.  Compact bounds make a continuous finite-parameter correction small
in this neighborhood.  No local-minimum hypothesis is imposed separately on
the scalar energy path.
-/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace Elastica

/-- A C¹ local minimum among angles with exactly the same endpoint data.
All functions are the same global representatives used by the existing library. -/
def LocallyMinimizing (ε θ : ℝ → ℝ) (ℓ : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ →
    ψ 0 = θ 0 → ψ ℓ = θ ℓ →
    (∫ s in 0..ℓ, cos (ψ s)) = (∫ s in 0..ℓ, cos (θ s)) →
    (∫ s in 0..ℓ, sin (ψ s)) = (∫ s in 0..ℓ, sin (θ s)) →
    (∀ s ∈ Icc 0 ℓ,
      |ψ s - θ s| < r ∧ |deriv ψ s - deriv θ s| < r) →
    energy ε θ ℓ ≤ energy ε ψ ℓ

private theorem abs_three_term_bound {t a b u v w C : ℝ}
    (hu : |u| ≤ C) (hv : |v| ≤ C) (hw : |w| ≤ C) :
    |t * u + a * v + b * w| ≤ (|t| + |a| + |b|) * C := by
  calc
    _ ≤ |t * u + a * v| + |b * w| := abs_add_le _ _
    _ ≤ |t * u| + |a * v| + |b * w| := add_le_add (abs_add_le _ _) le_rfl
    _ = |t| * |u| + |a| * |v| + |b| * |w| := by simp only [abs_mul]
    _ ≤ |t| * C + |a| * C + |b| * C :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hu (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hv (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hw (abs_nonneg _))
    _ = _ := by ring

/-- A continuous finite-parameter correction tending to zero tends to the base
angle in the C¹ neighborhood on the fixed compact interval. -/
theorem corrected_family_C1_close {θ : ℝ → ℝ} {ℓ : ℝ}
    (hθ : ContDiff ℝ 1 θ) (η ξ₁ ξ₂ : variationSpace ℓ)
    {a b : ℝ → ℝ} (ha : ContinuousAt a 0) (hb : ContinuousAt b 0)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ s ∈ Icc 0 ℓ,
      |(θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s) - θ s| < r ∧
      |deriv (fun u => θ u + t * η.val u + a t * ξ₁.val u + b t * ξ₂.val u) s -
        deriv θ s| < r := by
  let G : ℝ → ℝ := fun s =>
    |η.val s| + |deriv η.val s| + |ξ₁.val s| + |deriv ξ₁.val s| +
      |ξ₂.val s| + |deriv ξ₂.val s|
  have hG : Continuous G :=
    ((((η.property.1.continuous.abs.add η.property.1.continuous_deriv_one.abs).add
      ξ₁.property.1.continuous.abs).add ξ₁.property.1.continuous_deriv_one.abs).add
        ξ₂.property.1.continuous.abs).add ξ₂.property.1.continuous_deriv_one.abs
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) ℓ)).exists_bound_of_continuousOn
    hG.continuousOn
  have hbounds (s : ℝ) (hs : s ∈ Icc 0 ℓ) :
      |η.val s| ≤ C ∧ |deriv η.val s| ≤ C ∧
      |ξ₁.val s| ≤ C ∧ |deriv ξ₁.val s| ≤ C ∧
      |ξ₂.val s| ≤ C ∧ |deriv ξ₂.val s| ≤ C := by
    have hg : G s ≤ C := (le_abs_self (G s)).trans (by
      simpa only [Real.norm_eq_abs] using hC s hs)
    dsimp [G] at hg
    have h₁ := abs_nonneg (η.val s)
    have h₂ := abs_nonneg (deriv η.val s)
    have h₃ := abs_nonneg (ξ₁.val s)
    have h₄ := abs_nonneg (deriv ξ₁.val s)
    have h₅ := abs_nonneg (ξ₂.val s)
    have h₆ := abs_nonneg (deriv ξ₂.val s)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hcont : ContinuousAt (fun t : ℝ => (|t| + |a t| + |b t|) * C) 0 :=
    ((continuousAt_id.abs.add ha.abs).add hb.abs).mul continuousAt_const
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), (|t| + |a t| + |b t|) * C < r :=
    hcont.eventually (Iio_mem_nhds (by simpa [ha0, hb0] using hr))
  filter_upwards [hsmall] with t ht
  intro s hs
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hbounds s hs
  have hd : deriv (fun u => θ u + t * η.val u + a t * ξ₁.val u + b t * ξ₂.val u) s =
      deriv θ s + t * deriv η.val s + a t * deriv ξ₁.val s + b t * deriv ξ₂.val s :=
    ((((hθ.differentiable one_ne_zero s).hasDerivAt.add
      ((η.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul t)).add
        ((ξ₁.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul (a t))).add
          ((ξ₂.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul (b t))).deriv
  constructor
  · have he : θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s - θ s =
        t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s := by ring
    rw [he]
    exact (abs_three_term_bound h₁ h₃ h₅).trans_lt ht
  · rw [hd]
    have he : deriv θ s + t * deriv η.val s + a t * deriv ξ₁.val s +
        b t * deriv ξ₂.val s - deriv θ s =
        t * deriv η.val s + a t * deriv ξ₁.val s + b t * deriv ξ₂.val s := by ring
    rw [he]
    exact (abs_three_term_bound h₂ h₄ h₆).trans_lt ht

/-- A C¹ local minimum of the constrained energy induces a scalar local minimum
on every exact corrected family with continuous coefficients vanishing at zero.
The hypotheses from a C² implicit-function correction are therefore sufficient. -/
theorem locallyMinimizing_isLocalMin_corrected_family {ε θ : ℝ → ℝ} {ℓ : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hmin : LocallyMinimizing ε θ ℓ)
    (η ξ₁ ξ₂ : variationSpace ℓ) {a b : ℝ → ℝ}
    (ha : ContinuousAt a 0) (hb : ContinuousAt b 0)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (hexact : ∀ᶠ t in 𝓝 (0 : ℝ),
      (∫ s in 0..ℓ, cos (θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s)) =
        (∫ s in 0..ℓ, cos (θ s)) ∧
      (∫ s in 0..ℓ, sin (θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s)) =
        (∫ s in 0..ℓ, sin (θ s))) :
    IsLocalMin (fun t => energy ε
      (fun s => θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s) ℓ) 0 := by
  obtain ⟨r, hr, hminimal⟩ := hmin
  have hclose := corrected_family_C1_close hθ η ξ₁ ξ₂ ha hb ha0 hb0 hr
  change ∀ᶠ t in 𝓝 (0 : ℝ),
    energy ε (fun s => θ s + 0 * η.val s + a 0 * ξ₁.val s + b 0 * ξ₂.val s) ℓ ≤ _
  simp only [ha0, hb0, zero_mul, add_zero]
  filter_upwards [hclose, hexact] with t ht hx
  apply hminimal (fun s => θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s)
  · exact ((hθ.add (contDiff_const.mul η.property.1)).add
      (contDiff_const.mul ξ₁.property.1)).add (contDiff_const.mul ξ₂.property.1)
  · simp only [η.property.2.1, ξ₁.property.2.1, ξ₂.property.2.1, mul_zero, add_zero]
  · simp only [η.property.2.2, ξ₁.property.2.2, ξ₂.property.2.2, mul_zero, add_zero]
  · exact hx.1
  · exact hx.2
  · exact ht

end Elastica
