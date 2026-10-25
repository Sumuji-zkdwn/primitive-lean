import Elastica.Composition
import Elastica.ExponentialWeight
import Elastica.LocalMinimum

/-!
# Middle replacement, exponential comparison, and local minimality

This file composes the existing restriction, boundary, energy, and weight
theorems. Replacements are already globally C¹ angle functions; existence of a
smooth gluing is not asserted. Exact matching of the middle displacement
integrals derives global feasibility. Closeness on the middle interval alone
suffices for the local comparison because the exterior angles agree.
-/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology

namespace Elastica

private theorem deriv_eqOn_closed_interval {θ φ : ℝ → ℝ} {a b : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hφ : ContDiff ℝ 1 φ) (hab : a < b)
    (hEq : EqOn θ φ (Icc a b)) : EqOn (deriv θ) (deriv φ) (Icc a b) := by
  have hi : EqOn θ φ (Ioo a b) := fun _ hs => hEq ⟨hs.1.le, hs.2.le⟩
  have hd := hi.deriv isOpen_Ioo
  have hc := hd.closure hθ.continuous_deriv_one hφ.continuous_deriv_one
  simpa only [closure_Ioo hab.ne] using hc

private theorem C1_close_of_middle_close {θ φ : ℝ → ℝ} {a b ℓ r : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hφ : ContDiff ℝ 1 φ) (hr : 0 < r)
    (hleft : EqOn θ φ (Icc 0 a)) (hright : EqOn θ φ (Icc b ℓ))
    (hclose : ∀ s ∈ Icc a b,
      |φ s - θ s| < r ∧ |deriv φ s - deriv θ s| < r) :
    ∀ s ∈ Icc 0 ℓ, |φ s - θ s| < r ∧ |deriv φ s - deriv θ s| < r := by
  intro s hs
  by_cases hsa : s < a
  · have hsa' : s ∈ Icc 0 a := ⟨hs.1, hsa.le⟩
    have he := hleft hsa'
    have hd := deriv_eqOn_closed_interval hθ hφ (hs.1.trans_lt hsa) hleft hsa'
    simpa only [← he, ← hd, sub_self, abs_zero, and_self] using hr
  · by_cases hbs : b < s
    · have hbs' : s ∈ Icc b ℓ := ⟨hbs.le, hs.2⟩
      have he := hright hbs'
      have hd := deriv_eqOn_closed_interval hθ hφ (hbs.trans_le hs.2) hright hbs'
      simpa only [← he, ← hd, sub_self, abs_zero, and_self] using hr
    · exact hclose s ⟨le_of_not_gt hsa, le_of_not_gt hbs⟩

/-- The original boundary data are preserved, and the ratio of whole-curve
weights depends only on the middle energy difference. No sign on `β` or on the
energy is needed for this identity. -/
theorem middle_replacement_boundary_and_weight_ratio
    {ε θ φ : ℝ → ℝ} {a b ℓ : ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (hφ : ContDiff ℝ 1 φ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ℓ)
    (hleft : EqOn θ φ (Icc 0 a)) (hright : EqOn θ φ (Icc b ℓ))
    (hx : (∫ s in a..b, cos (θ s)) = ∫ s in a..b, cos (φ s))
    (hy : (∫ s in a..b, sin (θ s)) = ∫ s in a..b, sin (φ s))
    (β x₀ y₀ : ℝ) :
    (θ 0 = φ 0 ∧ θ ℓ = φ ℓ ∧
      xCoord θ x₀ ℓ = xCoord φ x₀ ℓ ∧ yCoord θ y₀ ℓ = yCoord φ y₀ ℓ) ∧
    exponentialWeight β ε φ ℓ / exponentialWeight β ε θ ℓ =
      exp (-β * ((∫ s in a..b, ε (deriv φ s)) -
        (∫ s in a..b, ε (deriv θ s)))) := by
  refine ⟨boundary_eq_of_middle_integrals hθ.continuous hφ.continuous
    ha hab hb hleft hright hx hy x₀ y₀, ?_⟩
  have henergy := energy_sub_eq_middle_of_outer_angle_eq
    hε hθ hφ ha hab hb hleft hright
  rw [exponentialWeight, exponentialWeight, ← exp_sub, ← mul_sub, henergy]

/-- With the exterior fixed, strict improvement of the middle energy is
equivalent to strict increase of the whole-curve weight. Feasibility follows
from the preceding theorem when the two middle displacements also match. -/
theorem middle_energy_lt_iff_exponentialWeight_lt
    {ε θ φ : ℝ → ℝ} {a b ℓ β : ℝ} (hβ : 0 < β)
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ) (hφ : ContDiff ℝ 1 φ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ℓ)
    (hleft : EqOn θ φ (Icc 0 a)) (hright : EqOn θ φ (Icc b ℓ)) :
    (∫ s in a..b, ε (deriv φ s)) < (∫ s in a..b, ε (deriv θ s)) ↔
      exponentialWeight β ε θ ℓ < exponentialWeight β ε φ ℓ := by
  have henergy := energy_sub_eq_middle_of_outer_angle_eq
    hε hθ hφ ha hab hb hleft hright
  rw [← energy_lt_iff_exponentialWeight_lt hβ]
  constructor <;> intro h <;> linarith

/-- A whole-curve C¹ local minimum cannot be improved by sufficiently small
smooth middle replacements preserving middle displacement. Only middle C¹
closeness is required: exterior derivative agreement and all global endpoint
conditions are derived. The same replacement cannot increase the whole weight. -/
theorem locallyMinimizing_middle_replacement_comparison
    {ε θ : ℝ → ℝ} {a b ℓ β : ℝ} (hβ : 0 < β)
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ℓ)
    (hmin : LocallyMinimizing ε θ ℓ) :
    ∃ r : ℝ, 0 < r ∧ ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ →
      EqOn θ φ (Icc 0 a) → EqOn θ φ (Icc b ℓ) →
      (∫ s in a..b, cos (θ s)) = (∫ s in a..b, cos (φ s)) →
      (∫ s in a..b, sin (θ s)) = (∫ s in a..b, sin (φ s)) →
      (∀ s ∈ Icc a b, |φ s - θ s| < r ∧ |deriv φ s - deriv θ s| < r) →
      (∫ s in a..b, ε (deriv θ s)) ≤ (∫ s in a..b, ε (deriv φ s)) ∧
        exponentialWeight β ε φ ℓ ≤ exponentialWeight β ε θ ℓ := by
  obtain ⟨r, hr, hminimal⟩ := hmin
  refine ⟨r, hr, ?_⟩
  intro φ hφ hleft hright hx hy hclose
  obtain ⟨hzero, hend, hxglobal, hyglobal⟩ := boundary_eq_of_middle_integrals
    hθ.continuous hφ.continuous ha hab hb hleft hright hx hy 0 0
  have hcos : (∫ s in 0..ℓ, cos (φ s)) = ∫ s in 0..ℓ, cos (θ s) := by
    simpa only [xCoord, zero_add] using hxglobal.symm
  have hsin : (∫ s in 0..ℓ, sin (φ s)) = ∫ s in 0..ℓ, sin (θ s) := by
    simpa only [yCoord, zero_add] using hyglobal.symm
  have he := hminimal φ hφ hzero.symm hend.symm hcos hsin
    (C1_close_of_middle_close hθ hφ hr hleft hright hclose)
  have henergy := energy_sub_eq_middle_of_outer_angle_eq
    hε hθ hφ ha hab hb hleft hright
  exact ⟨by linarith, (energy_le_iff_exponentialWeight_le hβ ε θ φ ℓ).mp he⟩

/-- Arbitrarily small C¹ middle improvements exclude a constrained local
minimum of the whole curve. The hypothesis supplies actual globally smooth
replacements and their exact displacement matching, not just formal directions. -/
theorem not_locallyMinimizing_of_arbitrarily_close_middle_improvements
    {ε θ : ℝ → ℝ} {a b ℓ : ℝ}
    (hε : Continuous ε) (hθ : ContDiff ℝ 1 θ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ℓ)
    (himprove : ∀ r : ℝ, 0 < r → ∃ φ : ℝ → ℝ,
      ContDiff ℝ 1 φ ∧ EqOn θ φ (Icc 0 a) ∧ EqOn θ φ (Icc b ℓ) ∧
      (∫ s in a..b, cos (θ s)) = (∫ s in a..b, cos (φ s)) ∧
      (∫ s in a..b, sin (θ s)) = (∫ s in a..b, sin (φ s)) ∧
      (∀ s ∈ Icc a b, |φ s - θ s| < r ∧ |deriv φ s - deriv θ s| < r) ∧
      (∫ s in a..b, ε (deriv φ s)) < (∫ s in a..b, ε (deriv θ s))) :
    ¬ LocallyMinimizing ε θ ℓ := by
  intro hmin
  obtain ⟨r, hr, hcompare⟩ := locallyMinimizing_middle_replacement_comparison
    (β := 1) zero_lt_one hε hθ ha hab hb hmin
  obtain ⟨φ, hφ, hleft, hright, hx, hy, hclose, himproved⟩ := himprove r hr
  exact (not_lt_of_ge (hcompare φ hφ hleft hright hx hy hclose).1) himproved

end Elastica
