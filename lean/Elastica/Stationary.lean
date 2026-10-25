import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-! Fixed-end C¹ variations, finite-codimensional multipliers, and the
fundamental lemma used for the classical angle equation. -/

noncomputable section
open Real Set MeasureTheory
open scoped Topology Interval
namespace Elastica

/-- Vanishing on the kernel of two linear constraints gives two multipliers.
No rank or independence assumption is needed for this implication. -/
theorem exists_multipliers_of_kernel
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f c₁ c₂ : V →ₗ[ℝ] ℝ)
    (h : ∀ v, c₁ v = 0 → c₂ v = 0 → f v = 0) :
    ∃ lam μ : ℝ, ∀ v, f v + lam * c₁ v + μ * c₂ v = 0 := by
  let c : V →ₗ[ℝ] ℝ × ℝ := c₁.prod c₂
  have hf : f ∈ (LinearMap.ker c).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    have hv' : c v = 0 := hv
    exact h v (congrArg Prod.fst hv') (congrArg Prod.snd hv')
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hf
  obtain ⟨g, hg⟩ := hf
  refine ⟨-g (1, 0), -g (0, 1), ?_⟩
  intro v
  have hgv : g (c v) = f v := DFunLike.congr_fun hg v
  have hc : c v = (c₁ v) • (1, 0) + (c₂ v) • (0, 1) := by
    ext <;> simp [c]
  rw [hc, map_add, map_smul, map_smul] at hgv
  simp only [smul_eq_mul] at hgv
  nlinarith

/-- Globally C¹ representatives of fixed-end angle variations.
Only their restrictions to [0,ℓ] enter the integrals. -/
def variationSpace (ℓ : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {η | ContDiff ℝ 1 η ∧ η 0 = 0 ∧ η ℓ = 0}
  zero_mem' := ⟨contDiff_const, rfl, rfl⟩
  add_mem' := by
    intro η ξ hη hξ
    exact ⟨hη.1.add hξ.1, by simp [hη.2.1, hξ.2.1], by simp [hη.2.2, hξ.2.2]⟩
  smul_mem' := by
    intro a η hη
    exact ⟨hη.1.const_smul a, by simp [hη.2.1], by simp [hη.2.2]⟩

/-- A weighted endpoint-displacement derivative. -/
def constraintLinear (ℓ : ℝ) (w : ℝ → ℝ) (hw : Continuous w) :
    variationSpace ℓ →ₗ[ℝ] ℝ where
  toFun η := ∫ s in 0..ℓ, w s * η.val s
  map_add' η ξ := by
    change (∫ s in 0..ℓ, w s * (η.val s + ξ.val s)) = _
    simp_rw [mul_add]
    exact intervalIntegral.integral_add
      ((hw.mul η.property.1.continuous).intervalIntegrable _ _)
      ((hw.mul ξ.property.1.continuous).intervalIntegrable _ _)
  map_smul' a η := by
    change (∫ s in 0..ℓ, w s * (a * η.val s)) = a * _
    simp_rw [show ∀ s, w s * (a * η.val s) = a * (w s * η.val s) by intro s; ring]
    exact intervalIntegral.integral_const_mul _ _

/-- The first-variation integral as a linear functional of the variation. -/
def firstVariationLinear (ℓ : ℝ) (M : ℝ → ℝ) (hM : Continuous M) :
    variationSpace ℓ →ₗ[ℝ] ℝ where
  toFun η := ∫ s in 0..ℓ, M s * deriv η.val s
  map_add' η ξ := by
    change (∫ s in 0..ℓ, M s * deriv (η.val + ξ.val) s) = _
    have hd : ∀ s, deriv (η.val + ξ.val) s = deriv η.val s + deriv ξ.val s := by
      intro s
      exact deriv_add (η.property.1.differentiable one_ne_zero s)
        (ξ.property.1.differentiable one_ne_zero s)
    simp_rw [hd, mul_add]
    exact intervalIntegral.integral_add
      ((hM.mul η.property.1.continuous_deriv_one).intervalIntegrable _ _)
      ((hM.mul ξ.property.1.continuous_deriv_one).intervalIntegrable _ _)
  map_smul' a η := by
    change (∫ s in 0..ℓ, M s * deriv (a • η.val) s) = a * _
    have hd : ∀ s, deriv (a • η.val) s = a * deriv η.val s := by
      intro s
      exact deriv_const_mul a (η.property.1.differentiable one_ne_zero s)
    simp_rw [hd]
    simp_rw [show ∀ s, M s * (a * deriv η.val s) = a * (M s * deriv η.val s) by
      intro s; ring]
    exact intervalIntegral.integral_const_mul _ _

/-- The multiplier theorem for the actual elastica integral functionals. -/
theorem stationary_multipliers {ℓ : ℝ} {θ M : ℝ → ℝ}
    (hθ : Continuous θ) (hM : Continuous M)
    (hstat : ∀ η : variationSpace ℓ,
      (∫ s in 0..ℓ, -sin (θ s) * η.val s) = 0 →
      (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0 →
      (∫ s in 0..ℓ, M s * deriv η.val s) = 0) :
    ∃ lam μ : ℝ, ∀ η : variationSpace ℓ,
      (∫ s in 0..ℓ, M s * deriv η.val s) +
      lam * (∫ s in 0..ℓ, -sin (θ s) * η.val s) +
      μ * (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0 := by
  exact exists_multipliers_of_kernel (firstVariationLinear ℓ M hM)
    (constraintLinear ℓ (fun s => -sin (θ s)) (Real.continuous_sin.comp hθ).neg)
    (constraintLinear ℓ (fun s => cos (θ s)) (Real.continuous_cos.comp hθ)) hstat

/-- Weighted square form of the fundamental lemma, with explicit positivity. -/
theorem residual_zero_of_weighted_square_integral {ℓ : ℝ} {r : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hr : Continuous r)
    (hint : (∫ s in 0..ℓ, s * (ℓ - s) * (r s) ^ 2) = 0) :
    ∀ s ∈ Ioo 0 ℓ, r s = 0 := by
  intro s hs
  by_contra hne
  have hcont : Continuous (fun t : ℝ => t * (ℓ - t) * (r t) ^ 2) := by fun_prop
  have hpos : 0 < ∫ t in 0..ℓ, t * (ℓ - t) * (r t) ^ 2 := by
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hℓ continuousOn_const hcont.continuousOn
      (fun t ht => mul_nonneg (mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)) (sq_nonneg _))
      ⟨s, ⟨hs.1.le, hs.2.le⟩, mul_pos (mul_pos hs.1 (sub_pos.mpr hs.2)) (sq_pos_of_ne_zero hne)⟩
    simpa using h
  linarith

/-- Integration by parts with the two fixed-end boundary terms removed. -/
theorem firstVariation_by_parts {ℓ : ℝ} {M : ℝ → ℝ}
    (hM : ContDiff ℝ 1 M) (η : variationSpace ℓ) :
    (∫ s in 0..ℓ, M s * deriv η.val s) =
      -(∫ s in 0..ℓ, deriv M s * η.val s) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun s _ => (hM.differentiable one_ne_zero s).hasDerivAt)
    (fun s _ => (η.property.1.differentiable one_ne_zero s).hasDerivAt)
    (hM.continuous_deriv_one.intervalIntegrable 0 ℓ)
    (η.property.1.continuous_deriv_one.intervalIntegrable 0 ℓ)
  simpa [η.property.2.1, η.property.2.2] using h

/-- Combining the two terms of a first variation into its Euler residual. -/
theorem augmented_integral_eq_residual {ℓ : ℝ} {M q : ℝ → ℝ}
    (hM : ContDiff ℝ 1 M) (hq : Continuous q) (η : variationSpace ℓ) :
    (∫ s in 0..ℓ, M s * deriv η.val s) + (∫ s in 0..ℓ, q s * η.val s) =
      ∫ s in 0..ℓ, (-deriv M s + q s) * η.val s := by
  rw [firstVariation_by_parts hM η]
  simp_rw [add_mul, neg_mul]
  have he := intervalIntegral.integral_add
    (μ := volume) (a := 0) (b := ℓ)
    (f := fun s => -(deriv M s * η.val s)) (g := fun s => q s * η.val s)
    ((hM.continuous_deriv_one.mul η.property.1.continuous).neg.intervalIntegrable _ _)
    ((hq.mul η.property.1.continuous).intervalIntegrable _ _)
  simpa only [intervalIntegral.integral_neg] using he.symm

/-- The residual-derived test function is C¹ and has zero endpoint values.
This is the step that keeps the fundamental lemma within the stated variation family. -/
theorem residual_zero_of_augmented_stationary {ℓ : ℝ} {M q : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hM : ContDiff ℝ 2 M) (hq : ContDiff ℝ 1 q)
    (hstat : ∀ η : variationSpace ℓ,
      (∫ s in 0..ℓ, M s * deriv η.val s) + (∫ s in 0..ℓ, q s * η.val s) = 0) :
    ∀ s ∈ Ioo 0 ℓ, deriv M s = q s := by
  let r : ℝ → ℝ := fun s => -deriv M s + q s
  have hr : ContDiff ℝ 1 r := (hM.deriv').neg.add hq
  let η : variationSpace ℓ :=
    ⟨fun s => s * (ℓ - s) * r s,
      ⟨(contDiff_id.mul (contDiff_const.sub contDiff_id)).mul hr, by simp, by simp⟩⟩
  have hint := hstat η
  rw [augmented_integral_eq_residual (hM.of_le (by norm_num)) hq.continuous η] at hint
  have hint' : (∫ s in 0..ℓ, s * (ℓ - s) * (r s) ^ 2) = 0 := by
    convert hint using 1
    apply intervalIntegral.integral_congr
    intro s _
    change s * (ℓ - s) * (r s) ^ 2 = r s * (s * (ℓ - s) * r s)
    ring
  have hz := residual_zero_of_weighted_square_integral hℓ hr.continuous hint'
  intro s hs
  have := hz s hs
  dsimp [r] at this
  linarith

/-- The converse integration-by-parts implication needs only C¹ for M.
Equality on the interior extends to the endpoints by continuity. -/
theorem augmented_stationary_of_residual_zero {ℓ : ℝ} {M q : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hM : ContDiff ℝ 1 M) (hq : Continuous q)
    (hEL : ∀ s ∈ Ioo 0 ℓ, deriv M s = q s) :
    ∀ η : variationSpace ℓ,
      (∫ s in 0..ℓ, M s * deriv η.val s) + (∫ s in 0..ℓ, q s * η.val s) = 0 := by
  have hcc : EqOn (deriv M) q (Icc 0 ℓ) := by
    have hh : EqOn (deriv M) q (Ioo 0 ℓ) := hEL
    have hc := hh.closure hM.continuous_deriv_one hq
    simpa only [closure_Ioo hℓ.ne] using hc
  intro η
  rw [augmented_integral_eq_residual hM hq η]
  calc
    _ = ∫ s in 0..ℓ, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hℓ.le] at hs
      change (-deriv M s + q s) * η.val s = 0
      rw [hcc hs]
      ring
    _ = 0 := by simp

/-- For this smoothness class the integral condition and angle residual are equivalent. -/
theorem augmented_stationary_iff_residual_zero {ℓ : ℝ} {M q : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hM : ContDiff ℝ 2 M) (hq : ContDiff ℝ 1 q) :
    (∀ η : variationSpace ℓ,
      (∫ s in 0..ℓ, M s * deriv η.val s) + (∫ s in 0..ℓ, q s * η.val s) = 0) ↔
      ∀ s ∈ Ioo 0 ℓ, deriv M s = q s :=
  ⟨residual_zero_of_augmented_stationary hℓ hM hq,
    augmented_stationary_of_residual_zero hℓ (hM.of_le (by norm_num)) hq.continuous⟩

/-- The integrated force term is the linear combination of endpoint constraints. -/
theorem force_integral {ℓ lam μ : ℝ} {θ : ℝ → ℝ}
    (hθ : Continuous θ) (η : variationSpace ℓ) :
    (∫ s in 0..ℓ, (-lam * sin (θ s) + μ * cos (θ s)) * η.val s) =
      lam * (∫ s in 0..ℓ, -sin (θ s) * η.val s) +
      μ * (∫ s in 0..ℓ, cos (θ s) * η.val s) := by
  have hi₁ : IntervalIntegrable (fun s => lam * (-sin (θ s) * η.val s)) volume 0 ℓ :=
    (continuous_const.mul ((Real.continuous_sin.comp hθ).neg.mul η.property.1.continuous)).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun s => μ * (cos (θ s) * η.val s)) volume 0 ℓ :=
    (continuous_const.mul ((Real.continuous_cos.comp hθ).mul η.property.1.continuous)).intervalIntegrable _ _
  calc
    _ = ∫ s in 0..ℓ,
        lam * (-sin (θ s) * η.val s) + μ * (cos (θ s) * η.val s) := by
      apply intervalIntegral.integral_congr
      intro s _
      ring
    _ = _ := by rw [intervalIntegral.integral_add hi₁ hi₂,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- Concrete constrained stationarity implies the classical angle equation. -/
theorem angleEquation_of_stationary {ℓ : ℝ} {θ M : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ) (hM : ContDiff ℝ 2 M)
    (hstat : ∀ η : variationSpace ℓ,
      (∫ s in 0..ℓ, -sin (θ s) * η.val s) = 0 →
      (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0 →
      (∫ s in 0..ℓ, M s * deriv η.val s) = 0) :
    ∃ lam μ : ℝ, ∀ s ∈ Ioo 0 ℓ,
      deriv M s = -lam * sin (θ s) + μ * cos (θ s) := by
  obtain ⟨lam, μ, hm⟩ := stationary_multipliers hθ.continuous hM.continuous hstat
  refine ⟨lam, μ, residual_zero_of_augmented_stationary hℓ hM
    ((contDiff_const.mul hθ.sin).add (contDiff_const.mul hθ.cos)) ?_⟩
  intro η
  rw [force_integral hθ.continuous η]
  linarith [hm η]

/-- A solution of the angle equation is stationary under the linearized constraints. -/
theorem stationary_of_angleEquation {ℓ lam μ : ℝ} {θ M : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hθ : Continuous θ) (hM : ContDiff ℝ 1 M)
    (hEL : ∀ s ∈ Ioo 0 ℓ, deriv M s = -lam * sin (θ s) + μ * cos (θ s)) :
    ∀ η : variationSpace ℓ,
      (∫ s in 0..ℓ, -sin (θ s) * η.val s) = 0 →
      (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0 →
      (∫ s in 0..ℓ, M s * deriv η.val s) = 0 := by
  have hq : Continuous (fun s => -lam * sin (θ s) + μ * cos (θ s)) :=
    (continuous_const.mul (Real.continuous_sin.comp hθ)).add
      (continuous_const.mul (Real.continuous_cos.comp hθ))
  intro η hx hy
  have h := augmented_stationary_of_residual_zero hℓ hM hq hEL η
  rw [force_integral hθ η, hx, hy] at h
  simpa using h

/-- Full equivalence with the linearized fixed-position constraints.
It says neither that a stationary curve minimizes energy nor that admissible
curves exist for arbitrary boundary data. -/
theorem stationary_iff_exists_angleEquation {ℓ : ℝ} {θ M : ℝ → ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ) (hM : ContDiff ℝ 2 M) :
    (∀ η : variationSpace ℓ,
      (∫ s in 0..ℓ, -sin (θ s) * η.val s) = 0 →
      (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0 →
      (∫ s in 0..ℓ, M s * deriv η.val s) = 0) ↔
    (∃ lam μ : ℝ, ∀ s ∈ Ioo 0 ℓ,
      deriv M s = -lam * sin (θ s) + μ * cos (θ s)) := by
  constructor
  · exact angleEquation_of_stationary hℓ hθ hM
  · rintro ⟨lam, μ, hEL⟩
    exact stationary_of_angleEquation hℓ hθ.continuous (hM.of_le (by norm_num)) hEL

end Elastica
