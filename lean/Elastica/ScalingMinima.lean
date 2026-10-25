import Elastica.Scaling
import Elastica.ExponentialWeight

/-!
# Similarities transport constrained local minima

The energy scaling law alone compares values.  Here its positive multiplier
is combined with the inverse reparametrization and an explicit C¹ neighborhood
bound to transport the existing constrained local-minimum predicate.  The
length and endpoint displacements scale with the curve; the real endpoint
angles do not change.  Density homogeneity is an additional hypothesis.
-/

noncomputable section
open Real Set MeasureTheory

namespace Elastica

/-- A positive density multiplier transports a C¹ constrained local minimum.
The proof pulls every nearby scaled competitor back to the original interval.
If the original radius is `r`, the scaled radius `r / (a + 1)` suffices. -/
theorem locallyMinimizing_scaling_of_density_factor {ε θ : ℝ → ℝ}
    {a c ℓ : ℝ} (ha : 0 < a) (hc : 0 < c) (hθ : ContDiff ℝ 1 θ)
    (hε : ∀ q, ε (q / a) = c * ε q)
    (hmin : LocallyMinimizing ε θ ℓ) :
    LocallyMinimizing ε (fun s => θ (s / a)) (a * ℓ) := by
  obtain ⟨r, hr, hmin⟩ := hmin
  let δ := r / (a + 1)
  have hδ : 0 < δ := div_pos hr (by linarith)
  have hδr : δ < r := (div_lt_iff₀ (by linarith : 0 < a + 1)).mpr (by nlinarith)
  have haδr : a * δ < r := by
    have he : δ * (a + 1) = r := div_mul_cancel₀ r (by linarith : a + 1 ≠ 0)
    nlinarith
  refine ⟨δ, hδ, ?_⟩
  intro ψ hψ hψ0 hψℓ hx hy hclose
  let φ : ℝ → ℝ := fun s => ψ (s / a⁻¹)
  have hφ : ContDiff ℝ 1 φ := contDiff_angle_scaling hψ a⁻¹
  have hround : (fun s => φ (s / a)) = ψ := by
    funext s
    simp [φ, ha.ne']
  have hθdiff := hθ.differentiable one_ne_zero
  have hφdiff := hφ.differentiable one_ne_zero
  have hφ0 : φ 0 = θ 0 := by simpa [φ] using hψ0
  have hφℓ : φ ℓ = θ ℓ := by
    have hal : a * ℓ / a = ℓ := by field_simp
    simp only [hal] at hψℓ
    simpa [φ, div_inv_eq_mul, mul_comm] using hψℓ
  have hφx : (∫ s in 0..ℓ, cos (φ s)) = (∫ s in 0..ℓ, cos (θ s)) := by
    have heφ := xCoord_scaling φ ha 0 ℓ
    have heθ := xCoord_scaling θ ha 0 ℓ
    simp only [xCoord, mul_zero, zero_add] at heφ heθ
    simp_rw [show ∀ s, φ (s / a) = ψ s from congrFun hround] at heφ
    rw [heφ, heθ] at hx
    exact (mul_left_cancel₀ ha.ne') hx
  have hφy : (∫ s in 0..ℓ, sin (φ s)) = (∫ s in 0..ℓ, sin (θ s)) := by
    have heφ := yCoord_scaling φ ha 0 ℓ
    have heθ := yCoord_scaling θ ha 0 ℓ
    simp only [yCoord, mul_zero, zero_add] at heφ heθ
    simp_rw [show ∀ s, φ (s / a) = ψ s from congrFun hround] at heφ
    rw [heφ, heθ] at hy
    exact (mul_left_cancel₀ ha.ne') hy
  have hφclose : ∀ s ∈ Icc 0 ℓ,
      |φ s - θ s| < r ∧ |deriv φ s - deriv θ s| < r := by
    intro s hs
    have has : a * s ∈ Icc 0 (a * ℓ) :=
      ⟨mul_nonneg ha.le hs.1, mul_le_mul_of_nonneg_left hs.2 ha.le⟩
    obtain ⟨hval, hder⟩ := hclose (a * s) has
    have hsa : a * s / a = s := by field_simp
    simp only [hsa] at hval
    constructor
    · have hv : |φ s - θ s| < δ := by
        simpa [φ, div_eq_mul_inv, mul_comm] using hval
      exact hv.trans hδr
    · rw [deriv_angle_scaling hθdiff, hsa] at hder
      have hdφ : deriv φ s = a * deriv ψ (a * s) := by
        rw [show φ = (fun s => ψ (s / a⁻¹)) from rfl,
          deriv_angle_scaling (hψ.differentiable one_ne_zero)]
        simp [div_eq_mul_inv, mul_comm]
      have hd : deriv φ s - deriv θ s =
          a * (deriv ψ (a * s) - deriv θ s / a) := by
        rw [hdφ]
        field_simp
      rw [hd, abs_mul, abs_of_pos ha]
      exact (mul_lt_mul_of_pos_left hder ha).trans haδr
  have he := hmin φ hφ hφ0 hφℓ hφx hφy hφclose
  have hscaled := mul_le_mul_of_nonneg_left he (mul_pos ha hc).le
  rw [← energy_scaling_of_density_factor hθdiff ha hε ℓ,
    ← energy_scaling_of_density_factor hφdiff ha hε ℓ, hround] at hscaled
  exact hscaled

/-- Positive similarity is reversible on the actual constrained C¹ local-minimum
property, including its neighborhood and all endpoint constraints. -/
theorem locallyMinimizing_scaling_iff_of_density_factor {ε θ : ℝ → ℝ}
    {a c ℓ : ℝ} (ha : 0 < a) (hc : 0 < c) (hθ : ContDiff ℝ 1 θ)
    (hε : ∀ q, ε (q / a) = c * ε q) :
    LocallyMinimizing ε (fun s => θ (s / a)) (a * ℓ) ↔
      LocallyMinimizing ε θ ℓ := by
  constructor
  · intro hmin
    have hi : ∀ q, ε (q / a⁻¹) = c⁻¹ * ε q := by
      intro q
      have he : ε q = c * ε (q / a⁻¹) := by
        simpa [div_div, ha.ne'] using hε (q / a⁻¹)
      calc
        ε (q / a⁻¹) = c⁻¹ * (c * ε (q / a⁻¹)) := by simp [hc.ne']
        _ = c⁻¹ * ε q := by rw [← he]
    have hm := locallyMinimizing_scaling_of_density_factor
      (inv_pos.mpr ha) (inv_pos.mpr hc) (contDiff_angle_scaling hθ a) hi hmin
    simpa [div_eq_mul_inv, ha.ne', mul_assoc] using hm
  · exact locallyMinimizing_scaling_of_density_factor ha hc hθ hε

/-- Real-degree homogeneous densities transport local minima under every
positive similarity. The degree may be arbitrary: the energy multiplier is
positive even when the energy itself is not. -/
theorem locallyMinimizing_scaling_iff_of_homogeneous {ε θ : ℝ → ℝ}
    {a m ℓ : ℝ} (ha : 0 < a) (hθ : ContDiff ℝ 1 θ)
    (hε : ∀ t : ℝ, 0 < t → ∀ q : ℝ, ε (t * q) = t ^ m * ε q) :
    LocallyMinimizing ε (fun s => θ (s / a)) (a * ℓ) ↔
      LocallyMinimizing ε θ ℓ := by
  apply locallyMinimizing_scaling_iff_of_density_factor ha
    (Real.rpow_pos_of_pos (inv_pos.mpr ha) m) hθ
  intro q
  simpa only [div_eq_mul_inv, mul_comm q] using hε a⁻¹ (inv_pos.mpr ha) q

/-- In particular the classical quadratic density has equivalent constrained
local-minimum problems at positively scaled boundary data. -/
theorem locallyMinimizing_scaling_iff_quadratic {θ : ℝ → ℝ}
    {a ℓ : ℝ} (ha : 0 < a) (hθ : ContDiff ℝ 1 θ) (k : ℝ) :
    LocallyMinimizing (fun q => k * q ^ 2 / 2) (fun s => θ (s / a)) (a * ℓ) ↔
      LocallyMinimizing (fun q => k * q ^ 2 / 2) θ ℓ := by
  apply locallyMinimizing_scaling_iff_of_density_factor ha
    (sq_pos_of_pos (inv_pos.mpr ha)) hθ
  intro q
  simp only [div_eq_mul_inv, mul_pow]
  ring

/-- The scale factor in energy can be absorbed into the weight parameter.
No probabilistic interpretation of the exponential weight is required. -/
theorem exponentialWeight_scaling_of_density_factor {ε θ : ℝ → ℝ}
    (hθ : Differentiable ℝ θ) {a c : ℝ} (ha : 0 < a)
    (hε : ∀ q, ε (q / a) = c * ε q) (β ℓ : ℝ) :
    exponentialWeight β ε (fun s => θ (s / a)) (a * ℓ) =
      exponentialWeight (β * (a * c)) ε θ ℓ := by
  unfold exponentialWeight
  rw [energy_scaling_of_density_factor hθ ha hε ℓ]
  congr 1
  ring

/-- Changing the weight parameter by the reciprocal of the positive energy
scale preserves the numerical weight of each curve. -/
theorem exponentialWeight_scaling_rescaled_parameter {ε θ : ℝ → ℝ}
    (hθ : Differentiable ℝ θ) {a c : ℝ} (ha : 0 < a) (hc : c ≠ 0)
    (hε : ∀ q, ε (q / a) = c * ε q) (β ℓ : ℝ) :
    exponentialWeight (β / (a * c)) ε (fun s => θ (s / a)) (a * ℓ) =
      exponentialWeight β ε θ ℓ := by
  rw [exponentialWeight_scaling_of_density_factor hθ ha hε]
  rw [div_mul_cancel₀ _ (mul_ne_zero ha.ne' hc)]

end Elastica
