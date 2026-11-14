import Elastica.Reconstruction
import Elastica.Examples
import Elastica.SecondVariation
import Mathlib.Tactic.FunProp

/-!
# The degenerate straight endpoint constraint

Horizontal displacement equal to the full arc length forces a horizontal
straight curve.  At this singular constraint, linearized feasible directions
can have negative energy second variation although every exactly feasible
curve has the same energy.  Everything below uses the actual reconstruction
and actual parameter derivatives.  The result is stated in horizontal
coordinates; no general Euclidean equality theorem is claimed here.
-/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace Elastica

/-- Saturation of the horizontal displacement bound forces the horizontal
tangent component to be one, including at the endpoints. -/
theorem cos_eq_one_of_xCoord_eq_length {θ : ℝ → ℝ} {ℓ x₀ : ℝ}
    (hℓ : 0 < ℓ) (hθ : Continuous θ)
    (hx : xCoord θ x₀ ℓ = x₀ + ℓ) :
    ∀ s ∈ Icc 0 ℓ, cos (θ s) = 1 := by
  have hi : (∫ s in 0..ℓ, cos (θ s)) = ℓ := by
    unfold xCoord at hx
    linarith
  intro s hs
  by_contra hne
  have hp : cos (θ s) < 1 := lt_of_le_of_ne (cos_le_one _) hne
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hℓ (continuous_cos.comp hθ).continuousOn continuousOn_const
    (fun t _ => cos_le_one (θ t)) ⟨s, hs, hp⟩
  have : (∫ t in 0..ℓ, cos (θ t)) < ℓ := by simpa using hlt
  linarith

/-- The vertical tangent component vanishes under the same saturated constraint. -/
theorem sin_eq_zero_of_xCoord_eq_length {θ : ℝ → ℝ} {ℓ x₀ : ℝ}
    (hℓ : 0 < ℓ) (hθ : Continuous θ)
    (hx : xCoord θ x₀ ℓ = x₀ + ℓ) :
    ∀ s ∈ Icc 0 ℓ, sin (θ s) = 0 := by
  intro s hs
  have hc := cos_eq_one_of_xCoord_eq_length hℓ hθ hx s hs
  have hh := sin_sq_add_cos_sq (θ s)
  rw [hc] at hh
  nlinarith [sq_nonneg (sin (θ s))]

/-- For C¹ angles, the signed curvature also vanishes on the closed interval. -/
theorem curvature_zero_of_xCoord_eq_length {θ : ℝ → ℝ} {ℓ x₀ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ)
    (hx : xCoord θ x₀ ℓ = x₀ + ℓ) :
    ∀ s ∈ Icc 0 ℓ, curvature θ s = 0 := by
  have hc := cos_eq_one_of_xCoord_eq_length hℓ hθ.continuous hx
  have hs := sin_eq_zero_of_xCoord_eq_length hℓ hθ.continuous hx
  have hd : EqOn (deriv θ) (fun _ => (0 : ℝ)) (Ioo 0 ℓ) := by
    intro s hsi
    have he : (fun t => sin (θ t)) =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hsi] with t ht
      exact hs t ⟨ht.1.le, ht.2.le⟩
    have hh := ((hθ.differentiable one_ne_zero s).hasDerivAt.sin).deriv
    rw [he.deriv_eq, deriv_const, hc s ⟨hsi.1.le, hsi.2.le⟩, one_mul] at hh
    exact hh.symm
  have hclosed := hd.closure hθ.continuous_deriv_one continuous_const
  simpa only [curvature, closure_Ioo hℓ.ne, Set.EqOn] using hclosed

/-- Fixing the initial real angle removes the possible multiples of 2π:
the whole lifted angle is exactly its initial value. -/
theorem angle_eq_initial_of_xCoord_eq_length {θ : ℝ → ℝ} {ℓ x₀ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ)
    (hx : xCoord θ x₀ ℓ = x₀ + ℓ) :
    ∀ s ∈ Icc 0 ℓ, θ s = θ 0 := by
  apply angle_eq_of_curvature_eq_initial (θ := fun _ => θ 0) hℓ contDiff_const hθ
  · intro s hs
    simpa using curvature_zero_of_xCoord_eq_length hℓ hθ hx s ⟨hs.1.le, hs.2.le⟩
  · rfl

/-- Every exactly feasible curve for the saturated horizontal displacement has
the same energy, for any density; no sign assumption on its second derivative. -/
theorem energy_eq_straight_of_xCoord_eq_length {θ : ℝ → ℝ} {ℓ x₀ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ)
    (hx : xCoord θ x₀ ℓ = x₀ + ℓ) (ε : ℝ → ℝ) :
    energy ε θ ℓ = ℓ * ε 0 := by
  unfold energy
  have he : (∫ s in 0..ℓ, ε (deriv θ s)) = ∫ s in 0..ℓ, ε 0 := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hℓ.le] at hs
    exact congrArg ε (curvature_zero_of_xCoord_eq_length hℓ hθ hx s hs)
  rw [he]
  simp

/-- In particular the straight curve is a global minimizer among all C¹ angles
with the saturated horizontal displacement, for every density. Adding the
fixed vertical endpoint and fixed end angles only restricts this feasible set. -/
theorem straight_is_global_minimum_on_horizontal_constraint {ℓ : ℝ}
    (hℓ : 0 < ℓ) (ε : ℝ → ℝ) (θ : ℝ → ℝ)
    (hθ : ContDiff ℝ 1 θ) (hx : xCoord θ 0 ℓ = ℓ) :
    energy ε (fun _ => 0) ℓ ≤ energy ε θ ℓ := by
  rw [energy_const, energy_eq_straight_of_xCoord_eq_length
    (x₀ := 0) hℓ hθ (by simpa using hx)]

/-- Derivative of the explicit fixed-end polynomial variation. -/
theorem straight_polynomial_hasDerivAt (s : ℝ) :
    HasDerivAt (fun u : ℝ => u * (1 - u) * (u - 1 / 2))
      (-3 * s ^ 2 + 3 * s - 1 / 2) s := by
  convert (((hasDerivAt_id s).mul ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))).mul
    ((hasDerivAt_id s).sub_const (1 / 2))) using 1
  all_goals first | rfl | (simp only [id_eq, Pi.sub_apply, Pi.mul_apply]; ring)

/-- Its average is zero, hence it lies in the vertical linearized constraint
kernel at a horizontal straight curve. -/
theorem straight_polynomial_integral :
    (∫ s in (0 : ℝ)..1, s * (1 - s) * (s - 1 / 2)) = 0 := by
  have hd (s : ℝ) :
      HasDerivAt (fun u : ℝ => -(u ^ 4) / 4 + u ^ 3 / 2 - u ^ 2 / 4)
        (s * (1 - s) * (s - 1 / 2)) s := by
    convert ((((hasDerivAt_id s).pow 4).neg.div_const 4).add
      (((hasDerivAt_id s).pow 3).div_const 2)).sub
        (((hasDerivAt_id s).pow 2).div_const 4) using 1
    all_goals first | rfl | (simp only [id_eq]; norm_num; ring)
  have hc : Continuous (fun s : ℝ => s * (1 - s) * (s - 1 / 2)) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun s _ => hd s) (hc.intervalIntegrable 0 1)
  norm_num at h ⊢
  exact h

/-- Its derivative has strictly positive squared integral, evaluated exactly. -/
theorem straight_polynomial_deriv_square_integral :
    (∫ s in (0 : ℝ)..1,
      (deriv (fun u : ℝ => u * (1 - u) * (u - 1 / 2)) s) ^ 2) = 1 / 20 := by
  have hd (s : ℝ) :
      HasDerivAt (fun u : ℝ => 9 * u ^ 5 / 5 - 9 * u ^ 4 / 2 +
        4 * u ^ 3 - 3 * u ^ 2 / 2 + u / 4)
        ((-3 * s ^ 2 + 3 * s - 1 / 2) ^ 2) s := by
    convert ((((((hasDerivAt_id s).pow 5).const_mul 9).div_const 5).sub
      ((((hasDerivAt_id s).pow 4).const_mul 9).div_const 2)).add
        (((hasDerivAt_id s).pow 3).const_mul 4)).sub
          ((((hasDerivAt_id s).pow 2).const_mul 3).div_const 2) |>.add
            ((hasDerivAt_id s).div_const 4) using 1
    all_goals first | rfl | (simp only [id_eq]; norm_num; ring)
  have hc : Continuous (fun s : ℝ => (-3 * s ^ 2 + 3 * s - 1 / 2) ^ 2) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun s _ => hd s) (hc.intervalIntegrable 0 1)
  simp_rw [(straight_polynomial_hasDerivAt _).deriv]
  norm_num at h ⊢
  exact h

theorem negative_quadratic_second_deriv (q : ℝ) :
    deriv (deriv (fun x : ℝ => -(x ^ 2) / 2)) q = -1 := by
  have hd : deriv (fun x : ℝ => -(x ^ 2) / 2) = fun x => -x := by
    funext x
    have h : HasDerivAt (fun u : ℝ => -(u ^ 2) / 2) (-x) x := by
      convert ((hasDerivAt_id x).pow 2).neg.div_const 2 using 1
      all_goals first | rfl | (simp only [id_eq]; norm_num; ring)
    exact h.deriv
  rw [hd]
  exact (hasDerivAt_id q).neg.deriv

/-- Although its first endpoint derivative is zero, every nonzero member of
this additive variation has strictly smaller horizontal displacement. -/
theorem straight_polynomial_variation_not_exactly_feasible {t : ℝ} (ht : t ≠ 0) :
    xCoord (angleVariation (fun _ => 0)
      (fun s : ℝ => s * (1 - s) * (s - 1 / 2)) t) 0 1 < 1 := by
  let θ : ℝ → ℝ := angleVariation (fun _ => 0)
    (fun s : ℝ => s * (1 - s) * (s - 1 / 2)) t
  have hθ : ContDiff ℝ 1 θ := by
    change ContDiff ℝ 1 (fun s : ℝ => 0 + t * (s * (1 - s) * (s - 1 / 2)))
    fun_prop
  have hne : xCoord θ 0 1 ≠ 1 := by
    intro hx
    have ha := angle_eq_initial_of_xCoord_eq_length (ℓ := 1) (x₀ := 0)
      (by norm_num) hθ (by simpa using hx) (1 / 4) (by constructor <;> norm_num)
    norm_num [θ, angleVariation] at ha
    exact ht (by linarith)
  have habs := abs_x_displacement_le θ 0 1 (by norm_num)
  have hle : xCoord θ 0 1 ≤ 1 := by
    simpa using (le_abs_self (xCoord θ 0 1)).trans (by simpa using habs)
  exact lt_of_le_of_ne hle hne

/-- The straight curve is an exact constrained global minimizer, but this C¹
fixed-end direction belongs to both linearized endpoint kernels and has a
negative actual energy second derivative. The singular constraint is essential. -/
theorem straight_negative_secondVariation_counterexample :
    (∀ θ : ℝ → ℝ, ContDiff ℝ 1 θ → xCoord θ 0 1 = 1 →
      energy (fun q : ℝ => -(q ^ 2) / 2) (fun _ => 0) 1 ≤
        energy (fun q : ℝ => -(q ^ 2) / 2) θ 1) ∧
    ∃ η : ℝ → ℝ, ContDiff ℝ 1 η ∧ η 0 = 0 ∧ η 1 = 0 ∧
      deriv (fun t : ℝ => ∫ s in 0..1, cos (t * η s)) 0 = 0 ∧
      deriv (fun t : ℝ => ∫ s in 0..1, sin (t * η s)) 0 = 0 ∧
      deriv (deriv (fun t =>
        energy (fun q : ℝ => -(q ^ 2) / 2)
          (angleVariation (fun _ => 0) η t) 1)) 0 = -1 / 20 := by
  refine ⟨fun θ hθ hx => straight_is_global_minimum_on_horizontal_constraint
    (by norm_num) _ θ hθ hx, ?_⟩
  let η : ℝ → ℝ := fun s => s * (1 - s) * (s - 1 / 2)
  have hη : ContDiff ℝ 1 η := by dsimp [η]; fun_prop
  refine ⟨η, hη, by simp [η], by simp [η], ?_, ?_, ?_⟩
  · simpa only [zero_add, sin_zero, neg_zero, zero_mul, intervalIntegral.integral_zero] using
      (hasDerivAt_horizontal_variation (θ := fun _ => 0)
        (ℓ := 1) (by norm_num) continuous_const hη.continuous).deriv
  · have h := (hasDerivAt_vertical_variation (θ := fun _ => 0)
      (ℓ := 1) (by norm_num) continuous_const hη.continuous).deriv
    simpa only [zero_add, cos_zero, one_mul, η, straight_polynomial_integral] using h
  · rw [secondVariation_energy (by norm_num)
      (show ContDiff ℝ 2 (fun q : ℝ => -(q ^ 2) / 2) by fun_prop) contDiff_const hη]
    simp_rw [negative_quadratic_second_deriv]
    rw [intervalIntegral.integral_const_mul]
    have hi : (∫ s in (0 : ℝ)..1, (deriv η s) ^ 2) = 1 / 20 :=
      straight_polynomial_deriv_square_integral
    rw [hi]
    norm_num

end Elastica
