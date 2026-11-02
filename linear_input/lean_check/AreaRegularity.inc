import Elastica.ConstraintRegularity

/-!
The endpoint-position and signed-area constraints have full rank unless the
curvature is constant. Constant curvature directly satisfies the first-order
stationarity of the pure bending energy, including the straight case.
-/

noncomputable section
namespace LinearInputAreaRegularity

open Real Set MeasureTheory Filter Elastica
open scoped Topology Interval

/-- Nonconstant curvature makes the two endpoint differentials and the area
moment differential independent. The true area differential differs from the
moment by a linear combination of the first two differentials. -/
theorem constraint_coefficients_zero {θ : ℝ → ℝ} {ℓ a b c : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 3 θ)
    (hnonconst : ¬ ∃ K : ℝ, ∀ s ∈ Ioo 0 ℓ, deriv θ s = K)
    (h : ∀ η : variationSpace ℓ,
      a * (∫ s in 0..ℓ, -sin (θ s) * η.val s) +
      b * (∫ s in 0..ℓ, cos (θ s) * η.val s) +
      c * (∫ s in 0..ℓ,
        (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) * η.val s) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  classical
  have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  by_cases hc : c = 0
  · have hne : ∃ s ∈ Ioo 0 ℓ, deriv θ s ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hnonconst ⟨0, hn⟩
    obtain ⟨ha, hb⟩ := Elastica.constraint_coefficients_zero hℓ hθ1 hne (by
      intro η
      simpa only [hc, zero_mul, add_zero] using h η)
    exact ⟨ha, hb, hc⟩
  · let A : ℝ → ℝ := fun s => c * xCoord θ 0 s + b
    let B : ℝ → ℝ := fun s => c * yCoord θ 0 s - a
    let q : ℝ → ℝ := fun s => A s * cos (θ s) + B s * sin (θ s)
    let F : ℝ → ℝ := fun s => -(A s * sin (θ s)) + B s * cos (θ s)
    have hA : ContDiff ℝ 1 A :=
      (contDiff_const.mul (LinearInputPressureStationary.contDiff_xCoord hθ.continuous)).add contDiff_const
    have hB : ContDiff ℝ 1 B :=
      (contDiff_const.mul (LinearInputPressureStationary.contDiff_yCoord hθ.continuous)).sub contDiff_const
    have hq : ContDiff ℝ 1 q := (hA.mul hθ1.cos).add (hB.mul hθ1.sin)
    let η : variationSpace ℓ := ⟨fun s => s * (ℓ - s) * q s,
      ⟨(contDiff_id.mul (contDiff_const.sub contDiff_id)).mul hq, by simp, by simp⟩⟩
    have hint : (∫ s in 0..ℓ, q s * η.val s) = 0 := by
      have hi : (∫ s in 0..ℓ, q s * η.val s) =
          (∫ s in 0..ℓ, (-a * sin (θ s) + b * cos (θ s)) * η.val s) +
          c * (∫ s in 0..ℓ,
            (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) * η.val s) := by
        have hi₁ : IntervalIntegrable
            (fun s => (-a * sin (θ s) + b * cos (θ s)) * η.val s) volume 0 ℓ :=
          ((((continuous_const.mul hθ1.sin.continuous).add
            (continuous_const.mul hθ1.cos.continuous)).mul η.property.1.continuous).intervalIntegrable 0 ℓ)
        have hi₂ : IntervalIntegrable
            (fun s => c * ((xCoord θ 0 s * cos (θ s) +
              yCoord θ 0 s * sin (θ s)) * η.val s)) volume 0 ℓ :=
          ((continuous_const.mul ((LinearInputAreaVariation.continuous_moment hθ.continuous).mul
            η.property.1.continuous)).intervalIntegrable 0 ℓ)
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi₁ hi₂]
        apply intervalIntegral.integral_congr
        intro s _
        dsimp [q, A, B]
        ring
      rw [hi, force_integral hθ.continuous η]
      exact h η
    have hz : (∫ s in 0..ℓ, s * (ℓ - s) * (q s) ^ 2) = 0 := by
      convert hint using 1
      apply intervalIntegral.integral_congr
      intro s _
      change s * (ℓ - s) * q s ^ 2 = q s * (s * (ℓ - s) * q s)
      ring
    have hzero := residual_zero_of_weighted_square_integral hℓ hq.continuous hz
    have hdq (s : ℝ) : HasDerivAt q (c + deriv θ s * F s) s := by
      have ht := (hθ1.differentiable one_ne_zero s).hasDerivAt
      have hx := (hasDerivAt_xCoord hθ.continuous 0 s).const_mul c |>.add_const b
      have hy := (hasDerivAt_yCoord hθ.continuous 0 s).const_mul c |>.sub_const a
      convert (hx.mul ht.cos).add (hy.mul ht.sin) using 1
      dsimp [F, A, B]
      nlinarith [congrArg (fun v : ℝ => c * v) (sin_sq_add_cos_sq (θ s))]
    have hdF (s : ℝ) : HasDerivAt F (-deriv θ s * q s) s := by
      have ht := (hθ1.differentiable one_ne_zero s).hasDerivAt
      have hx := (hasDerivAt_xCoord hθ.continuous 0 s).const_mul c |>.add_const b
      have hy := (hasDerivAt_yCoord hθ.continuous 0 s).const_mul c |>.sub_const a
      convert ((hx.mul ht.sin).neg).add (hy.mul ht.cos) using 1
      dsimp [q, A, B]
      ring
    have hrel : ∀ s ∈ Ioo 0 ℓ, c + deriv θ s * F s = 0 := by
      intro s hs
      have heq : q =ᶠ[𝓝 s] fun _ => 0 := by
        filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht using hzero t ht
      exact (hdq s).unique ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq heq)
    have hFd : ∀ s ∈ Ioo 0 ℓ, HasDerivAt F 0 s := by
      intro s hs
      simpa only [hzero s hs, mul_zero] using hdF s
    obtain ⟨d, hd⟩ : ∃ d : ℝ, ∀ s ∈ Ioo 0 ℓ, F s = d := by
      apply isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo 0 ℓ).isPreconnected
      · intro s hs
        exact (hFd s hs).differentiableAt.differentiableWithinAt
      · intro s hs
        exact (hFd s hs).deriv
    have hmid : ℓ / 2 ∈ Ioo 0 ℓ := by constructor <;> linarith
    have hdne : d ≠ 0 := by
      intro hd0
      have hm := hrel (ℓ / 2) hmid
      rw [hd (ℓ / 2) hmid, hd0, mul_zero, add_zero] at hm
      exact hc hm
    exfalso
    apply hnonconst
    refine ⟨-c / d, fun s hs => ?_⟩
    apply (eq_div_iff hdne).2
    have hr := hrel s hs
    rw [hd s hs] at hr
    linarith

/-- Three fixed-angle variations can independently correct endpoint position
and area moment when the curvature is not constant. -/
theorem exists_normalized_constraint_directions {θ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 3 θ)
    (hnonconst : ¬ ∃ K : ℝ, ∀ s ∈ Ioo 0 ℓ, deriv θ s = K) :
    ∃ ξ₁ ξ₂ ξ₃ : variationSpace ℓ,
      ((∫ s in 0..ℓ, -sin (θ s) * ξ₁.val s) = 1 ∧
       (∫ s in 0..ℓ, cos (θ s) * ξ₁.val s) = 0 ∧
       (∫ s in 0..ℓ, (xCoord θ 0 s * cos (θ s) +
         yCoord θ 0 s * sin (θ s)) * ξ₁.val s) = 0) ∧
      ((∫ s in 0..ℓ, -sin (θ s) * ξ₂.val s) = 0 ∧
       (∫ s in 0..ℓ, cos (θ s) * ξ₂.val s) = 1 ∧
       (∫ s in 0..ℓ, (xCoord θ 0 s * cos (θ s) +
         yCoord θ 0 s * sin (θ s)) * ξ₂.val s) = 0) ∧
      ((∫ s in 0..ℓ, -sin (θ s) * ξ₃.val s) = 0 ∧
       (∫ s in 0..ℓ, cos (θ s) * ξ₃.val s) = 0 ∧
       (∫ s in 0..ℓ, (xCoord θ 0 s * cos (θ s) +
         yCoord θ 0 s * sin (θ s)) * ξ₃.val s) = 1) := by
  let cx := constraintLinear ℓ (fun s => -sin (θ s)) hθ.sin.continuous.neg
  let cy := constraintLinear ℓ (fun s => cos (θ s)) hθ.cos.continuous
  let ca := constraintLinear ℓ (fun s => xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s))
    (LinearInputAreaVariation.continuous_moment hθ.continuous)
  let C : variationSpace ℓ →ₗ[ℝ] ℝ × (ℝ × ℝ) := cx.prod (cy.prod ca)
  have hev (f : (ℝ × (ℝ × ℝ)) →ₗ[ℝ] ℝ) (x y z : ℝ) :
      f (x, (y, z)) = f (1, (0, 0)) * x + f (0, (1, 0)) * y + f (0, (0, 1)) * z := by
    have hp : (x, (y, z)) = x • (1, (0, 0)) + y • (0, (1, 0)) + z • (0, (0, 1)) := by
      ext <;> simp
    rw [hp, map_add, map_add, map_smul, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  have ha : (LinearMap.range C).dualAnnihilator = ⊥ := by
    apply le_antisymm _ bot_le
    intro f hf
    rw [Submodule.mem_dualAnnihilator] at hf
    have habc : f (1, (0, 0)) = 0 ∧ f (0, (1, 0)) = 0 ∧ f (0, (0, 1)) = 0 := by
      apply constraint_coefficients_zero hℓ hθ hnonconst
      intro η
      have hfc : f (C η) = 0 := hf (C η) ⟨η, rfl⟩
      change f (cx η, (cy η, ca η)) = 0 at hfc
      rw [hev] at hfc
      exact hfc
    change f = 0
    apply LinearMap.ext
    intro p
    change f (p.1, (p.2.1, p.2.2)) = 0
    rw [hev, habc.1, habc.2.1, habc.2.2]
    ring
  have hsurj : Function.Surjective C :=
    LinearMap.range_eq_top.mp (Submodule.dualAnnihilator_eq_bot_iff.mp ha)
  obtain ⟨ξ₁, h₁⟩ := hsurj (1, (0, 0))
  obtain ⟨ξ₂, h₂⟩ := hsurj (0, (1, 0))
  obtain ⟨ξ₃, h₃⟩ := hsurj (0, (0, 1))
  refine ⟨ξ₁, ξ₂, ξ₃, ?_, ?_, ?_⟩
  · exact ⟨congrArg Prod.fst h₁, congrArg (fun z => z.2.1) h₁, congrArg (fun z => z.2.2) h₁⟩
  · exact ⟨congrArg Prod.fst h₂, congrArg (fun z => z.2.1) h₂, congrArg (fun z => z.2.2) h₂⟩
  · exact ⟨congrArg Prod.fst h₃, congrArg (fun z => z.2.1) h₃, congrArg (fun z => z.2.2) h₃⟩

/-- The pressure multiplier is unique on a fixed nonconstant-curvature curve.
This does not assert that the multiplier is nonzero, and it does not apply to
the constant-curvature cases where the third differential loses rank. -/
theorem pressure_coefficient_unique {θ : ℝ → ℝ} {ℓ k p₁ p₂ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 3 θ)
    (hnonconst : ¬ ∃ K : ℝ, ∀ s ∈ Ioo 0 ℓ, deriv θ s = K)
    (hp₁ : LinearInputPressureStationary.Stationary k p₁ θ ℓ)
    (hp₂ : LinearInputPressureStationary.Stationary k p₂ θ ℓ) : p₁ = p₂ := by
  obtain ⟨ξ₁, ξ₂, ξ₃, _, _, h₃⟩ :=
    exists_normalized_constraint_directions hℓ hθ hnonconst
  have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  have hv₁ := (LinearInputPressureStationary.stationary_iff_firstVariation hℓ.le hθ1).mp
    hp₁ ξ₃ h₃.1 h₃.2.1
  have hv₂ := (LinearInputPressureStationary.stationary_iff_firstVariation hℓ.le hθ1).mp
    hp₂ ξ₃ h₃.1 h₃.2.1
  rw [h₃.2.2, mul_one] at hv₁ hv₂
  linarith

/-- At constant curvature the pure bending first variation vanishes for every
fixed-angle direction. No exact-constraint correction or rank hypothesis is
needed; this includes straight curves. -/
theorem areaStationary_of_constant_curvature {θ : ℝ → ℝ} {ℓ k K : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 3 θ)
    (hconst : ∀ s ∈ Ioo 0 ℓ, deriv θ s = K) :
    LinearInputPressureStationary.AreaStationary k θ ℓ := by
  have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  intro η _ _ _
  have he := hasDerivAt_energy_variation hℓ.le
    (show ContDiff ℝ 1 (fun q : ℝ => k * q ^ 2 / 2) by fun_prop) hθ1 η.property.1
  have hd (q : ℝ) : deriv (fun q : ℝ => k * q ^ 2 / 2) q = k * q :=
    (quadratic_density_hasDerivAt k q).deriv
  simp_rw [hd] at he
  rw [he.deriv]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun s => (k * K) * η.val s)
    (f' := fun s => k * deriv θ s * deriv η.val s)
    hℓ.le (continuous_const.mul η.property.1.continuous).continuousOn
    (fun s hs => by
      simpa only [hconst s hs] using
        ((η.property.1.differentiable one_ne_zero s).hasDerivAt.const_mul (k * K)))
    (((continuous_const.mul hθ1.continuous_deriv_one).mul
      η.property.1.continuous_deriv_one).intervalIntegrable 0 ℓ)
  simpa only [η.property.2.1, η.property.2.2, mul_zero, sub_self] using hi

end LinearInputAreaRegularity
