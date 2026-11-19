import Elastica.ExactVariation

/-!
Actual endpoint-and-area preserving variations, obtained from a finite
dimensional implicit-function theorem.  The third constraint is changed by a
fixed linear combination of the first two to expose the identity correction
block; preserving all three is still exactly preserving endpoint and area.
-/

noncomputable section
namespace LinearInputAreaExactVariation

open Real Set MeasureTheory Filter Elastica LinearInputAreaParameters
open scoped Topology

/-- An invertible linear recombination of endpoint and signed-area constraints.
Its third differential at the base curve is the area moment. -/
def constraintParameters (θ η ξ₁ ξ₂ ξ₃ : ℝ → ℝ) (ℓ : ℝ) (p : Parameters) :
    ℝ × (ℝ × ℝ) :=
  let X := ∫ s in 0..ℓ, cos (θ s + parameterLinear η ξ₁ ξ₂ ξ₃ s p)
  let Y := ∫ s in 0..ℓ, sin (θ s + parameterLinear η ξ₁ ξ₂ ξ₃ s p)
  (X, (Y, areaParameters θ η ξ₁ ξ₂ ξ₃ ℓ p -
    yCoord θ 0 ℓ / 2 * X + xCoord θ 0 ℓ / 2 * Y))

theorem contDiff_constraintParameters {θ η ξ₁ ξ₂ ξ₃ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hθ : Continuous θ) (hη : Continuous η)
    (hξ₁ : Continuous ξ₁) (hξ₂ : Continuous ξ₂) (hξ₃ : Continuous ξ₃) :
    ContDiff ℝ 2 (constraintParameters θ η ξ₁ ξ₂ ξ₃ ℓ) := by
  have hB := continuous_parameterLinear hη hξ₁ hξ₂ hξ₃
  have hx := LinearInputAreaParameters.contDiff_two_integral_linear_parameters
    hℓ Real.contDiff_cos hθ hB
  have hy := LinearInputAreaParameters.contDiff_two_integral_linear_parameters
    hℓ Real.contDiff_sin hθ hB
  have ha := contDiff_areaParameters hℓ hθ hη hξ₁ hξ₂ hξ₃
  exact hx.prodMk (hy.prodMk ((ha.sub (contDiff_const.mul hx)).add (contDiff_const.mul hy)))

/-- The differential is calculated from actual parameter derivatives of the
endpoint integrals and signed area, including the area boundary term. -/
theorem fderiv_constraintParameters_zero {θ η ξ₁ ξ₂ ξ₃ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hθ : Continuous θ) (hη : Continuous η)
    (hξ₁ : Continuous ξ₁) (hξ₂ : Continuous ξ₂) (hξ₃ : Continuous ξ₃)
    (p : Parameters) :
    fderiv ℝ (constraintParameters θ η ξ₁ ξ₂ ξ₃ ℓ) 0 p =
      ((∫ s in 0..ℓ, -sin (θ s) * parameterLinear η ξ₁ ξ₂ ξ₃ s p),
       ((∫ s in 0..ℓ, cos (θ s) * parameterLinear η ξ₁ ξ₂ ξ₃ s p),
        (∫ s in 0..ℓ, (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) *
          parameterLinear η ξ₁ ξ₂ ξ₃ s p))) := by
  let ζ : ℝ → ℝ := fun s => parameterLinear η ξ₁ ξ₂ ξ₃ s p
  have hζ : Continuous ζ :=
    (continuous_parameterLinear hη hξ₁ hξ₂ hξ₃).clm_apply continuous_const
  have hx := hasDerivAt_horizontal_variation hℓ hθ hζ
  have hy := hasDerivAt_vertical_variation hℓ hθ hζ
  have ha := LinearInputAreaVariation.hasDerivAt_area_variation hθ hζ ℓ
  have hadj : HasDerivAt
      (fun t => LinearInputAreaVariation.area (angleVariation θ ζ t) ℓ -
        yCoord θ 0 ℓ / 2 * (∫ s in 0..ℓ, cos (θ s + t * ζ s)) +
        xCoord θ 0 ℓ / 2 * (∫ s in 0..ℓ, sin (θ s + t * ζ s)))
      (∫ s in 0..ℓ, (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) * ζ s) 0 := by
    convert (ha.sub (hx.const_mul (yCoord θ 0 ℓ / 2))).add
      (hy.const_mul (xCoord θ 0 ℓ / 2)) using 1
    simp only [neg_mul, intervalIntegral.integral_neg]
    ring
  have hd : HasDerivAt
      (fun t : ℝ => constraintParameters θ η ξ₁ ξ₂ ξ₃ ℓ (t • p))
      ((∫ s in 0..ℓ, -sin (θ s) * ζ s),
        ((∫ s in 0..ℓ, cos (θ s) * ζ s),
          (∫ s in 0..ℓ, (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) * ζ s))) 0 := by
    convert hx.prodMk (hy.prodMk hadj) using 1
    simp only [constraintParameters, areaParameters, map_smul, smul_eq_mul, ζ]
    rfl
  have hf := (contDiff_constraintParameters hℓ hθ hη hξ₁ hξ₂ hξ₃).differentiable
    (by norm_num)
  have hfd : HasDerivAt
      (fun t : ℝ => constraintParameters θ η ξ₁ ξ₂ ξ₃ ℓ (t • p))
      (fderiv ℝ (constraintParameters θ η ξ₁ ξ₂ ξ₃ ℓ) 0 p) 0 := by
    have hfp : HasFDerivAt (constraintParameters θ η ξ₁ ξ₂ ξ₃ ℓ)
        (fderiv ℝ (constraintParameters θ η ξ₁ ξ₂ ξ₃ ℓ) 0) ((0 : ℝ) • p) := by
      simpa only [zero_smul] using (hf (0 : Parameters)).hasFDerivAt
    have hp : HasDerivAt (fun t : ℝ => t • p) p 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const p
    exact hfp.comp_hasDerivAt 0 hp
  exact hfd.unique hd

theorem integral_parameterLinear {η ξ₁ ξ₂ ξ₃ w : ℝ → ℝ} {ℓ : ℝ}
    (hη : Continuous η) (hξ₁ : Continuous ξ₁) (hξ₂ : Continuous ξ₂)
    (hξ₃ : Continuous ξ₃) (hw : Continuous w) (p : Parameters) :
    (∫ s in 0..ℓ, w s * parameterLinear η ξ₁ ξ₂ ξ₃ s p) =
      p.1 * (∫ s in 0..ℓ, w s * η s) +
      p.2.1 * (∫ s in 0..ℓ, w s * ξ₁ s) +
      p.2.2.1 * (∫ s in 0..ℓ, w s * ξ₂ s) +
      p.2.2.2 * (∫ s in 0..ℓ, w s * ξ₃ s) := by
  have hiη : IntervalIntegrable (fun s => p.1 * (w s * η s)) volume 0 ℓ :=
    (continuous_const.mul (hw.mul hη)).intervalIntegrable _ _
  have hi₁ : IntervalIntegrable (fun s => p.2.1 * (w s * ξ₁ s)) volume 0 ℓ :=
    (continuous_const.mul (hw.mul hξ₁)).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun s => p.2.2.1 * (w s * ξ₂ s)) volume 0 ℓ :=
    (continuous_const.mul (hw.mul hξ₂)).intervalIntegrable _ _
  have hi₃ : IntervalIntegrable (fun s => p.2.2.2 * (w s * ξ₃ s)) volume 0 ℓ :=
    (continuous_const.mul (hw.mul hξ₃)).intervalIntegrable _ _
  calc
    _ = ∫ s in 0..ℓ, p.1 * (w s * η s) + p.2.1 * (w s * ξ₁ s) +
        p.2.2.1 * (w s * ξ₂ s) + p.2.2.2 * (w s * ξ₃ s) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [parameterLinear_apply]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add ((hiη.add hi₁).add hi₂) hi₃,
        intervalIntegral.integral_add (hiη.add hi₁) hi₂,
        intervalIntegral.integral_add hiη hi₁]
      simp only [intervalIntegral.integral_const_mul]

/-- The actual finite-dimensional IFT for three correction coordinates. -/
theorem exists_implicit_correction {f : Parameters → ℝ × (ℝ × ℝ)}
    (hf : ContDiff ℝ 2 f)
    (ht : (fderiv ℝ f 0).comp (ContinuousLinearMap.inl ℝ ℝ (ℝ × (ℝ × ℝ))) = 0)
    (hc : (fderiv ℝ f 0).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ))) =
      ContinuousLinearMap.id ℝ (ℝ × (ℝ × ℝ))) :
    ∃ g : ℝ → ℝ × (ℝ × ℝ), ContDiffAt ℝ 2 g 0 ∧ g 0 = 0 ∧ HasDerivAt g 0 0 ∧
      ∀ᶠ t in 𝓝 0, f (t, g t) = f 0 := by
  have hi : ((fderiv ℝ f 0).comp
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ)))).IsInvertible := by
    rw [hc]
    exact ⟨ContinuousLinearEquiv.refl ℝ (ℝ × (ℝ × ℝ)), rfl⟩
  let h := hf.contDiffAt (x := (0 : Parameters))
  let g := h.implicitFunction (by norm_num) hi
  refine ⟨g, h.contDiffAt_implicitFunction (by norm_num) hi,
    h.implicitFunction_apply_self (by norm_num) hi, ?_,
    h.eventually_apply_implicitFunction (by norm_num) hi⟩
  have hd := h.hasStrictFDerivAt_implicitFunction (by norm_num) hi
  rw [ht] at hd
  simpa using hd.hasFDerivAt.hasDerivAt

/-- Every first-order feasible direction at a nonconstant-curvature curve is
realized by an actual C²-parameter family preserving both endpoint coordinates
and signed area exactly.  All three correction derivatives vanish at zero. -/
theorem exists_exact_area_variation {θ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 3 θ)
    (hnonconst : ¬ ∃ K : ℝ, ∀ s ∈ Ioo 0 ℓ, deriv θ s = K)
    (η : variationSpace ℓ)
    (hηx : (∫ s in 0..ℓ, -sin (θ s) * η.val s) = 0)
    (hηy : (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0)
    (hηa : (∫ s in 0..ℓ,
      (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) * η.val s) = 0) :
    ∃ ξ₁ ξ₂ ξ₃ : variationSpace ℓ, ∃ a b c : ℝ → ℝ,
      ContDiffAt ℝ 2 a 0 ∧ ContDiffAt ℝ 2 b 0 ∧ ContDiffAt ℝ 2 c 0 ∧
      a 0 = 0 ∧ b 0 = 0 ∧ c 0 = 0 ∧
      HasDerivAt a 0 0 ∧ HasDerivAt b 0 0 ∧ HasDerivAt c 0 0 ∧
      ∀ᶠ t in 𝓝 0,
        (∫ s in 0..ℓ, cos
          (θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s + c t * ξ₃.val s)) =
          (∫ s in 0..ℓ, cos (θ s)) ∧
        (∫ s in 0..ℓ, sin
          (θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s + c t * ξ₃.val s)) =
          (∫ s in 0..ℓ, sin (θ s)) ∧
        LinearInputAreaVariation.area
          (fun s => θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s + c t * ξ₃.val s) ℓ =
            LinearInputAreaVariation.area θ ℓ := by
  obtain ⟨ξ₁, ξ₂, ξ₃, ⟨hx₁, hy₁, ha₁⟩, ⟨hx₂, hy₂, ha₂⟩, ⟨hx₃, hy₃, ha₃⟩⟩ :=
    LinearInputAreaRegularity.exists_normalized_constraint_directions hℓ hθ hnonconst
  let f := constraintParameters θ η.val ξ₁.val ξ₂.val ξ₃.val ℓ
  have hf : ContDiff ℝ 2 f := contDiff_constraintParameters hℓ.le hθ.continuous
    η.property.1.continuous ξ₁.property.1.continuous ξ₂.property.1.continuous ξ₃.property.1.continuous
  have hd (p : Parameters) := fderiv_constraintParameters_zero hℓ.le hθ.continuous
    η.property.1.continuous ξ₁.property.1.continuous ξ₂.property.1.continuous ξ₃.property.1.continuous p
  have hi (w : ℝ → ℝ) (hw : Continuous w) (p : Parameters) :=
    integral_parameterLinear (ℓ := ℓ) η.property.1.continuous ξ₁.property.1.continuous
      ξ₂.property.1.continuous ξ₃.property.1.continuous hw p
  have ht : (fderiv ℝ f 0).comp
      (ContinuousLinearMap.inl ℝ ℝ (ℝ × (ℝ × ℝ))) = 0 := by
    apply ContinuousLinearMap.ext
    intro t
    change fderiv ℝ f 0 (t, (0, (0, 0))) = (0, (0, 0))
    rw [hd]
    rw [hi (fun s => -sin (θ s)) (by fun_prop), hi _ hθ.cos.continuous,
      hi _ (LinearInputAreaVariation.continuous_moment hθ.continuous)]
    simp only [hηx, hηy, hηa, mul_zero, zero_mul, add_zero]
  have hc : (fderiv ℝ f 0).comp
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × (ℝ × ℝ))) =
      ContinuousLinearMap.id ℝ (ℝ × (ℝ × ℝ)) := by
    apply ContinuousLinearMap.ext
    intro p
    change fderiv ℝ f 0 (0, p) = p
    rw [hd]
    rw [hi (fun s => -sin (θ s)) (by fun_prop), hi _ hθ.cos.continuous,
      hi _ (LinearInputAreaVariation.continuous_moment hθ.continuous)]
    rw [hx₁, hy₁, ha₁, hx₂, hy₂, ha₂, hx₃, hy₃, ha₃]
    simp
  obtain ⟨g, hg, hg₀, hgd, hge⟩ := exists_implicit_correction hf ht hc
  refine ⟨ξ₁, ξ₂, ξ₃, (fun t => (g t).1), (fun t => (g t).2.1),
    (fun t => (g t).2.2), hg.fst, hg.snd.fst, hg.snd.snd,
    congrArg Prod.fst hg₀, congrArg (fun q => q.2.1) hg₀,
    congrArg (fun q => q.2.2) hg₀, hgd.fst, hgd.snd.fst, hgd.snd.snd, ?_⟩
  filter_upwards [hge] with t ht
  simp only [add_assoc]
  have hx := congrArg Prod.fst ht
  have hy := congrArg (fun q => q.2.1) ht
  have ha := congrArg (fun q => q.2.2) ht
  simp [f, constraintParameters, areaParameters, parameterLinear_apply, add_assoc] at hx hy ha
  refine ⟨hx, hy, ?_⟩
  rw [hx, hy] at ha
  linarith

end LinearInputAreaExactVariation
