import Elastica.Stationary
import Elastica.Variation
import Elastica.ConstraintRegularity
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! Exact endpoint-preserving finite-parameter angle variations. -/

noncomputable section
open Real Set MeasureTheory Filter Metric
open scoped Topology Interval
namespace Elastica

private abbrev Parameters := ℝ × (ℝ × ℝ)

/-- Continuity of a compact interval integral, for a continuous joint integrand. -/
theorem continuous_parameter_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Parameters → ℝ → E} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hG : Continuous (Function.uncurry G)) :
    Continuous (fun p => ∫ s in 0..ℓ, G p s) := by
  have h := continuous_parametric_integral_of_continuous (μ := volume) hG
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) ℓ))
  simpa only [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hℓ] using h

/-- A continuous parameter derivative on a compact rectangle supplies the bound
needed to differentiate the actual interval integral. -/
theorem hasFDerivAt_parameter_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : Parameters → ℝ → E} {D : Parameters → ℝ → Parameters →L[ℝ] E}
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hG : Continuous (Function.uncurry G)) (hD : Continuous (Function.uncurry D))
    (hd : ∀ p s, HasFDerivAt (fun q => G q s) (D p s) p) (p₀ : Parameters) :
    HasFDerivAt (fun p => ∫ s in 0..ℓ, G p s) (∫ s in 0..ℓ, D p₀ s) p₀ := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall p₀ 1).prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) ℓ))).exists_bound_of_continuousOn
      hD.continuousOn
  have hGs (p : Parameters) : Continuous (G p) := hG.comp (continuous_const.prodMk continuous_id)
  have hDs (p : Parameters) : Continuous (D p) := hD.comp (continuous_const.prodMk continuous_id)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball p₀ 1) (bound := fun _ => C) (ball_mem_nhds p₀ one_pos)
    (Eventually.of_forall fun p => (hGs p).aestronglyMeasurable)
    ((hGs p₀).intervalIntegrable 0 ℓ) (hDs p₀).aestronglyMeasurable
  · filter_upwards [] with s hs
    rw [uIoc_of_le hℓ] at hs
    intro p hp
    exact hC (p, s) ⟨ball_subset_closedBall hp, ⟨hs.1.le, hs.2⟩⟩
  · exact continuous_const.intervalIntegrable 0 ℓ
  · filter_upwards [] with s _ p _
    exact hd p s

/-- Two continuous actual parameter derivatives yield C² of the actual integral. -/
theorem contDiff_two_parameter_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : Parameters → ℝ → E} {D : Parameters → ℝ → Parameters →L[ℝ] E}
    {D₂ : Parameters → ℝ → Parameters →L[ℝ] (Parameters →L[ℝ] E)}
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hG : Continuous (Function.uncurry G)) (hD : Continuous (Function.uncurry D))
    (hD₂ : Continuous (Function.uncurry D₂))
    (hd : ∀ p s, HasFDerivAt (fun q => G q s) (D p s) p)
    (hd₂ : ∀ p s, HasFDerivAt (fun q => D q s) (D₂ p s) p) :
    ContDiff ℝ 2 (fun p => ∫ s in 0..ℓ, G p s) := by
  have h₁ := hasFDerivAt_parameter_intervalIntegral hℓ hG hD hd
  have h₂ := hasFDerivAt_parameter_intervalIntegral hℓ hD hD₂ hd₂
  have heq : fderiv ℝ (fun p => ∫ s in 0..ℓ, G p s) = fun p => ∫ s in 0..ℓ, D p s :=
    funext fun p => (h₁ p).fderiv
  rw [show (2 : WithTop ENat) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
  refine ⟨fun p => (h₁ p).differentiableAt, by simp, ?_⟩
  rw [heq, contDiff_one_iff_fderiv]
  refine ⟨fun p => (h₂ p).differentiableAt, ?_⟩
  have heq₂ : fderiv ℝ (fun p => ∫ s in 0..ℓ, D p s) = fun p => ∫ s in 0..ℓ, D₂ p s :=
    funext fun p => (h₂ p).fderiv
  rw [heq₂]
  exact continuous_parameter_intervalIntegral hℓ hD₂

theorem hasFDerivAt_integral_linear_parameters
    {ρ κ : ℝ → ℝ} {B : ℝ → Parameters →L[ℝ] ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hρ : ContDiff ℝ 1 ρ) (hκ : Continuous κ) (hB : Continuous B)
    (p : Parameters) :
    HasFDerivAt (fun p => ∫ s in 0..ℓ, ρ (κ s + B s p))
      (∫ s in 0..ℓ, deriv ρ (κ s + B s p) • B s) p := by
  have hp : Continuous (fun q : Parameters × ℝ => κ q.2 + B q.2 q.1) :=
    (hκ.comp continuous_snd).add ((hB.comp continuous_snd).clm_apply continuous_fst)
  apply hasFDerivAt_parameter_intervalIntegral
    (G := fun p s => ρ (κ s + B s p))
    (D := fun p s => deriv ρ (κ s + B s p) • B s) hℓ (hρ.continuous.comp hp)
    ((hρ.continuous_deriv_one.comp hp).smul (hB.comp continuous_snd))
  intro p s
  exact (hρ.differentiable one_ne_zero _).hasDerivAt.comp_hasFDerivAt p
    ((B s).hasFDerivAt.const_add (κ s))

theorem contDiff_two_integral_linear_parameters
    {ρ κ : ℝ → ℝ} {B : ℝ → Parameters →L[ℝ] ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hρ : ContDiff ℝ 2 ρ) (hκ : Continuous κ) (hB : Continuous B) :
    ContDiff ℝ 2 (fun p => ∫ s in 0..ℓ, ρ (κ s + B s p)) := by
  let D := fun (p : Parameters) (s : ℝ) => deriv ρ (κ s + B s p) • B s
  let D₂ := fun (p : Parameters) (s : ℝ) =>
    (deriv (deriv ρ) (κ s + B s p) • B s).smulRight (B s)
  have hp : Continuous (fun q : Parameters × ℝ => κ q.2 + B q.2 q.1) :=
    (hκ.comp continuous_snd).add ((hB.comp continuous_snd).clm_apply continuous_fst)
  have hρ₁ : ContDiff ℝ 1 (deriv ρ) := hρ.deriv'
  have hD : Continuous (Function.uncurry D) :=
    ((hρ₁.continuous.comp hp).smul (hB.comp continuous_snd))
  have hD₂ : Continuous (Function.uncurry D₂) := by
    dsimp [D₂, Function.uncurry]
    exact (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := Parameters)
      (F := Parameters →L[ℝ] ℝ)).continuous.comp
      (((hρ₁.continuous_deriv_one.comp hp).smul (hB.comp continuous_snd)).prodMk
        (hB.comp continuous_snd))
  apply contDiff_two_parameter_intervalIntegral
    (G := fun p s => ρ (κ s + B s p)) (D := D) (D₂ := D₂)
    hℓ (hρ.continuous.comp hp) hD hD₂
  · intro p s
    exact (hρ.differentiable (by norm_num) _).hasDerivAt.comp_hasFDerivAt p
      ((B s).hasFDerivAt.const_add (κ s))
  · intro p s
    exact ((hρ₁.differentiable one_ne_zero _).hasDerivAt.comp_hasFDerivAt p
      ((B s).hasFDerivAt.const_add (κ s))).smul_const (B s)

private def parameterLinear (η u v : ℝ → ℝ) (s : ℝ) : Parameters →L[ℝ] ℝ :=
  η s • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
    u s • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) +
    v s • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

private theorem parameterLinear_apply (η u v : ℝ → ℝ) (s : ℝ) (p : Parameters) :
    parameterLinear η u v s p = p.1 * η s + p.2.1 * u s + p.2.2 * v s := by
  change η s * p.1 + u s * p.2.1 + v s * p.2.2 = _
  ring

private theorem continuous_parameterLinear {η u v : ℝ → ℝ}
    (hη : Continuous η) (hu : Continuous u) (hv : Continuous v) :
    Continuous (parameterLinear η u v) := by
  unfold parameterLinear
  exact ((hη.smul continuous_const).add (hu.smul continuous_const)).add (hv.smul continuous_const)

/-- Two endpoint displacement integrals for the three-parameter angle family. -/
def endpointParameters (θ η u v : ℝ → ℝ) (ℓ : ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (∫ s in 0..ℓ, cos (θ s + parameterLinear η u v s p),
   ∫ s in 0..ℓ, sin (θ s + parameterLinear η u v s p))

theorem contDiff_endpointParameters {θ η u v : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hθ : Continuous θ) (hη : Continuous η)
    (hu : Continuous u) (hv : Continuous v) :
    ContDiff ℝ 2 (endpointParameters θ η u v ℓ) := by
  exact (contDiff_two_integral_linear_parameters hℓ Real.contDiff_cos hθ
    (continuous_parameterLinear hη hu hv)).prodMk
    (contDiff_two_integral_linear_parameters hℓ Real.contDiff_sin hθ
      (continuous_parameterLinear hη hu hv))

private theorem integral_parameterLinear {η u v w : ℝ → ℝ} {ℓ : ℝ}
    (hη : Continuous η) (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (p : Parameters) :
    (∫ s in 0..ℓ, w s * parameterLinear η u v s p) =
      p.1 * (∫ s in 0..ℓ, w s * η s) +
      p.2.1 * (∫ s in 0..ℓ, w s * u s) +
      p.2.2 * (∫ s in 0..ℓ, w s * v s) := by
  have hiη : IntervalIntegrable (fun s => p.1 * (w s * η s)) volume 0 ℓ :=
    (continuous_const.mul (hw.mul hη)).intervalIntegrable _ _
  have hiu : IntervalIntegrable (fun s => p.2.1 * (w s * u s)) volume 0 ℓ :=
    (continuous_const.mul (hw.mul hu)).intervalIntegrable _ _
  have hiv : IntervalIntegrable (fun s => p.2.2 * (w s * v s)) volume 0 ℓ :=
    (continuous_const.mul (hw.mul hv)).intervalIntegrable _ _
  calc
    _ = ∫ s in 0..ℓ, p.1 * (w s * η s) + p.2.1 * (w s * u s) +
        p.2.2 * (w s * v s) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp
      rw [parameterLinear_apply]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hiη.add hiu) hiv,
        intervalIntegral.integral_add hiη hiu]
      simp only [intervalIntegral.integral_const_mul]

theorem fderiv_endpointParameters_zero {θ η u v : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hθ : Continuous θ) (hη : Continuous η)
    (hu : Continuous u) (hv : Continuous v) (p : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (endpointParameters θ η u v ℓ) 0 p =
      (p.1 * (∫ s in 0..ℓ, -sin (θ s) * η s) +
        p.2.1 * (∫ s in 0..ℓ, -sin (θ s) * u s) +
        p.2.2 * (∫ s in 0..ℓ, -sin (θ s) * v s),
       p.1 * (∫ s in 0..ℓ, cos (θ s) * η s) +
        p.2.1 * (∫ s in 0..ℓ, cos (θ s) * u s) +
        p.2.2 * (∫ s in 0..ℓ, cos (θ s) * v s)) := by
  have hB := continuous_parameterLinear hη hu hv
  have hc := hasFDerivAt_integral_linear_parameters hℓ Real.contDiff_cos hθ hB (0 : Parameters)
  have hs := hasFDerivAt_integral_linear_parameters hℓ Real.contDiff_sin hθ hB (0 : Parameters)
  have hd : HasFDerivAt (endpointParameters θ η u v ℓ)
      ((∫ s in 0..ℓ, -sin (θ s) • parameterLinear η u v s).prod
       (∫ s in 0..ℓ, cos (θ s) • parameterLinear η u v s)) 0 := by
    convert hc.prodMk hs using 1
    all_goals first | rfl | simp only [map_zero, add_zero, Real.deriv_cos, Real.deriv_sin]
  rw [hd.fderiv]
  apply Prod.ext
  · change (∫ s in 0..ℓ, -sin (θ s) • parameterLinear η u v s) p = _
    rw [ContinuousLinearMap.intervalIntegral_apply
      (φ := fun s => -sin (θ s) • parameterLinear η u v s) (μ := volume) (v := p)
      (((Real.continuous_sin.comp hθ).neg.smul hB).intervalIntegrable 0 ℓ)]
    simpa only [smul_apply, smul_eq_mul, Function.comp_apply, Pi.neg_apply] using
      integral_parameterLinear hη hu hv (Real.continuous_sin.comp hθ).neg p
  · change (∫ s in 0..ℓ, cos (θ s) • parameterLinear η u v s) p = _
    rw [ContinuousLinearMap.intervalIntegral_apply
      (φ := fun s => cos (θ s) • parameterLinear η u v s) (μ := volume) (v := p)
      (((Real.continuous_cos.comp hθ).smul hB).intervalIntegrable 0 ℓ)]
    simpa only [smul_apply, smul_eq_mul, Function.comp_apply] using
      integral_parameterLinear hη hu hv (Real.continuous_cos.comp hθ) p

/-- Genuine finite-dimensional IFT, specialized to an identity correction block
and a zero tangent block. No solution function is assumed. -/
theorem exists_implicit_correction {f : (ℝ × (ℝ × ℝ)) → ℝ × ℝ}
    (hf : ContDiff ℝ 2 f)
    (ht : (fderiv ℝ f 0).comp (ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ)) = 0)
    (hc : (fderiv ℝ f 0).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) =
      ContinuousLinearMap.id ℝ (ℝ × ℝ)) :
    ∃ g : ℝ → ℝ × ℝ, ContDiffAt ℝ 2 g 0 ∧ g 0 = 0 ∧ HasDerivAt g 0 0 ∧
      ∀ᶠ t in 𝓝 0, f (t, g t) = f 0 := by
  have hi : ((fderiv ℝ f 0).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))).IsInvertible := by
    rw [hc]
    exact ⟨ContinuousLinearEquiv.refl ℝ (ℝ × ℝ), rfl⟩
  let h := hf.contDiffAt (x := (0 : Parameters))
  let g := h.implicitFunction (by norm_num) hi
  refine ⟨g, h.contDiffAt_implicitFunction (by norm_num) hi,
    h.implicitFunction_apply_self (by norm_num) hi, ?_,
    h.eventually_apply_implicitFunction (by norm_num) hi⟩
  have hd := h.hasStrictFDerivAt_implicitFunction (by norm_num) hi
  rw [ht] at hd
  simpa using hd.hasFDerivAt.hasDerivAt

/-- Every linearized feasible C¹ direction at a nonstraight curve is tangent to
an actual C²-parameter family preserving both endpoint positions exactly.
The two correction directions have zero endpoint values by their subtype. -/
theorem exists_exact_endpoint_variation {θ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hθ : ContDiff ℝ 1 θ)
    (hne : ∃ s ∈ Ioo 0 ℓ, deriv θ s ≠ 0)
    (η : variationSpace ℓ)
    (hηx : (∫ s in 0..ℓ, -sin (θ s) * η.val s) = 0)
    (hηy : (∫ s in 0..ℓ, cos (θ s) * η.val s) = 0) :
    ∃ ξ₁ ξ₂ : variationSpace ℓ, ∃ a b : ℝ → ℝ,
      ContDiffAt ℝ 2 a 0 ∧ ContDiffAt ℝ 2 b 0 ∧
      a 0 = 0 ∧ b 0 = 0 ∧ HasDerivAt a 0 0 ∧ HasDerivAt b 0 0 ∧
      ∀ᶠ t in 𝓝 0,
        (∫ s in 0..ℓ, cos (θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s)) =
          (∫ s in 0..ℓ, cos (θ s)) ∧
        (∫ s in 0..ℓ, sin (θ s + t * η.val s + a t * ξ₁.val s + b t * ξ₂.val s)) =
          (∫ s in 0..ℓ, sin (θ s)) := by
  obtain ⟨ξ₁, ξ₂, hx₁, hy₁, hx₂, hy₂⟩ := exists_normalized_constraint_directions hℓ hθ hne
  let f := endpointParameters θ η.val ξ₁.val ξ₂.val ℓ
  have hf : ContDiff ℝ 2 f := contDiff_endpointParameters hℓ.le hθ.continuous
    η.property.1.continuous ξ₁.property.1.continuous ξ₂.property.1.continuous
  have ht : (fderiv ℝ f 0).comp (ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ)) = 0 := by
    apply ContinuousLinearMap.ext
    intro t
    change fderiv ℝ f 0 (t, (0, 0)) = (0, 0)
    rw [fderiv_endpointParameters_zero hℓ.le hθ.continuous
      η.property.1.continuous ξ₁.property.1.continuous ξ₂.property.1.continuous]
    rw [hηx, hηy]
    simp
  have hc : (fderiv ℝ f 0).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    apply ContinuousLinearMap.ext
    intro p
    change fderiv ℝ f 0 (0, p) = p
    rw [fderiv_endpointParameters_zero hℓ.le hθ.continuous
      η.property.1.continuous ξ₁.property.1.continuous ξ₂.property.1.continuous]
    rw [hx₁, hy₁, hx₂, hy₂]
    simp
  obtain ⟨g, hg, hg₀, hgd, hge⟩ := exists_implicit_correction hf ht hc
  refine ⟨ξ₁, ξ₂, (fun t => (g t).1), (fun t => (g t).2), hg.fst, hg.snd,
    congrArg Prod.fst hg₀, congrArg Prod.snd hg₀, hgd.fst, hgd.snd, ?_⟩
  filter_upwards [hge] with t ht
  constructor
  · have hx := congrArg Prod.fst ht
    simpa [f, endpointParameters, parameterLinear_apply, add_assoc] using hx
  · have hy := congrArg Prod.snd ht
    simpa [f, endpointParameters, parameterLinear_apply, add_assoc] using hy

/-- The correction terms vanish to first order, so the realized tangent is η. -/
theorem corrected_angle_hasDerivAt {θ η u v a b : ℝ → ℝ}
    (ha : HasDerivAt a 0 0) (hb : HasDerivAt b 0 0) (s : ℝ) :
    HasDerivAt (fun t => θ s + t * η s + a t * u s + b t * v s) (η s) 0 := by
  convert (((hasDerivAt_id (0 : ℝ)).mul_const (η s)).const_add (θ s) |>.add
    (ha.mul_const (u s)) |>.add (hb.mul_const (v s))) using 1
  all_goals first | rfl | simp only [one_mul, zero_mul, add_zero]

/-- Correction by fixed-end angle variations preserves both prescribed angles. -/
theorem corrected_angle_endpoints {θ a b : ℝ → ℝ} {ℓ : ℝ}
    (η u v : variationSpace ℓ) (t : ℝ) :
    (θ 0 + t * η.val 0 + a t * u.val 0 + b t * v.val 0 = θ 0) ∧
    (θ ℓ + t * η.val ℓ + a t * u.val ℓ + b t * v.val ℓ = θ ℓ) := by
  simp [η.property.2.1, η.property.2.2, u.property.2.1, u.property.2.2,
    v.property.2.1, v.property.2.2]

end Elastica
