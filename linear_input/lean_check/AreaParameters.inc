import Elastica.ExactVariation
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Actual C² dependence of reconstructed area on four angle parameters. -/

noncomputable section
open Real Set MeasureTheory Filter Metric
open scoped Topology Interval
namespace LinearInputAreaParameters

open Elastica LinearInputAreaVariation

abbrev Parameters := ℝ × (ℝ × (ℝ × ℝ))

local instance : IsTopologicalAddGroup (Parameters →L[ℝ] (Parameters →L[ℝ] ℝ)) :=
  ContinuousLinearMap.isTopologicalAddGroup

local instance : ContinuousAdd (Parameters →L[ℝ] (Parameters →L[ℝ] ℝ)) :=
  (inferInstance : IsTopologicalAddGroup (Parameters →L[ℝ] (Parameters →L[ℝ] ℝ))).toContinuousAdd

theorem continuous_parameter_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Parameters → ℝ → E} {ℓ : ℝ}
    (hG : Continuous (Function.uncurry G)) :
    Continuous (fun p => ∫ s in 0..ℓ, G p s) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG 0 ℓ

theorem continuous_parameter_primitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Parameters → ℝ → E} (hG : Continuous (Function.uncurry G)) :
    Continuous (fun p : Parameters × ℝ => ∫ s in 0..p.2, G p.1 s) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (s := fun p : Parameters × ℝ => p.2) ?_ continuous_snd
  exact hG.comp ((continuous_fst.fst).prodMk continuous_snd)

theorem hasFDerivAt_parameter_intervalIntegral_any
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : Parameters → ℝ → E} {D : Parameters → ℝ → Parameters →L[ℝ] E}
    {ℓ : ℝ}
    (hG : Continuous (Function.uncurry G)) (hD : Continuous (Function.uncurry D))
    (hd : ∀ p s, HasFDerivAt (fun q => G q s) (D p s) p) (p₀ : Parameters) :
    HasFDerivAt (fun p => ∫ s in 0..ℓ, G p s) (∫ s in 0..ℓ, D p₀ s) p₀ := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall p₀ 1).prod (isCompact_uIcc : IsCompact (uIcc (0 : ℝ) ℓ))).exists_bound_of_continuousOn
      hD.continuousOn
  have hGs (p : Parameters) : Continuous (G p) := hG.comp (continuous_const.prodMk continuous_id)
  have hDs (p : Parameters) : Continuous (D p) := hD.comp (continuous_const.prodMk continuous_id)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball p₀ 1) (bound := fun _ => C) (ball_mem_nhds p₀ one_pos)
    (Eventually.of_forall fun p => (hGs p).aestronglyMeasurable)
    ((hGs p₀).intervalIntegrable 0 ℓ) (hDs p₀).aestronglyMeasurable
  · filter_upwards [] with s hs
    intro p hp
    exact hC (p, s) ⟨ball_subset_closedBall hp, uIoc_subset_uIcc hs⟩
  · exact continuous_const.intervalIntegrable 0 ℓ
  · filter_upwards [] with s _ p _
    exact hd p s

theorem hasFDerivAt_parameter_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : Parameters → ℝ → E} {D : Parameters → ℝ → Parameters →L[ℝ] E}
    {ℓ : ℝ} (_hℓ : 0 ≤ ℓ)
    (hG : Continuous (Function.uncurry G)) (hD : Continuous (Function.uncurry D))
    (hd : ∀ p s, HasFDerivAt (fun q => G q s) (D p s) p) (p₀ : Parameters) :
    HasFDerivAt (fun p => ∫ s in 0..ℓ, G p s) (∫ s in 0..ℓ, D p₀ s) p₀ :=
  hasFDerivAt_parameter_intervalIntegral_any hG hD hd p₀

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
  exact continuous_parameter_intervalIntegral hD₂

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

theorem continuous_smulRight_parameter
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : Parameters × ℝ → Parameters →L[ℝ] ℝ} {B : Parameters × ℝ → F}
    (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun q => (A q).smulRight (B q)) :=
  (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := Parameters) (F := F)).continuous.comp
    (hA.prodMk hB)

/-- Product closure before integration, with both actual parameter derivatives. -/
theorem contDiff_two_integral_mul
    {A B : Parameters → ℝ → ℝ}
    {D E : Parameters → ℝ → Parameters →L[ℝ] ℝ}
    {D₂ E₂ : Parameters → ℝ → Parameters →L[ℝ] (Parameters →L[ℝ] ℝ)}
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hA : Continuous (Function.uncurry A)) (hB : Continuous (Function.uncurry B))
    (hD : Continuous (Function.uncurry D)) (hE : Continuous (Function.uncurry E))
    (hD₂ : Continuous (Function.uncurry D₂)) (hE₂ : Continuous (Function.uncurry E₂))
    (hdA : ∀ p s, HasFDerivAt (fun q => A q s) (D p s) p)
    (hdB : ∀ p s, HasFDerivAt (fun q => B q s) (E p s) p)
    (hdD : ∀ p s, HasFDerivAt (fun q => D q s) (D₂ p s) p)
    (hdE : ∀ p s, HasFDerivAt (fun q => E q s) (E₂ p s) p) :
    ContDiff ℝ 2 (fun p => ∫ s in 0..ℓ, A p s * B p s) := by
  apply contDiff_two_parameter_intervalIntegral
    (G := fun p s => A p s * B p s)
    (D := fun p s => A p s • E p s + B p s • D p s)
    (D₂ := fun p s =>
      (A p s • E₂ p s + (D p s).smulRight (E p s)) +
      (B p s • D₂ p s + (E p s).smulRight (D p s))) hℓ
    (hA.mul hB) ((hA.smul hE).add (hB.smul hD))
    (((hA.smul hE₂).add (continuous_smulRight_parameter hD hE)).add
      ((hB.smul hD₂).add (continuous_smulRight_parameter hE hD)))
  · intro p s
    exact (hdA p s).mul (hdB p s)
  · intro p s
    exact ((hdA p s).smul (hdE p s)).add ((hdB p s).smul (hdD p s))

/-- One primitive factor and one pointwise factor, each depending on actual linear parameters. -/
theorem contDiff_two_integral_primitive_mul
    {ρ τ θ : ℝ → ℝ} {B : ℝ → Parameters →L[ℝ] ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hρ : ContDiff ℝ 2 ρ) (hτ : ContDiff ℝ 2 τ)
    (hθ : Continuous θ) (hB : Continuous B) :
    ContDiff ℝ 2 (fun p => ∫ s in 0..ℓ,
      (∫ q in 0..s, ρ (θ q + B q p)) * τ (θ s + B s p)) := by
  let R := fun (p : Parameters) (s : ℝ) => ρ (θ s + B s p)
  let D := fun (p : Parameters) (s : ℝ) => deriv ρ (θ s + B s p) • B s
  let D₂ := fun (p : Parameters) (s : ℝ) =>
    (deriv (deriv ρ) (θ s + B s p) • B s).smulRight (B s)
  let T := fun (p : Parameters) (s : ℝ) => τ (θ s + B s p)
  let E := fun (p : Parameters) (s : ℝ) => deriv τ (θ s + B s p) • B s
  let E₂ := fun (p : Parameters) (s : ℝ) =>
    (deriv (deriv τ) (θ s + B s p) • B s).smulRight (B s)
  have hp : Continuous (fun q : Parameters × ℝ => θ q.2 + B q.2 q.1) :=
    (hθ.comp continuous_snd).add ((hB.comp continuous_snd).clm_apply continuous_fst)
  have hρ₁ : ContDiff ℝ 1 (deriv ρ) := hρ.deriv'
  have hτ₁ : ContDiff ℝ 1 (deriv τ) := hτ.deriv'
  have hR : Continuous (Function.uncurry R) := hρ.continuous.comp hp
  have hD : Continuous (Function.uncurry D) :=
    (hρ₁.continuous.comp hp).smul (hB.comp continuous_snd)
  have hD₂ : Continuous (Function.uncurry D₂) :=
    continuous_smulRight_parameter
      ((hρ₁.continuous_deriv_one.comp hp).smul (hB.comp continuous_snd))
      (hB.comp continuous_snd)
  have hT : Continuous (Function.uncurry T) := hτ.continuous.comp hp
  have hE : Continuous (Function.uncurry E) :=
    (hτ₁.continuous.comp hp).smul (hB.comp continuous_snd)
  have hE₂ : Continuous (Function.uncurry E₂) :=
    continuous_smulRight_parameter
      ((hτ₁.continuous_deriv_one.comp hp).smul (hB.comp continuous_snd))
      (hB.comp continuous_snd)
  have hdR (p : Parameters) (s : ℝ) : HasFDerivAt (fun q => R q s) (D p s) p :=
    (hρ.differentiable (by norm_num) _).hasDerivAt.comp_hasFDerivAt p
      ((B s).hasFDerivAt.const_add (θ s))
  have hdD (p : Parameters) (s : ℝ) : HasFDerivAt (fun q => D q s) (D₂ p s) p :=
    ((hρ₁.differentiable one_ne_zero _).hasDerivAt.comp_hasFDerivAt p
      ((B s).hasFDerivAt.const_add (θ s))).smul_const (B s)
  have hdT (p : Parameters) (s : ℝ) : HasFDerivAt (fun q => T q s) (E p s) p :=
    (hτ.differentiable (by norm_num) _).hasDerivAt.comp_hasFDerivAt p
      ((B s).hasFDerivAt.const_add (θ s))
  have hdE (p : Parameters) (s : ℝ) : HasFDerivAt (fun q => E q s) (E₂ p s) p :=
    ((hτ₁.differentiable one_ne_zero _).hasDerivAt.comp_hasFDerivAt p
      ((B s).hasFDerivAt.const_add (θ s))).smul_const (B s)
  exact contDiff_two_integral_mul
    (A := fun p s => ∫ q in 0..s, R p q) (B := T)
    (D := fun p s => ∫ q in 0..s, D p q) (E := E)
    (D₂ := fun p s => ∫ q in 0..s, D₂ p q) (E₂ := E₂) hℓ
    (continuous_parameter_primitive hR) hT
    (continuous_parameter_primitive hD) hE
    (continuous_parameter_primitive
      (E := Parameters →L[ℝ] (Parameters →L[ℝ] ℝ)) (G := D₂) hD₂) hE₂
    (fun p s => hasFDerivAt_parameter_intervalIntegral_any hR hD hdR p)
    hdT
    (fun p s => hasFDerivAt_parameter_intervalIntegral_any hD hD₂ hdD p)
    hdE

def parameterLinear (η ξ₁ ξ₂ ξ₃ : ℝ → ℝ) (s : ℝ) : Parameters →L[ℝ] ℝ :=
  η s • ContinuousLinearMap.fst ℝ ℝ (ℝ × (ℝ × ℝ)) +
    ξ₁ s • ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ)))) +
    ξ₂ s • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))))) +
    ξ₃ s • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ)))))

theorem parameterLinear_apply (η ξ₁ ξ₂ ξ₃ : ℝ → ℝ) (s : ℝ) (p : Parameters) :
    parameterLinear η ξ₁ ξ₂ ξ₃ s p =
      p.1 * η s + p.2.1 * ξ₁ s + p.2.2.1 * ξ₂ s + p.2.2.2 * ξ₃ s := by
  change η s * p.1 + ξ₁ s * p.2.1 + ξ₂ s * p.2.2.1 + ξ₃ s * p.2.2.2 = _
  ring

theorem continuous_parameterLinear {η ξ₁ ξ₂ ξ₃ : ℝ → ℝ}
    (hη : Continuous η) (hξ₁ : Continuous ξ₁) (hξ₂ : Continuous ξ₂) (hξ₃ : Continuous ξ₃) :
    Continuous (parameterLinear η ξ₁ ξ₂ ξ₃) := by
  unfold parameterLinear
  exact (((hη.smul continuous_const).add (hξ₁.smul continuous_const)).add
    (hξ₂.smul continuous_const)).add (hξ₃.smul continuous_const)

def areaParameters (θ η ξ₁ ξ₂ ξ₃ : ℝ → ℝ) (ℓ : ℝ) (p : Parameters) : ℝ :=
  area (fun s => θ s + parameterLinear η ξ₁ ξ₂ ξ₃ s p) ℓ

/-- The area functional is genuinely C² in the four parameters. -/
theorem contDiff_area_linear_parameters
    {θ : ℝ → ℝ} {B : ℝ → Parameters →L[ℝ] ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hθ : Continuous θ) (hB : Continuous B) :
    ContDiff ℝ 2 (fun p => area (fun s => θ s + B s p) ℓ) := by
  have h₁ := contDiff_two_integral_primitive_mul hℓ Real.contDiff_cos Real.contDiff_sin hθ hB
  have h₂ := contDiff_two_integral_primitive_mul hℓ Real.contDiff_sin Real.contDiff_cos hθ hB
  have he : (fun p => area (fun s => θ s + B s p) ℓ) =
      (fun p => (1 / 2) *
        ((∫ s in 0..ℓ, (∫ q in 0..s, cos (θ q + B q p)) * sin (θ s + B s p)) -
         (∫ s in 0..ℓ, (∫ q in 0..s, sin (θ q + B q p)) * cos (θ s + B s p)))) := by
    funext p
    have hp : Continuous (fun s => θ s + B s p) := hθ.add (hB.clm_apply continuous_const)
    have hX : Continuous (xCoord (fun s => θ s + B s p) 0) :=
      continuous_iff_continuousAt.mpr fun s => (hasDerivAt_xCoord hp 0 s).continuousAt
    have hY : Continuous (yCoord (fun s => θ s + B s p) 0) :=
      continuous_iff_continuousAt.mpr fun s => (hasDerivAt_yCoord hp 0 s).continuousAt
    unfold area
    rw [intervalIntegral.integral_sub (μ := volume)
      (f := fun s => xCoord (fun s => θ s + B s p) 0 s * sin (θ s + B s p))
      (g := fun s => yCoord (fun s => θ s + B s p) 0 s * cos (θ s + B s p))
      ((hX.mul (Real.continuous_sin.comp hp)).intervalIntegrable 0 ℓ)
      ((hY.mul (Real.continuous_cos.comp hp)).intervalIntegrable 0 ℓ)]
    simp only [xCoord, yCoord, zero_add]
  rw [he]
  exact contDiff_const.mul (h₁.sub h₂)

theorem contDiff_areaParameters {θ η ξ₁ ξ₂ ξ₃ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hθ : Continuous θ) (hη : Continuous η)
    (hξ₁ : Continuous ξ₁) (hξ₂ : Continuous ξ₂) (hξ₃ : Continuous ξ₃) :
    ContDiff ℝ 2 (areaParameters θ η ξ₁ ξ₂ ξ₃ ℓ) :=
  contDiff_area_linear_parameters hℓ hθ (continuous_parameterLinear hη hξ₁ hξ₂ hξ₃)

end LinearInputAreaParameters
