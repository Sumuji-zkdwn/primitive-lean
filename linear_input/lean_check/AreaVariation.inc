import Elastica.Geometry
import Elastica.Variation
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Signed area of the actual tangent-angle reconstruction and its actual variation. -/

noncomputable section
open Real Set MeasureTheory Filter Metric
open scoped Topology Interval
namespace LinearInputAreaVariation

open Elastica

/-- Oriented area closed by the chord from the endpoint to the origin. -/
def area (θ : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  (1 / 2) * ∫ s in 0..ℓ,
    xCoord θ 0 s * sin (θ s) - yCoord θ 0 s * cos (θ s)

/-- Compact domination for a genuine continuous parameter derivative. -/
theorem hasDerivAt_parameter_integral
    {G D : ℝ → ℝ → ℝ} (hG : Continuous (Function.uncurry G))
    (hD : Continuous (Function.uncurry D))
    (hd : ∀ t s, HasDerivAt (fun p => G p s) (D t s) t) (ℓ t₀ : ℝ) :
    HasDerivAt (fun t => ∫ s in 0..ℓ, G t s) (∫ s in 0..ℓ, D t₀ s) t₀ := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall t₀ 1).prod (isCompact_uIcc : IsCompact (uIcc (0 : ℝ) ℓ))).exists_bound_of_continuousOn
      hD.continuousOn
  have hGs (t : ℝ) : Continuous (G t) := hG.comp (continuous_const.prodMk continuous_id)
  have hDs (t : ℝ) : Continuous (D t) := hD.comp (continuous_const.prodMk continuous_id)
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := ball t₀ 1) (bound := fun _ => C) (ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall fun t => (hGs t).aestronglyMeasurable)
    ((hGs t₀).intervalIntegrable 0 ℓ) (hDs t₀).aestronglyMeasurable
    ?_ (continuous_const.intervalIntegrable 0 ℓ) ?_).2
  · filter_upwards [] with s hs
    intro t ht
    exact hC (t, s) ⟨ball_subset_closedBall ht, uIoc_subset_uIcc hs⟩
  · filter_upwards [] with s _ t _
    exact hd t s

/-- A primitive with jointly continuous parameter and endpoint. -/
theorem continuous_primitive_parameter {G : ℝ → ℝ → ℝ}
    (hG : Continuous (Function.uncurry G)) :
    Continuous (fun p : ℝ × ℝ => ∫ s in 0..p.2, G p.1 s) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (s := fun p : ℝ × ℝ => p.2) ?_ continuous_snd
  exact hG.comp ((continuous_fst.fst).prodMk continuous_snd)

/-- Parameter derivative of the actual horizontal reconstructed coordinate. -/
theorem hasDerivAt_xCoord_variation {θ η : ℝ → ℝ}
    (hθ : Continuous θ) (hη : Continuous η) (t s : ℝ) :
    HasDerivAt (fun p => xCoord (angleVariation θ η p) 0 s)
      (∫ q in 0..s, -sin (θ q + t * η q) * η q) t := by
  have hc : Continuous (fun p : ℝ × ℝ => θ p.2 + p.1 * η p.2) :=
    (hθ.comp continuous_snd).add (continuous_fst.mul (hη.comp continuous_snd))
  have h := hasDerivAt_parameter_integral
    (G := fun p q => cos (θ q + p * η q))
    (D := fun p q => -sin (θ q + p * η q) * η q)
    (Real.continuous_cos.comp hc)
    (((Real.continuous_sin.comp hc).neg).mul (hη.comp continuous_snd))
    (fun p q => by simpa using (((hasDerivAt_id p).mul_const (η q)).const_add (θ q)).cos) s t
  simpa only [xCoord, angleVariation, zero_add] using h

/-- Parameter derivative of the actual vertical reconstructed coordinate. -/
theorem hasDerivAt_yCoord_variation {θ η : ℝ → ℝ}
    (hθ : Continuous θ) (hη : Continuous η) (t s : ℝ) :
    HasDerivAt (fun p => yCoord (angleVariation θ η p) 0 s)
      (∫ q in 0..s, cos (θ q + t * η q) * η q) t := by
  have hc : Continuous (fun p : ℝ × ℝ => θ p.2 + p.1 * η p.2) :=
    (hθ.comp continuous_snd).add (continuous_fst.mul (hη.comp continuous_snd))
  have h := hasDerivAt_parameter_integral
    (G := fun p q => sin (θ q + p * η q))
    (D := fun p q => cos (θ q + p * η q) * η q)
    (Real.continuous_sin.comp hc)
    ((Real.continuous_cos.comp hc).mul (hη.comp continuous_snd))
    (fun p q => by simpa using (((hasDerivAt_id p).mul_const (η q)).const_add (θ q)).sin) s t
  simpa only [yCoord, angleVariation, zero_add] using h

/-- Continuity of the area moment entering the first variation. -/
theorem continuous_moment {θ : ℝ → ℝ} (hθ : Continuous θ) :
    Continuous (fun s => xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) := by
  have hx : Continuous (xCoord θ 0) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_xCoord hθ 0 s).continuousAt
  have hy : Continuous (yCoord θ 0) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_yCoord hθ 0 s).continuousAt
  exact (hx.mul (Real.continuous_cos.comp hθ)).add (hy.mul (Real.continuous_sin.comp hθ))

/-- Differentiate the reconstructed area integral before removing its boundary term. -/
theorem hasDerivAt_area_variation_raw {θ η : ℝ → ℝ}
    (hθ : Continuous θ) (hη : Continuous η) (ℓ : ℝ) :
    HasDerivAt (fun t => area (angleVariation θ η t) ℓ)
      ((1 / 2) * ∫ s in 0..ℓ,
        (∫ q in 0..s, -sin (θ q) * η q) * sin (θ s) +
          xCoord θ 0 s * (cos (θ s) * η s) -
        ((∫ q in 0..s, cos (θ q) * η q) * cos (θ s) +
          yCoord θ 0 s * (-sin (θ s) * η s))) 0 := by
  have hc : Continuous (fun p : ℝ × ℝ => θ p.2 + p.1 * η p.2) :=
    (hθ.comp continuous_snd).add (continuous_fst.mul (hη.comp continuous_snd))
  have hX : Continuous (fun p : ℝ × ℝ => xCoord (angleVariation θ η p.1) 0 p.2) := by
    simpa only [xCoord, angleVariation, zero_add] using
      continuous_primitive_parameter (G := fun t s => cos (θ s + t * η s))
        (Real.continuous_cos.comp hc)
  have hY : Continuous (fun p : ℝ × ℝ => yCoord (angleVariation θ η p.1) 0 p.2) := by
    simpa only [yCoord, angleVariation, zero_add] using
      continuous_primitive_parameter (G := fun t s => sin (θ s + t * η s))
        (Real.continuous_sin.comp hc)
  have hU : Continuous (fun p : ℝ × ℝ => ∫ q in 0..p.2, -sin (θ q + p.1 * η q) * η q) :=
    continuous_primitive_parameter (G := fun t q => -sin (θ q + t * η q) * η q)
      ((Real.continuous_sin.comp hc).neg.mul (hη.comp continuous_snd))
  have hV : Continuous (fun p : ℝ × ℝ => ∫ q in 0..p.2, cos (θ q + p.1 * η q) * η q) :=
    continuous_primitive_parameter (G := fun t q => cos (θ q + t * η q) * η q)
      ((Real.continuous_cos.comp hc).mul (hη.comp continuous_snd))
  have hd := hasDerivAt_parameter_integral
    (G := fun t s => xCoord (angleVariation θ η t) 0 s * sin (θ s + t * η s) -
      yCoord (angleVariation θ η t) 0 s * cos (θ s + t * η s))
    (D := fun t s =>
      (∫ q in 0..s, -sin (θ q + t * η q) * η q) * sin (θ s + t * η s) +
        xCoord (angleVariation θ η t) 0 s * (cos (θ s + t * η s) * η s) -
      ((∫ q in 0..s, cos (θ q + t * η q) * η q) * cos (θ s + t * η s) +
        yCoord (angleVariation θ η t) 0 s * (-sin (θ s + t * η s) * η s)))
    ((hX.mul (Real.continuous_sin.comp hc)).sub (hY.mul (Real.continuous_cos.comp hc)))
    (((hU.mul (Real.continuous_sin.comp hc)).add
      (hX.mul ((Real.continuous_cos.comp hc).mul (hη.comp continuous_snd)))).sub
      ((hV.mul (Real.continuous_cos.comp hc)).add
        (hY.mul ((Real.continuous_sin.comp hc).neg.mul (hη.comp continuous_snd)))))
    (fun t s => by
      have ha : HasDerivAt (fun p => θ s + p * η s) (η s) t := by
        simpa using ((hasDerivAt_id t).mul_const (η s)).const_add (θ s)
      exact ((hasDerivAt_xCoord_variation hθ hη t s).mul ha.sin).sub
        ((hasDerivAt_yCoord_variation hθ hη t s).mul ha.cos)) ℓ 0
  have hzero : angleVariation θ η 0 = θ := by ext s; simp [angleVariation]
  have hh := hd.const_mul (1 / 2)
  rw [hzero] at hh
  simpa only [area, angleVariation, zero_mul, add_zero] using hh

/-- Integration by parts displays the endpoint contribution of the actual area derivative. -/
theorem area_variation_integral_eq {θ η : ℝ → ℝ}
    (hθ : Continuous θ) (hη : Continuous η) (ℓ : ℝ) :
    ((1 / 2) * ∫ s in 0..ℓ,
        (∫ q in 0..s, -sin (θ q) * η q) * sin (θ s) +
          xCoord θ 0 s * (cos (θ s) * η s) -
        ((∫ q in 0..s, cos (θ q) * η q) * cos (θ s) +
          yCoord θ 0 s * (-sin (θ s) * η s))) =
      (∫ s in 0..ℓ, (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) * η s) -
      (xCoord θ 0 ℓ * (∫ s in 0..ℓ, cos (θ s) * η s) +
        yCoord θ 0 ℓ * (∫ s in 0..ℓ, sin (θ s) * η s)) / 2 := by
  let U := fun s => ∫ q in 0..s, -sin (θ q) * η q
  let V := fun s => ∫ q in 0..s, cos (θ q) * η q
  have hC := Real.continuous_cos.comp hθ
  have hS := Real.continuous_sin.comp hθ
  have hX : Continuous (xCoord θ 0) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_xCoord hθ 0 s).continuousAt
  have hY : Continuous (yCoord θ 0) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_yCoord hθ 0 s).continuousAt
  have hUd (s : ℝ) : HasDerivAt U (-sin (θ s) * η s) s :=
    ((hS.neg.mul hη).integral_hasStrictDerivAt 0 s).hasDerivAt
  have hVd (s : ℝ) : HasDerivAt V (cos (θ s) * η s) s :=
    ((hC.mul hη).integral_hasStrictDerivAt 0 s).hasDerivAt
  have hU : Continuous U := continuous_iff_continuousAt.mpr fun s => (hUd s).continuousAt
  have hV : Continuous V := continuous_iff_continuousAt.mpr fun s => (hVd s).continuousAt
  have hpartsU : (∫ s in 0..ℓ, U s * sin (θ s)) =
      U ℓ * yCoord θ 0 ℓ - (∫ s in 0..ℓ, yCoord θ 0 s * (-sin (θ s) * η s)) := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun s _ => hUd s) (fun s _ => hasDerivAt_yCoord hθ 0 s)
      ((hS.neg.mul hη).intervalIntegrable 0 ℓ) (hS.intervalIntegrable 0 ℓ)
    simpa only [yCoord_zero, mul_zero, zero_mul, sub_zero, mul_comm] using h
  have hpartsV : (∫ s in 0..ℓ, V s * cos (θ s)) =
      V ℓ * xCoord θ 0 ℓ - (∫ s in 0..ℓ, xCoord θ 0 s * (cos (θ s) * η s)) := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun s _ => hVd s) (fun s _ => hasDerivAt_xCoord hθ 0 s)
      ((hC.mul hη).intervalIntegrable 0 ℓ) (hC.intervalIntegrable 0 ℓ)
    simpa only [xCoord_zero, mul_zero, zero_mul, sub_zero, mul_comm] using h
  have hmoment :
      (∫ s in 0..ℓ, (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) * η s) =
      (∫ s in 0..ℓ, xCoord θ 0 s * (cos (θ s) * η s)) -
      (∫ s in 0..ℓ, yCoord θ 0 s * (-sin (θ s) * η s)) := by
    rw [← intervalIntegral.integral_sub (μ := volume)
      (f := fun s => xCoord θ 0 s * (cos (θ s) * η s))
      (g := fun s => yCoord θ 0 s * (-sin (θ s) * η s))
      ((hX.mul (hC.mul hη)).intervalIntegrable 0 ℓ)
      ((hY.mul (hS.neg.mul hη)).intervalIntegrable 0 ℓ)]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  have hUne : U ℓ = -(∫ s in 0..ℓ, sin (θ s) * η s) := by
    simp only [U, neg_mul, intervalIntegral.integral_neg]
  change (1 / 2) * (∫ s in 0..ℓ, U s * sin (θ s) +
      xCoord θ 0 s * (cos (θ s) * η s) -
      (V s * cos (θ s) + yCoord θ 0 s * (-sin (θ s) * η s))) = _
  rw [intervalIntegral.integral_sub (μ := volume)
    (f := fun s => U s * sin (θ s) + xCoord θ 0 s * (cos (θ s) * η s))
    (g := fun s => V s * cos (θ s) + yCoord θ 0 s * (-sin (θ s) * η s))
    (((hU.mul hS).add (hX.mul (hC.mul hη))).intervalIntegrable 0 ℓ)
    (((hV.mul hC).add (hY.mul (hS.neg.mul hη))).intervalIntegrable 0 ℓ),
    intervalIntegral.integral_add (μ := volume)
      (f := fun s => U s * sin (θ s))
      (g := fun s => xCoord θ 0 s * (cos (θ s) * η s))
      ((hU.mul hS).intervalIntegrable 0 ℓ)
      ((hX.mul (hC.mul hη)).intervalIntegrable 0 ℓ),
    intervalIntegral.integral_add (μ := volume)
      (f := fun s => V s * cos (θ s))
      (g := fun s => yCoord θ 0 s * (-sin (θ s) * η s))
      ((hV.mul hC).intervalIntegrable 0 ℓ)
      ((hY.mul (hS.neg.mul hη)).intervalIntegrable 0 ℓ),
    hpartsU, hpartsV, hmoment, hUne]
  dsimp [V]
  ring

/-- First variation of signed area with its explicit endpoint correction. -/
theorem hasDerivAt_area_variation {θ η : ℝ → ℝ}
    (hθ : Continuous θ) (hη : Continuous η) (ℓ : ℝ) :
    HasDerivAt (fun t => area (angleVariation θ η t) ℓ)
      ((∫ s in 0..ℓ, (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) * η s) -
      (xCoord θ 0 ℓ * (∫ s in 0..ℓ, cos (θ s) * η s) +
        yCoord θ 0 ℓ * (∫ s in 0..ℓ, sin (θ s) * η s)) / 2) 0 := by
  rw [← area_variation_integral_eq hθ hη ℓ]
  exact hasDerivAt_area_variation_raw hθ hη ℓ

/-- Endpoint-feasible directions cancel the complete boundary correction. -/
theorem hasDerivAt_area_variation_feasible {θ η : ℝ → ℝ} {ℓ : ℝ}
    (_hℓ : 0 ≤ ℓ) (hθ : Continuous θ) (hη : Continuous η)
    (hx : (∫ s in 0..ℓ, -sin (θ s) * η s) = 0)
    (hy : (∫ s in 0..ℓ, cos (θ s) * η s) = 0) :
    HasDerivAt (fun t => area (angleVariation θ η t) ℓ)
      (∫ s in 0..ℓ, (xCoord θ 0 s * cos (θ s) + yCoord θ 0 s * sin (θ s)) * η s) 0 := by
  have hx' : (∫ s in 0..ℓ, sin (θ s) * η s) = 0 := by
    simpa only [neg_mul, intervalIntegral.integral_neg, neg_eq_zero] using hx
  simpa only [hy, hx', mul_zero, add_zero, zero_div, sub_zero] using
    hasDerivAt_area_variation hθ hη ℓ

end LinearInputAreaVariation
