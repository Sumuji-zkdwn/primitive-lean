import Elastica.Variation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Second variation derived from the curvature energy

The first derivative is identified at every parameter value, then differentiated
under the integral again. A compact rectangle provides the required uniform
bound. The result uses C² density and C¹ angles, so the original C³ assumptions
are more than sufficient. No positivity, minimizer, or evolution is asserted.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Elastica

/-- A weighted form of differentiation under the curvature integral, valid at
every real parameter value. The weight does not depend on that parameter. -/
theorem hasDerivAt_weighted_integral_variation {ε κ v w : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 1 ε) (hκ : Continuous κ)
    (hv : Continuous v) (hw : Continuous w) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ s in 0..ℓ, ε (κ s + t * v s) * w s)
      (∫ s in 0..ℓ, deriv ε (κ s + t₀ * v s) * v s * w s) t₀ := by
  have hεd : Differentiable ℝ ε := hε.differentiable one_ne_zero
  have hε' : Continuous (deriv ε) := hε.continuous_deriv_one
  have hc : Continuous
      (fun p : ℝ × ℝ => deriv ε (κ p.2 + p.1 * v p.2) * v p.2 * w p.2) :=
    ((hε'.comp ((hκ.comp continuous_snd).add
      (continuous_fst.mul (hv.comp continuous_snd)))).mul
      (hv.comp continuous_snd)).mul (hw.comp continuous_snd)
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc : IsCompact (Icc (t₀ - 1) (t₀ + 1))).prod
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) ℓ))).exists_bound_of_continuousOn hc.continuousOn
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun s => ε (κ s + t * v s) * w s) (volume.restrict (Ioc 0 ℓ)) :=
    ((hε.continuous.comp (hκ.add (continuous_const.mul hv))).mul hw).aestronglyMeasurable
  have hint : Integrable (fun s => ε (κ s + t₀ * v s) * w s)
      (volume.restrict (Ioc 0 ℓ)) :=
    (((hε.continuous.comp (hκ.add (continuous_const.mul hv))).mul hw).intervalIntegrable 0 ℓ).1
  have hmeas' : AEStronglyMeasurable
      (fun s => deriv ε (κ s + t₀ * v s) * v s * w s)
      (volume.restrict (Ioc 0 ℓ)) :=
    (((hε'.comp (hκ.add (continuous_const.mul hv))).mul hv).mul hw).aestronglyMeasurable
  have hbound : ∀ᵐ s ∂volume.restrict (Ioc 0 ℓ),
      ∀ t ∈ Ioo (t₀ - 1) (t₀ + 1), ‖deriv ε (κ s + t * v s) * v s * w s‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro t ht
    exact hC (t, s) ⟨⟨ht.1.le, ht.2.le⟩, ⟨hs.1.le, hs.2⟩⟩
  have hdiff : ∀ᵐ s ∂volume.restrict (Ioc 0 ℓ), ∀ t ∈ Ioo (t₀ - 1) (t₀ + 1),
      HasDerivAt (fun t => ε (κ s + t * v s) * w s)
        (deriv ε (κ s + t * v s) * v s * w s) t := by
    filter_upwards [] with s
    intro t _
    convert ((hεd (κ s + t * v s)).hasDerivAt.comp t
      (((hasDerivAt_id t).mul_const (v s)).const_add (κ s))).mul_const (w s) using 1
    simp
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : t₀ - 1 < t₀) (by linarith : t₀ < t₀ + 1))
    (Filter.Eventually.of_forall hmeas) hint hmeas' hbound
    (integrable_const C) hdiff
  simpa only [intervalIntegral.integral_of_le hℓ] using h.2

/-- The first derivative of the actual energy at every variation parameter. -/
theorem hasDerivAt_energy_variation_at {ε θ η : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 1 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η) (t : ℝ) :
    HasDerivAt (fun u => energy ε (angleVariation θ η u) ℓ)
      (∫ s in 0..ℓ, deriv ε (deriv θ s + t * deriv η s) * deriv η s) t := by
  have h := hasDerivAt_weighted_integral_variation (w := fun _ => 1) hℓ hε
    hθ.continuous_deriv_one hη.continuous_deriv_one continuous_const t
  simpa only [mul_one, energy,
    deriv_angleVariation (hθ.differentiable one_ne_zero) (hη.differentiable one_ne_zero)] using h

/-- Differentiate the already identified first derivative of the actual energy.
Its second variation is the curvature-density second derivative times `(η')²`. -/
theorem hasDerivAt_deriv_energy_variation {ε θ η : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 2 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η) :
    HasDerivAt (deriv (fun t => energy ε (angleVariation θ η t) ℓ))
      (∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η s) ^ 2) 0 := by
  have hd : deriv (fun t => energy ε (angleVariation θ η t) ℓ) =
      fun t => ∫ s in 0..ℓ, deriv ε (deriv θ s + t * deriv η s) * deriv η s := by
    funext t
    exact (hasDerivAt_energy_variation_at hℓ (hε.of_le (by norm_num)) hθ hη t).deriv
  rw [hd]
  have h := hasDerivAt_weighted_integral_variation (ε := deriv ε)
    (κ := deriv θ) (v := deriv η) (w := deriv η) hℓ hε.deriv'
    hθ.continuous_deriv_one hη.continuous_deriv_one hη.continuous_deriv_one 0
  simpa only [zero_mul, add_zero, mul_assoc, ← pow_two] using h

/-- The actual second derivative, rather than a separately defined quadratic form. -/
theorem secondVariation_energy {ε θ η : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 2 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η) :
    deriv (deriv (fun t => energy ε (angleVariation θ η t) ℓ)) 0 =
      ∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * (deriv η s) ^ 2 :=
  (hasDerivAt_deriv_energy_variation hℓ hε hθ hη).deriv

/-- The actual mixed derivative for the two angle directions `η` and `ξ`. -/
theorem mixedVariation_energy {ε θ η ξ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 2 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η) (hξ : ContDiff ℝ 1 ξ) :
    deriv (fun t => deriv
      (fun u => energy ε (angleVariation (angleVariation θ η t) ξ u) ℓ) 0) 0 =
      ∫ s in 0..ℓ, deriv (deriv ε) (deriv θ s) * deriv η s * deriv ξ s := by
  have hd (t : ℝ) :
      deriv (fun u => energy ε (angleVariation (angleVariation θ η t) ξ u) ℓ) 0 =
        ∫ s in 0..ℓ, deriv ε (deriv θ s + t * deriv η s) * deriv ξ s := by
    have ht : ContDiff ℝ 1 (angleVariation θ η t) :=
      hθ.add (contDiff_const.mul hη)
    simpa only [deriv_angleVariation (hθ.differentiable one_ne_zero)
      (hη.differentiable one_ne_zero)] using
      (hasDerivAt_energy_variation hℓ (hε.of_le (by norm_num)) ht hξ).deriv
  simp_rw [hd]
  have h := hasDerivAt_weighted_integral_variation (ε := deriv ε)
    (κ := deriv θ) (v := deriv η) (w := deriv ξ) hℓ hε.deriv'
    hθ.continuous_deriv_one hη.continuous_deriv_one hξ.continuous_deriv_one 0
  simpa only [zero_mul, add_zero] using h.deriv

/-- Interchanging the two angle-variation directions preserves the mixed derivative. -/
theorem mixedVariation_energy_symmetric {ε θ η ξ : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 2 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η) (hξ : ContDiff ℝ 1 ξ) :
    deriv (fun t => deriv
      (fun u => energy ε (angleVariation (angleVariation θ η t) ξ u) ℓ) 0) 0 =
    deriv (fun u => deriv
      (fun t => energy ε (angleVariation (angleVariation θ ξ u) η t) ℓ) 0) 0 := by
  rw [mixedVariation_energy hℓ hε hθ hη hξ, mixedVariation_energy hℓ hε hθ hξ hη]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp
  ring

end Elastica
