import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

/-!
# First variation of the actual curvature integral

The derivative under the integral is proved using a compact, uniform derivative
bound and mathlib's dominated differentiation theorem. No first-variation formula
is postulated. Functions on a compact interval are represented by smooth functions
on the real line; only their values on the interval enter the integrals.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Elastica

/-- Curvature energy in the tangent-angle representation. -/
def energy (ε θ : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  ∫ s in 0..ℓ, ε (deriv θ s)

/-- The usual additive tangent-angle variation. -/
def angleVariation (θ η : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  fun s => θ s + t * η s

/-- Its curvature is the sum of the original curvature and the varied derivative. -/
theorem deriv_angleVariation {θ η : ℝ → ℝ} (hθ : Differentiable ℝ θ)
    (hη : Differentiable ℝ η) (t s : ℝ) :
    deriv (angleVariation θ η t) s = deriv θ s + t * deriv η s := by
  exact ((hθ s).hasDerivAt.add ((hη s).hasDerivAt.const_mul t)).deriv

/-- Differentiating a general density under a finite curvature integral.

The compact rectangle supplies the bound; boundedness of the density derivative
on all of ℝ is not assumed. -/
theorem hasDerivAt_integral_variation {ε κ v : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 1 ε) (hκ : Continuous κ) (hv : Continuous v) :
    HasDerivAt (fun t : ℝ => ∫ s in 0..ℓ, ε (κ s + t * v s))
      (∫ s in 0..ℓ, deriv ε (κ s) * v s) 0 := by
  have hεd : Differentiable ℝ ε := hε.differentiable (by norm_num)
  have hε' : Continuous (deriv ε) := hε.continuous_deriv (by norm_num)
  have hc : Continuous (fun p : ℝ × ℝ => deriv ε (κ p.2 + p.1 * v p.2) * v p.2) :=
    (hε'.comp ((hκ.comp continuous_snd).add
      (continuous_fst.mul (hv.comp continuous_snd)))).mul (hv.comp continuous_snd)
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).prod
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) ℓ))).exists_bound_of_continuousOn hc.continuousOn
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun s => ε (κ s + t * v s)) (volume.restrict (Ioc 0 ℓ)) :=
    (hε.continuous.comp (hκ.add (continuous_const.mul hv))).aestronglyMeasurable
  have hint : Integrable (fun s => ε (κ s + (0 : ℝ) * v s))
      (volume.restrict (Ioc 0 ℓ)) := by
    exact ((hε.continuous.comp (hκ.add (continuous_const.mul hv))).intervalIntegrable 0 ℓ).1
  have hmeas' : AEStronglyMeasurable
      (fun s => deriv ε (κ s + (0 : ℝ) * v s) * v s)
      (volume.restrict (Ioc 0 ℓ)) :=
    ((hε'.comp (hκ.add (continuous_const.mul hv))).mul hv).aestronglyMeasurable
  have hbound : ∀ᵐ s ∂volume.restrict (Ioc 0 ℓ),
      ∀ t ∈ Ioo (-1 : ℝ) 1, ‖deriv ε (κ s + t * v s) * v s‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    intro t ht
    exact hC (t, s) ⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, ⟨le_of_lt hs.1, hs.2⟩⟩
  have hdiff : ∀ᵐ s ∂volume.restrict (Ioc 0 ℓ), ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun t => ε (κ s + t * v s))
        (deriv ε (κ s + t * v s) * v s) t := by
    filter_upwards [] with s
    intro t _
    convert (hεd (κ s + t * v s)).hasDerivAt.comp t
      (((hasDerivAt_id t).mul_const (v s)).const_add (κ s)) using 1
    all_goals first | (funext x; rfl) | ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall hmeas) hint hmeas' hbound
    (integrable_const C) hdiff
  simpa only [intervalIntegral.integral_of_le hℓ, zero_mul, add_zero] using h.2

/-- First variation of the energy evaluated at the genuinely varied angle. -/
theorem hasDerivAt_energy_variation {ε θ η : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hε : ContDiff ℝ 1 ε)
    (hθ : ContDiff ℝ 1 θ) (hη : ContDiff ℝ 1 η) :
    HasDerivAt (fun t => energy ε (angleVariation θ η t) ℓ)
      (∫ s in 0..ℓ, deriv ε (deriv θ s) * deriv η s) 0 := by
  have h := hasDerivAt_integral_variation hℓ hε
    (hθ.continuous_deriv (by norm_num)) (hη.continuous_deriv (by norm_num))
  simpa only [energy, deriv_angleVariation
    (hθ.differentiable (by norm_num)) (hη.differentiable (by norm_num))] using h

/-- First variation of the horizontal displacement. -/
theorem hasDerivAt_horizontal_variation {θ η : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hθ : Continuous θ) (hη : Continuous η) :
    HasDerivAt (fun t => ∫ s in 0..ℓ, Real.cos (θ s + t * η s))
      (∫ s in 0..ℓ, -Real.sin (θ s) * η s) 0 := by
  simpa only [Real.deriv_cos] using
    (hasDerivAt_integral_variation hℓ Real.contDiff_cos hθ hη)

/-- First variation of the vertical displacement. -/
theorem hasDerivAt_vertical_variation {θ η : ℝ → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hθ : Continuous θ) (hη : Continuous η) :
    HasDerivAt (fun t => ∫ s in 0..ℓ, Real.sin (θ s + t * η s))
      (∫ s in 0..ℓ, Real.cos (θ s) * η s) 0 := by
  simpa only [Real.deriv_sin] using
    (hasDerivAt_integral_variation hℓ Real.contDiff_sin hθ hη)

end Elastica
