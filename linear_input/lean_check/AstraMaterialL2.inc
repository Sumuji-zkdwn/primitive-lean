
/-!
# The actual real Kerr material map on normalized-circle L2

This is pointwise composition with the explicit inverse constitutive law,
well-defined on almost-everywhere equivalence classes. Global 1-Lipschitz
continuity is proved. No Frechet differentiability on infinite-dimensional
L2 and no complex-valued extension of the real material law is asserted.
-/

noncomputable section

open MeasureTheory
open KerrKoopman.FourierProjection KerrKoopman.ExplicitMaterial

namespace KerrKoopman.MaterialL2

abbrev RealCircleL2 := Lp ℝ 2
  (@AddCircle.haarAddCircle (2 * Real.pi) FourierProjection.positiveTwoPi)

/-- Pointwise explicit constitutive inversion as an actual map of real L2 classes. -/
def material : RealCircleL2 → RealCircleL2 :=
  electricOfDisplacement_lipschitz.compLp electricOfDisplacement_zero

theorem material_ae (f : RealCircleL2) :
    material f =ᵐ[AddCircle.haarAddCircle] electricOfDisplacement ∘ f :=
  electricOfDisplacement_lipschitz.coeFn_compLp electricOfDisplacement_zero f

theorem material_constitutive_ae (f : RealCircleL2) :
    ∀ᵐ x ∂AddCircle.haarAddCircle,
      (material f) x + (material f) x ^ 3 / 3 = f x := by
  filter_upwards [material_ae f] with x hx
  rw [hx]
  exact constitutive_electricOfDisplacement (f x)

theorem material_lipschitz : LipschitzWith 1 material :=
  electricOfDisplacement_lipschitz.lipschitzWith_compLp electricOfDisplacement_zero

theorem material_zero : material 0 = 0 := by
  exact electricOfDisplacement_lipschitz.compLp_zero electricOfDisplacement_zero

theorem material_norm_sub_le (f g : RealCircleL2) :
    ‖material f - material g‖ ≤ ‖f - g‖ := by
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using material_lipschitz.dist_le_mul f g

theorem material_norm_le (f : RealCircleL2) : ‖material f‖ ≤ ‖f‖ := by
  simpa only [material_zero, sub_zero] using material_norm_sub_le f 0

theorem material_continuous : Continuous material := material_lipschitz.continuous

end KerrKoopman.MaterialL2
