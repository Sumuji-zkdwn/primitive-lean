import KerrKoopman.PrimitiveConstitutive
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Explicit Kerr material inversion

The unique material inverse derived from primitive-lean now has a one-line
closed formula. This removes an implicit scalar solve at every material
evaluation. It does not solve the coupled spatial or physical-time equations.
-/

namespace KerrKoopman.ExplicitMaterial

noncomputable section

open Riccati PrimitiveConstitutive

/-- The real cubic Kerr law has this globally single-valued explicit inverse. -/
def electricOfDisplacement (d : ℝ) : ℝ :=
  2 * Real.sinh (Real.arsinh (3 * d / 2) / 3)

/-- Triple-angle hyperbolic sine directly verifies the actual constitutive law. -/
theorem constitutive_electricOfDisplacement (d : ℝ) :
    constitutive (electricOfDisplacement d) = d := by
  have h := Real.sinh_three_mul (Real.arsinh (3 * d / 2) / 3)
  have harg : 3 * (Real.arsinh (3 * d / 2) / 3) = Real.arsinh (3 * d / 2) := by ring
  rw [harg, Real.sinh_arsinh] at h
  dsimp [constitutive, electricOfDisplacement]
  nlinarith

/-- The explicit formula is the same inverse previously obtained from unique
global minimization, rather than a different choice of branch. -/
theorem electricOfDisplacement_eq_materialInverse (d : ℝ) :
    electricOfDisplacement d = materialInverse d := by
  apply constitutive_injective
  rw [constitutive_electricOfDisplacement, constitutive_materialInverse]

theorem electricOfDisplacement_constitutive (e : ℝ) :
    electricOfDisplacement (constitutive e) = e := by
  rw [electricOfDisplacement_eq_materialInverse, materialInverse_constitutive]

/-- Every order of real smoothness is available without choosing a branch. -/
theorem contDiff_electricOfDisplacement {n : WithTop ℕ∞} :
    ContDiff ℝ n electricOfDisplacement := by
  unfold electricOfDisplacement
  fun_prop

/-- The derivative is obtained from differentiating the actual inverse
identity; no reciprocal-derivative formula is postulated. -/
theorem hasDerivAt_electricOfDisplacement (d : ℝ) :
    HasDerivAt electricOfDisplacement
      (1 / (1 + electricOfDisplacement d ^ 2)) d := by
  have hd : DifferentiableAt ℝ electricOfDisplacement d := by
    unfold electricOfDisplacement
    fun_prop
  have hc := FiniteEnergy.constitutive_hasDerivAt electricOfDisplacement
    (deriv electricOfDisplacement d) d hd.hasDerivAt
  have hf : (fun z : ℝ => electricOfDisplacement z +
      electricOfDisplacement z ^ 3 / 3) = id := by
    funext z
    exact constitutive_electricOfDisplacement z
  rw [hf] at hc
  have heq := hc.unique (hasDerivAt_id d)
  have hn : 1 + electricOfDisplacement d ^ 2 ≠ 0 :=
    ne_of_gt (FiniteEnergy.constitutive_denominator_pos _)
  convert hd.hasDerivAt using 1
  symm
  apply (eq_div_iff hn).2
  simpa only [mul_comm] using heq

theorem hasDerivAt_materialInverse (d : ℝ) :
    HasDerivAt materialInverse (1 / (1 + materialInverse d ^ 2)) d := by
  have hf : electricOfDisplacement = materialInverse :=
    funext electricOfDisplacement_eq_materialInverse
  simpa only [hf] using hasDerivAt_electricOfDisplacement d

/-- The explicit expression retains the previously proved global error bound. -/
theorem electricOfDisplacement_lipschitz : LipschitzWith 1 electricOfDisplacement := by
  have hf : electricOfDisplacement = materialInverse :=
    funext electricOfDisplacement_eq_materialInverse
  simpa only [hf] using materialInverse_lipschitz

theorem electricOfDisplacement_zero : electricOfDisplacement 0 = 0 := by
  simp [electricOfDisplacement]

theorem electricOfDisplacement_neg (d : ℝ) :
    electricOfDisplacement (-d) = -electricOfDisplacement d := by
  unfold electricOfDisplacement
  rw [show 3 * (-d) / 2 = -(3 * d / 2) by ring,
    Real.arsinh_neg, neg_div, Real.sinh_neg, mul_neg]

end

end KerrKoopman.ExplicitMaterial
