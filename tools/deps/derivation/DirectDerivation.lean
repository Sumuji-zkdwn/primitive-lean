import InitialLayer

/-!
Direct derivations of two main theorems whose existing proofs detour through
objects defined outside the initial layer (`LinearInputVariablePairs.energy`,
`gradXu`, `gradient`). Only the initial layer and Mathlib are imported here.
-/
noncomputable section
open Real
namespace DirectDerivation

theorem original_potential_formula (k x u : ℝ) :
    LinearInputDesign.E 0 (k - 2) (-u) x 0 =
      k * x ^ 2 / 2 + u * x := by
  unfold LinearInputDesign.E LinearInputDesign.f
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [h]

theorem original_gradient_formula (k : ℝ) (z : ℝ × ℝ) :
    (deriv (fun t : ℝ => LinearInputDesign.E 0 (k - 2) (-z.2) t 0) z.1,
     deriv (fun t : ℝ => LinearInputDesign.E 0 (k - 2) (-t) z.1 0) z.2) =
      (k * z.1 + z.2, z.1) := by
  have hx : (fun t : ℝ => LinearInputDesign.E 0 (k - 2) (-z.2) t 0) =
      fun t => k / 2 * t ^ 2 + z.2 * t := by
    funext t
    rw [original_potential_formula]
    ring
  have hy : (fun t : ℝ => LinearInputDesign.E 0 (k - 2) (-t) z.1 0) =
      fun t => z.1 * t + k / 2 * z.1 ^ 2 := by
    funext t
    rw [original_potential_formula]
    ring
  rw [hx, hy]
  have d1 : HasDerivAt (fun t : ℝ => k / 2 * t ^ 2 + z.2 * t) (k * z.1 + z.2) z.1 := by
    have := ((hasDerivAt_pow 2 z.1).const_mul (k / 2)).add ((hasDerivAt_id z.1).const_mul z.2)
    convert this using 1
    · ring
  have d2 : HasDerivAt (fun t : ℝ => z.1 * t + k / 2 * z.1 ^ 2) z.1 z.2 := by
    have := ((hasDerivAt_id z.2).const_mul z.1).add_const (k / 2 * z.1 ^ 2)
    convert this using 1
    · ring
  rw [d1.deriv, d2.deriv]

end DirectDerivation
