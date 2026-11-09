import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Exact Kerr constitutive algebra and the scalar characteristic calculation.
The PDE-to-characteristic identities are explicit hypotheses; this module
does not assert local existence or continuation of the Kerr PDE.
-/

namespace KerrKoopman.Riccati

noncomputable section

def constitutive (e : ℝ) : ℝ := e + e ^ 3 / 3

theorem constitutive_shift (e : ℝ) :
    constitutive (1 + e) - 4 / 3 = 2 * e + e ^ 2 + e ^ 3 / 3 := by
  unfold constitutive
  ring

/-- The cancellation uses q = sqrt(c), hence c = q^2. -/
theorem mixed_gradient_cancellation (q dc r s : ℝ) (hq : q ≠ 0) :
    q * (-(dc / (2 * q ^ 2)) * (r - s) * r) +
        (-(dc * s) / (2 * q)) * r =
      (-(dc) / (2 * q ^ 3)) * (q * r) ^ 2 := by
  field_simp
  ring

/-- Conditional chain rule along either characteristic family. -/
theorem scaled_gradient_hasDerivAt (q r : ℝ → ℝ) (dc s t : ℝ)
    (hq : q t ≠ 0)
    (hq' : HasDerivAt q (-(dc * s) / (2 * q t)) t)
    (hr' : HasDerivAt r (-(dc / (2 * (q t) ^ 2)) * (r t - s) * r t) t) :
    HasDerivAt (fun z => q z * r z)
      (-(dc) / (2 * (q t) ^ 3) * (q t * r t) ^ 2) t := by
  convert hq'.mul hr' using 1
  simpa only [add_comm] using (mixed_gradient_cancellation (q t) dc (r t) s hq).symm

theorem reciprocal_riccati_derivative (y a : ℝ → ℝ) (t : ℝ)
    (hy : HasDerivAt y (a t * y t ^ 2) t) (hne : y t ≠ 0) :
    HasDerivAt (fun z => (y z)⁻¹) (-a t) t := by
  convert hy.inv hne using 1
  field_simp

def scalarSolution (A y₀ t : ℝ) : ℝ := y₀ / (1 - A * y₀ * t)

theorem scalarSolution_initial (A y₀ : ℝ) : scalarSolution A y₀ 0 = y₀ := by
  simp [scalarSolution]

/-- This is an actual derivative theorem, not only a polynomial identity. -/
theorem scalarSolution_hasDerivAt (A y₀ t : ℝ)
    (hden : 1 - A * y₀ * t ≠ 0) :
    HasDerivAt (scalarSolution A y₀)
      (A * (scalarSolution A y₀ t) ^ 2) t := by
  have hd : HasDerivAt (fun z : ℝ => 1 - A * y₀ * z) (-(A * y₀)) t := by
    simpa using (hasDerivAt_const t (1 : ℝ)).sub
      ((hasDerivAt_id t).const_mul (A * y₀))
  unfold scalarSolution
  convert (hasDerivAt_const t y₀).div hd hden using 1
  field_simp
  ring

/-- A positive Riccati solution with a positive coefficient lower bound
cannot remain positive and differentiable through its reciprocal deadline.
The hypotheses are scalar ODE hypotheses, not a PDE existence theorem. -/
theorem positive_riccati_lifetime_bound
    (y a : ℝ → ℝ) (a₀ T : ℝ) (hT : 0 ≤ T) (ha₀ : 0 < a₀)
    (hypos : ∀ t ∈ Set.Icc 0 T, 0 < y t)
    (ha : ∀ t ∈ Set.Icc 0 T, a₀ ≤ a t)
    (hderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (a t * y t ^ 2) t) :
    T < 1 / (a₀ * y 0) := by
  let v : ℝ → ℝ := fun t => (y t)⁻¹ + a₀ * t
  have hv : ∀ t ∈ Set.Icc 0 T, HasDerivAt v (-a t + a₀) t := by
    intro t ht
    simpa [v] using (reciprocal_riccati_derivative y a t (hderiv t ht)
      (ne_of_gt (hypos t ht))).add ((hasDerivAt_id t).const_mul a₀)
  have hvcont : ContinuousOn v (Set.Icc 0 T) := by
    intro t ht
    exact (hv t ht).continuousAt.continuousWithinAt
  have hmono : AntitoneOn v (Set.Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hvcont
    · intro t ht
      exact (hv t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      linarith [ha t (interior_subset ht)]
  have hb := hmono (show 0 ∈ Set.Icc 0 T from ⟨le_rfl, hT⟩)
    (show T ∈ Set.Icc 0 T from ⟨hT, le_rfl⟩) hT
  have hy0 := hypos 0 ⟨le_rfl, hT⟩
  have hyT := hypos T ⟨hT, le_rfl⟩
  have hiT : 0 < (y T)⁻¹ := inv_pos.mpr hyT
  have hi0 : (y 0)⁻¹ = 1 / y 0 := by rw [one_div]
  change (y T)⁻¹ + a₀ * T ≤ (y 0)⁻¹ + a₀ * 0 at hb
  have hb' : a₀ * T < 1 / y 0 := by linarith
  apply (lt_div_iff₀ (mul_pos ha₀ hy0)).mpr
  have := (lt_div_iff₀ hy0).mp hb'
  nlinarith

theorem small_profile_deadlines :
    (4 : ℝ) / (4 / 100 + 3 / 100) = 400 / 7 ∧
    (10 : ℝ) / (3 / 100) = 1000 / 3 := by
  norm_num

end

end KerrKoopman.Riccati
