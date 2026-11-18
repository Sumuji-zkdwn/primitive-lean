import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
Actual derivatives and necessary conditions for the quartic with a linear input.
The derivative is proved from the definition, not postulated.
-/
noncomputable section
namespace LinearInputCalculus

def potential (lam r u x : ℝ) : ℝ :=
  lam * x ^ 4 / 4 + r * x ^ 2 / 2 - u * x

theorem hasDerivAt_potential (lam r u x : ℝ) :
    HasDerivAt (potential lam r u) (lam * x ^ 3 + r * x - u) x := by
  convert ((((hasDerivAt_id x).pow 4).const_mul lam).div_const 4).add
    ((((hasDerivAt_id x).pow 2).const_mul r).div_const 2) |>.sub
    ((hasDerivAt_id x).const_mul u) using 1
  · rfl
  · simp only [id_eq]
    ring

theorem deriv_potential (lam r u x : ℝ) :
    deriv (potential lam r u) x = lam * x ^ 3 + r * x - u :=
  (hasDerivAt_potential lam r u x).deriv

theorem stationary_iff_input (lam r u x : ℝ) :
    deriv (potential lam r u) x = 0 ↔ u = lam * x ^ 3 + r * x := by
  rw [deriv_potential]
  constructor <;> intro h <;> linarith

theorem global_minimum_forces_input {lam r u a : ℝ}
    (hmin : ∀ t : ℝ, potential lam r u a ≤ potential lam r u t) :
    u = lam * a ^ 3 + r * a := by
  have hm : IsMinOn (potential lam r u) Set.univ a := fun t _ => hmin t
  have hz := (hm.isLocalMin Filter.univ_mem).hasDerivAt_eq_zero
    (hasDerivAt_potential lam r u a)
  linarith

theorem critical_value {lam r u x : ℝ} (hu : u = lam * x ^ 3 + r * x) :
    potential lam r u x = -3 * lam * x ^ 4 / 4 - r * x ^ 2 / 2 := by
  rw [hu]
  unfold potential
  ring

theorem critical_value_le {lam r u x : ℝ} (hlam : 0 < lam)
    (hu : u = lam * x ^ 3 + r * x) :
    potential lam r u x ≤ (max (-r) 0) ^ 2 / (12 * lam) := by
  rw [critical_value hu]
  by_cases hr : 0 ≤ r
  · rw [max_eq_right (by linarith : -r ≤ 0)]
    have h4 : 0 ≤ lam * x ^ 4 := by positivity
    have h2 : 0 ≤ r * x ^ 2 := mul_nonneg hr (sq_nonneg x)
    norm_num
    nlinarith
  · rw [max_eq_left (by linarith : 0 ≤ -r)]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 12 * lam)).2
    nlinarith [sq_nonneg (3 * lam * x ^ 2 + r)]

theorem critical_value_below_target {lam r u x target : ℝ} (hlam : 0 < lam)
    (hu : u = lam * x ^ 3 + r * x)
    (ht : (max (-r) 0) ^ 2 / (12 * lam) < target) :
    potential lam r u x < target :=
  lt_of_le_of_lt (critical_value_le hlam hu) ht

theorem positive_target_counterexample :
    deriv (potential 1 (-1) (10 / 27)) (-2 / 3) = 0 ∧
    potential 1 (-1) (10 / 27) (-2 / 3) = 2 / 27 ∧
    (0 : ℝ) < 1 / 27 ∧ (1 / 27 : ℝ) < 2 / 27 := by
  rw [deriv_potential]
  norm_num [potential]

end LinearInputCalculus
