import Mathlib

/-! Small, isolated decision-app obligations. This is not a JS refinement proof. -/
namespace DecisionApp

variable {α : Type*}

/-- The finite list prefix is an abstract representation of contextKey.
    In the app, the delimiter and end marker encode the length as well. -/
def prefix : Nat → List α → List α
  | 0, _ => []
  | _ + 1, [] => []
  | d + 1, a :: xs => a :: prefix d xs

theorem prefix_nested (xs : List α) (d e : Nat) (h : d ≤ e) :
    prefix d (prefix e xs) = prefix d xs := by
  induction d generalizing e xs with
  | zero => rfl
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e =>
      cases xs with
      | nil => rfl
      | cons a xs =>
        change a :: prefix d (prefix e xs) = a :: prefix d xs
        exact congrArg (List.cons a) (by
          apply ih
          omega)

theorem prefix_refinement (xs ys : List α) (d e : Nat) (h : d ≤ e)
    (he : prefix e xs = prefix e ys) : prefix d xs = prefix d ys := by
  have hh := congrArg (prefix d) he
  simpa only [prefix_nested xs d e h, prefix_nested ys d e h] using hh

/-- 0.8 prayer + 0.1 doubt + 0.1 uniform on two actions. -/
def actionProbability (r d : ℝ) : ℝ :=
  (8 / 10 : ℝ) * r + (1 / 10 : ℝ) * d + (1 / 20 : ℝ)

theorem action_floor (r d : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1) :
    (1 / 20 : ℝ) ≤ actionProbability r d ∧ actionProbability r d ≤ 19 / 20 := by
  unfold actionProbability
  constructor <;> linarith [hr.1, hr.2, hd.1, hd.2]

theorem action_normalization (r d : ℝ) :
    actionProbability r d + actionProbability (1-r) (1-d) = 1 := by
  unfold actionProbability
  ring

/-- One-step conditional expectation algebra for a fixed finite predictive
    likelihood ratio. Not a proof of Ville's inequality or empirical calibration. -/
theorem evidence_step_mass {Y : Type*} [Fintype Y] (A B : Y → ℝ) (e : ℝ)
    (hA : ∀ y, 0 < A y) (hB : ∑ y, B y = 1) :
    (∑ y, A y * (e * (B y / A y))) = e := by
  classical
  calc
    (∑ y, A y * (e * (B y / A y))) = ∑ y, e * B y := by
      apply Finset.sum_congr rfl
      intro y _
      field_simp [(hA y).ne'] <;> ring
    _ = e := by rw [← Finset.mul_sum, hB, mul_one]

end DecisionApp

#print axioms DecisionApp.prefix_nested
#print axioms DecisionApp.prefix_refinement
#print axioms DecisionApp.action_floor
#print axioms DecisionApp.action_normalization
#print axioms DecisionApp.evidence_step_mass
