import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# A scalar stability-and-defect recurrence

These are exact conditional inequalities for an arbitrary real sequence.
No PDE flow, local splitting defect, or uniform spatial estimate is assumed
to have been constructed: an application must supply the displayed recurrence.
-/

namespace KerrKoopman.IterationBound

/-- A geometric defect at each step telescopes without division by a-1.
The proof even allows b of either sign; only multiplication by a needs a>=0. -/
theorem weighted_recurrence_bound (a b : ℝ) (ha : 0 ≤ a)
    (err : ℕ → ℝ) (hzero : err 0 = 0)
    (hstep : ∀ k, err (k + 1) ≤ a * err k + b * a ^ (k + 1)) (n : ℕ) :
    err n ≤ (n : ℝ) * b * a ^ n := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    calc
      err (n + 1) ≤ a * err n + b * a ^ (n + 1) := hstep n
      _ ≤ a * ((n : ℝ) * b * a ^ n) + b * a ^ (n + 1) := by
        linarith [mul_le_mul_of_nonneg_left ih ha]
      _ = ((n + 1 : ℕ) : ℝ) * b * a ^ (n + 1) := by
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        ring

/-- Physical-time exponential growth can be retained exactly in this recurrence. -/
theorem exponential_recurrence_bound (K h b : ℝ)
    (err : ℕ → ℝ) (hzero : err 0 = 0)
    (hstep : ∀ k, err (k + 1) ≤ Real.exp (K * h) * err k +
      b * Real.exp (((k + 1 : ℕ) : ℝ) * K * h)) (n : ℕ) :
    err n ≤ (n : ℝ) * b * Real.exp ((n : ℝ) * K * h) := by
  have hpow : ∀ k : ℕ, Real.exp (K * h) ^ k =
      Real.exp ((k : ℝ) * K * h) := by
    intro k
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have bound := weighted_recurrence_bound (Real.exp (K * h)) b
    (Real.exp_nonneg _) err hzero (by
      intro k
      simpa only [hpow] using hstep k) n
  simpa only [hpow] using bound

/-- If stability and local defects give this displayed recurrence at h=T/n,
then the global error has the explicit O(1/n) bound. This theorem does not
prove that any particular finite or continuous field model has the recurrence. -/
theorem finite_time_error_bound (K T r₀ : ℝ) (n : ℕ) (hn : 0 < n)
    (err : ℕ → ℝ) (hzero : err 0 = 0)
    (hstep : ∀ k, err (k + 1) ≤ Real.exp (K * (T / n)) * err k +
      ((3 / 2 : ℝ) * K ^ 2 * (T / n) ^ 2 * r₀) *
        Real.exp (((k + 1 : ℕ) : ℝ) * K * (T / n))) :
    err n ≤ ((3 / 2 : ℝ) * K ^ 2 * T ^ 2 * r₀ / n) * Real.exp (K * T) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hexp : (n : ℝ) * K * (T / n) = K * T := by
    field_simp
  have bound := exponential_recurrence_bound K (T / n)
    ((3 / 2 : ℝ) * K ^ 2 * (T / n) ^ 2 * r₀) err hzero hstep n
  rw [hexp] at bound
  convert bound using 1
  field_simp

end KerrKoopman.IterationBound
