import OrbitTraceFiltration

/-!
# Sharp recurrence-step nilpotence bound for the actual transfer

A transfer deviation loses p+1 degrees at every nonzero step, hence a
polynomial of degree at most d is annihilated after the bounded recursive
number of steps below. This is an actual statement about the polynomial
linear operator, not an independent Jordan block.

The explicit equality with floor(d/(p+1))+1 is algebraic and can be
proved separately; this file verifies the terminating recurrence bound.
-/

namespace OrbitTrace

open Polynomial

def fastSteps (p : ℕ) (d : ℕ) : ℕ :=
  if h : d ≤ p then 1 else fastSteps p (d - (p + 1)) + 1
termination_by d
decreasing_by all_goals omega

theorem canonicalDelta_fast_nilpotent (p : ℕ) (a : ℚ) :
    ∀ d : ℕ, ∀ P : Polynomial ℚ, P.natDegree ≤ d →
      iterDrop (fun Q : Polynomial ℚ => canonicalDelta p a Q)
        (fastSteps p d) P = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro P hdegree
      by_cases hsmall : d ≤ p
      · have hzero : canonicalDelta p a P = 0 :=
          canonicalDelta_zero_of_low_degree p a P
            (hdegree.trans hsmall)
        have hsteps : fastSteps p d = 1 := by
          rw [fastSteps, dif_pos hsmall]
        rw [hsteps]
        change canonicalDelta p a P = 0
        exact hzero
      · have hq : p + 1 ≤ d := by omega
        have hnext : d - (p + 1) < d := by omega
        have hdegree' :
            (canonicalDelta p a P).natDegree ≤ d - (p + 1) :=
          (natDegree_le_iff_degree_le).2
            (canonicalDelta_degree_bound p a d P hdegree)
        have hstep : fastSteps p d =
            fastSteps p (d - (p + 1)) + 1 := by
          rw [fastSteps, dif_neg hsmall]
        rw [hstep]
        change iterDrop (fun Q : Polynomial ℚ => canonicalDelta p a Q)
          (fastSteps p (d - (p + 1)))
          (canonicalDelta p a P) = 0
        exact ih (d - (p + 1)) hnext
          (canonicalDelta p a P) hdegree'

#print axioms OrbitTrace.canonicalDelta_fast_nilpotent

end OrbitTrace
