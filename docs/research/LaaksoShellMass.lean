import Mathlib.Tactic

/-!
# Exact rational shell budgets for the A-track counterexample

The density consists of a constant baseline and a triangular bump on the
shell [6^(-n-1), 6^(-n)]. The average of the triangular bump is half its peak.
This module certifies the resulting algebraic shell mass and the consistency
recurrence. Identifying this number with a Lebesgue integral, or proving
all-scale doubling / PI-failure, remains outside this module.
-/

namespace LaaksoShellMass

/-- The rational mass allocated to shell n, where n=0 is allowed
algebraically. Original geometric shells begin at n=1. -/
def shellMass (n : ℕ) : ℚ :=
  ((1 / 6 : ℚ) ^ n - (1 / 6 : ℚ) ^ (n + 1)) *
    ((4 / 5 : ℚ) + ((8 / 5 : ℚ) * ((2 : ℚ) ^ n - 1)) / 2)

/-- Integration of the stipulated affine tent gives exactly 2/3 of the
n-th ternary mass unit. All quantities are exact rationals. -/
theorem shellMass_eq (n : ℕ) :
    shellMass n = (2 / 3 : ℚ) * (1 / 3 : ℚ) ^ n := by
  have hpow : (2 : ℚ) ^ n * (1 / 6 : ℚ) ^ n = (1 / 3 : ℚ) ^ n := by
    rw [← mul_pow]
    norm_num
  unfold shellMass
  rw [pow_succ]
  calc
    ((1 / 6 : ℚ) ^ n - (1 / 6 : ℚ) ^ n * (1 / 6 : ℚ)) *
        ((4 / 5 : ℚ) + ((8 / 5 : ℚ) * ((2 : ℚ) ^ n - 1)) / 2)
        = (2 / 3 : ℚ) * ((2 : ℚ) ^ n * (1 / 6 : ℚ) ^ n) := by ring
    _ = (2 / 3 : ℚ) * (1 / 3 : ℚ) ^ n := by rw [hpow]

/-- The shell mass plus the next gate's cumulative tail is exactly the
current ternary gate's mass. This is the algebraic counterpart of
F(6^-n)=3^-n, not a proof of the analytic integral identity. -/
theorem shellMass_plus_tail (n : ℕ) :
    shellMass n + (1 / 3 : ℚ) ^ (n + 1) = (1 / 3 : ℚ) ^ n := by
  rw [shellMass_eq, pow_succ]
  ring

#print axioms shellMass_eq
#print axioms shellMass_plus_tail

end LaaksoShellMass
