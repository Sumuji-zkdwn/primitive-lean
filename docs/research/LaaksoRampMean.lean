import Mathlib.Tactic

/-!
# Exact rational symmetric-ramp mean for the A-track density

The two affine tent sides integrate to the *algebraic* expression below
when the ramp width is δ_n=6^-n 4^-n. The source paper and Python Fraction
checker verify the integral-to-expression identification. This Lean module
checks the universal rational upper bound, not an integral over a Laakso
quotient or the final PI nonexistence theorem.
-/

namespace LaaksoRampMean

def exactRampMean (n : ℕ) : ℚ :=
  (4 / 5 : ℚ) +
    ((26 : ℚ) * (2 : ℚ) ^ n - 28) / (25 * (4 : ℚ) ^ n)

private theorem two_pow_ge_four (n : ℕ) (hn : 2 ≤ n) :
    (4 : ℚ) ≤ (2 : ℚ) ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : n = 1
      · subst n
        norm_num
      · have hn2 : 2 ≤ n := by omega
        have hprev := ih hn2
        rw [pow_succ]
        nlinarith

/-- The exact bump contribution cannot exceed 6/25 for any n≥1.
The maximum 26/25 is realized at the first gate n=1. -/
theorem exactRampMean_le (n : ℕ) (hn : 1 ≤ n) :
    exactRampMean n ≤ (26 / 25 : ℚ) := by
  by_cases h1 : n = 1
  · subst n
    norm_num [exactRampMean]
  · have hn2 : 2 ≤ n := by omega
    have ht : (4 : ℚ) ≤ (2 : ℚ) ^ n := two_pow_ge_four n hn2
    have hpow : (4 : ℚ) ^ n = ((2 : ℚ) ^ n) ^ 2 := by
      rw [show (4 : ℚ) = 2 * 2 by norm_num, mul_pow]
      ring
    have ha : 0 ≤ 3 * (2 : ℚ) ^ n - 7 := by linarith
    have hb : 0 ≤ (2 : ℚ) ^ n - 2 := by linarith
    have hmul := mul_nonneg ha hb
    have hquad : (26 : ℚ) * (2 : ℚ) ^ n - 28 ≤
        6 * (4 : ℚ) ^ n := by
      rw [hpow]
      nlinarith
    have hden : 0 < (25 : ℚ) * (4 : ℚ) ^ n := by positivity
    have hfrac :
        ((26 : ℚ) * (2 : ℚ) ^ n - 28) / (25 * (4 : ℚ) ^ n)
          ≤ 6 / 25 := by
      apply (div_le_iff₀ hden).2
      convert hquad using 1 <;> ring
    unfold exactRampMean
    linarith

theorem exactRampMean_first :
    exactRampMean 1 = (26 / 25 : ℚ) := by
  norm_num [exactRampMean]

#print axioms exactRampMean_le
#print axioms exactRampMean_first

end LaaksoRampMean
