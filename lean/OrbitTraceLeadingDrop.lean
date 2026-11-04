import OrbitTraceDegreeGap

/-!
The leading nontrivial coefficient of the p+1-degree deviation.

For k >= q=p+1, if a!=0, the coefficient of X^(k-q) in
M(k) - X^k is -(k-p)*a, so the previously verified upper
bound is sharp.

This theorem is for an arbitrary polynomial sequence satisfying the
initial conditions and recurrence, hence applies to canonicalMoment.
-/

namespace OrbitTrace

open Polynomial

theorem polynomial_moment_delta_step
    (p : ℕ) (a : ℚ) (M : ℕ → Polynomial ℚ)
    (hrec : ∀ k, M (k + p + 1) = X * M (k + p) - C a * M k)
    (k : ℕ) (hk : p + 1 ≤ k) :
    M k - X ^ k =
      X * (M (k - 1) - X ^ (k - 1)) -
        C a * M (k - (p + 1)) := by
  have h1 : k - (p + 1) + p + 1 = k := by omega
  have h2 : k - (p + 1) + p = k - 1 := by omega
  have h3 : k - 1 + 1 = k := by omega
  have hform : M k = X * M (k - 1) - C a * M (k - (p + 1)) := by
    simpa only [h1, h2, h3] using hrec (k - (p + 1))
  have hpow : (X : Polynomial ℚ) ^ k = X * X ^ (k - 1) := by
    conv_lhs => rw [← h3]
    rw [pow_succ]
    ring
  rw [hform, hpow]
  ring

theorem polynomial_moment_gap_coefficient
    (p : ℕ) (a : ℚ) (M : ℕ → Polynomial ℚ)
    (hinit : ∀ k, k ≤ p → M k = X ^ k)
    (hrec : ∀ k, M (k + p + 1) = X * M (k + p) - C a * M k) :
    ∀ k : ℕ, p + 1 ≤ k →
      (M k - X ^ k).coeff (k - (p + 1)) =
        -(((k - p : ℕ) : ℚ) * a) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      have hdelta := polynomial_moment_delta_step p a M hrec k hk
      obtain ⟨hm, hd⟩ :=
        polynomial_moment_monic_degree p a M hinit hrec (k - (p + 1))
      have hnat : (M (k - (p + 1))).natDegree = k - (p + 1) :=
        natDegree_eq_of_degree_eq_some hd
      have hlead : (M (k - (p + 1))).coeff (k - (p + 1)) = 1 := by
        change (M (k - (p + 1))).leadingCoeff = 1 at hm
        simpa only [leadingCoeff, hnat] using hm
      by_cases hbase : k = p + 1
      · have hsmall : k - 1 ≤ p := by omega
        have hn : k - p = 1 := by omega
        rw [hdelta, hinit (k - 1) hsmall, sub_self, mul_zero,
            zero_sub, coeff_neg, coeff_C_mul, hlead, hn]
        ring
      · have hprev : p + 1 ≤ k - 1 := by omega
        have hpind := ih (k - 1) (by omega) hprev
        have hidx : k - (p + 1) = (k - 1 - (p + 1)) + 1 := by omega
        have hnum : k - p = k - 1 - p + 1 := by omega
        have hcoefX : (X * (M (k - 1) - X ^ (k - 1))).coeff
            (k - (p + 1)) =
            (M (k - 1) - X ^ (k - 1)).coeff
              (k - 1 - (p + 1)) := by
          rw [hidx]
          exact coeff_X_mul _ _
        rw [hdelta, coeff_sub, coeff_C_mul, hcoefX, hlead, hpind, hnum]
        push_cast
        ring


theorem polynomial_moment_exact_degree_drop
    (p : ℕ) (a : ℚ) (ha : a ≠ 0) (M : ℕ → Polynomial ℚ)
    (hinit : ∀ k, k ≤ p → M k = X ^ k)
    (hrec : ∀ k, M (k + p + 1) = X * M (k + p) - C a * M k)
    (k : ℕ) (hk : p + 1 ≤ k) :
    (M k - X ^ k).degree =
        ((k - (p + 1) : ℕ) : WithBot ℕ) := by
  have hupper := polynomial_moment_q_gap p a M hinit hrec k
  have hcoeff := polynomial_moment_gap_coefficient p a M hinit hrec k hk
  have hkpos : 0 < k - p := by omega
  have hfactor : (((k - p : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hkpos)
  have hnonzero :
      (M k - X ^ k).coeff (k - (p + 1)) ≠ 0 := by
    rw [hcoeff]
    exact neg_ne_zero.mpr (mul_ne_zero hfactor ha)
  exact degree_eq_of_le_of_coeff_ne_zero hupper hnonzero

#print axioms OrbitTrace.polynomial_moment_exact_degree_drop

#print axioms OrbitTrace.polynomial_moment_gap_coefficient

end OrbitTrace
