import OrbitTraceMonicSequence

/-!
General degree-drop bound for the concrete moment recurrence.

For q=p+1 the non-leading part of every moment M(k) has degree <= k-q,
without any assumptions on the parameter a. This is stronger than the
previous degree < k result. A *nonzero* coefficient at k-q for a != 0
is a separate assertion.
-/

namespace OrbitTrace

open Polynomial

theorem polynomial_moment_q_gap
    (p : ℕ) (a : ℚ) (M : ℕ → Polynomial ℚ)
    (hinit : ∀ k, k ≤ p → M k = X ^ k)
    (hrec : ∀ k, M (k + p + 1) = X * M (k + p) - C a * M k) :
    ∀ k : ℕ,
      (M k - X ^ k).degree ≤ ((k - (p + 1) : ℕ) : WithBot ℕ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k ≤ p
      · rw [hinit k hk, sub_self]
        simp
      · have hkq : p + 1 ≤ k := by omega
        have hpred : k - 1 < k := by omega
        have hsub : k - (p + 1) < k := by omega
        have h1 : k - (p + 1) + p + 1 = k := by omega
        have h2 : k - (p + 1) + p = k - 1 := by omega
        have h3 : k - 1 + 1 = k := by omega
        have hform : M k = X * M (k - 1) - C a * M (k - (p + 1)) := by
          simpa only [h1, h2, h3] using hrec (k - (p + 1))
        have hpow : (X : Polynomial ℚ) ^ k =
            X * X ^ (k - 1) := by
          conv_lhs => rw [← h3]
          rw [pow_succ]
          ring
        have hdelta : M k - X ^ k =
            X * (M (k - 1) - X ^ (k - 1)) -
              C a * M (k - (p + 1)) := by
          rw [hform, hpow]
          ring
        have hleft :
            (X * (M (k - 1) - X ^ (k - 1))).degree ≤
                ((k - (p + 1) : ℕ) : WithBot ℕ) := by
          by_cases hsmall : k - 1 ≤ p
          · rw [hinit (k - 1) hsmall, sub_self, mul_zero]
            simp
          · have hih := ih (k - 1) hpred
            have hlt : ((1 : WithBot ℕ) +
                  ((k - 1 - (p + 1) : ℕ) : WithBot ℕ)) =
                  ((k - (p + 1) : ℕ) : WithBot ℕ) := by
              norm_cast
              omega
            calc
              (X * (M (k - 1) - X ^ (k - 1))).degree ≤
                  (X : Polynomial ℚ).degree +
                    (M (k - 1) - X ^ (k - 1)).degree :=
                    degree_mul_le _ _
              _ ≤ (1 : WithBot ℕ) +
                    ((k - 1 - (p + 1) : ℕ) : WithBot ℕ) := by
                  rw [degree_X]
                  exact add_le_add le_rfl hih
              _ = ((k - (p + 1) : ℕ) : WithBot ℕ) := hlt
        have hright :
            (C a * M (k - (p + 1))).degree ≤
                ((k - (p + 1) : ℕ) : WithBot ℕ) := by
          have hdegree :=
            (polynomial_moment_monic_degree p a M hinit hrec
              (k - (p + 1))).2
          calc
            (C a * M (k - (p + 1))).degree ≤
                (C a).degree + (M (k - (p + 1))).degree :=
                degree_mul_le _ _
            _ ≤ (0 : WithBot ℕ) +
                ((k - (p + 1) : ℕ) : WithBot ℕ) := by
                  rw [hdegree]
                  exact add_le_add degree_C_le le_rfl
            _ = ((k - (p + 1) : ℕ) : WithBot ℕ) := by simp
        rw [hdelta]
        exact (degree_sub_le _ _).trans (max_le hleft hright)

#print axioms OrbitTrace.polynomial_moment_q_gap

end OrbitTrace
