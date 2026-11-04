import Mathlib

/-!
# Every monic polynomial moment recurrence is unitriangular

An arbitrary sequence M_k over Q[X] with
  M_k = X^k       (0 <= k <= p)
  M_(k+p+1) = X*M_(k+p) - C(a)*M_k
has degree k and is monic for every k. It therefore defines a polynomial
sequence, not just a finite collection of checked moments.

The statement is conditional on the recurrence and does not identify
arbitrary root traces with this polynomial sequence by itself.
-/

namespace OrbitTrace

open Polynomial

theorem polynomial_moment_monic_degree
    (p : ℕ) (a : ℚ) (M : ℕ → Polynomial ℚ)
    (hinit : ∀ k, k ≤ p → M k = X ^ k)
    (hrec : ∀ k, M (k + p + 1) = X * M (k + p) - C a * M k) :
    ∀ k : ℕ, (M k).Monic ∧ (M k).degree = (k : WithBot ℕ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k ≤ p
      · rw [hinit k hk]
        exact ⟨monic_X_pow k, degree_X_pow k⟩
      · have hprev : k - 1 < k := by omega
        have hsub : k - (p + 1) < k := by omega
        obtain ⟨hmprev, hdprev⟩ := ih (k - 1) hprev
        obtain ⟨_, hdsub⟩ := ih (k - (p + 1)) hsub
        have heq1 : k - (p + 1) + p + 1 = k := by omega
        have heq2 : k - (p + 1) + p = k - 1 := by omega
        have heq3 : k - 1 + 1 = k := by omega
        have hform : M k = X * M (k - 1) - C a * M (k - (p + 1)) := by
          simpa only [heq1, heq2, heq3] using hrec (k - (p + 1))
        have hmono : (X * M (k - 1)).Monic := monic_X.mul hmprev
        have hdeg : (X * M (k - 1)).degree = (k : WithBot ℕ) := by
          calc
            (X * M (k - 1)).degree = (M (k - 1) * X).degree := by
              rw [mul_comm]
            _ = (M (k - 1)).degree + 1 := degree_mul_X
            _ = (k : WithBot ℕ) := by
              rw [hdprev]
              norm_cast
        have hright : (C a * M (k - (p + 1))).degree ≤
            ((k - (p + 1) : ℕ) : WithBot ℕ) := by
          calc
            (C a * M (k - (p + 1))).degree ≤
                (C a).degree + (M (k - (p + 1))).degree :=
              degree_mul_le _ _
            _ ≤ (0 : WithBot ℕ) + ((k - (p + 1) : ℕ) : WithBot ℕ) := by
              rw [hdsub]
              exact add_le_add degree_C_le le_rfl
            _ = ((k - (p + 1) : ℕ) : WithBot ℕ) := by simp
        have hlt : (C a * M (k - (p + 1))).degree <
            (X * M (k - 1)).degree := by
          rw [hdeg]
          apply lt_of_le_of_lt hright
          norm_cast
        rw [hform]
        exact ⟨hmono.sub_of_left hlt, by
          rw [degree_sub_eq_left_of_degree_lt hlt, hdeg]⟩

noncomputable def polynomialMomentSequence
    (p : ℕ) (a : ℚ) (M : ℕ → Polynomial ℚ)
    (hinit : ∀ k, k ≤ p → M k = X ^ k)
    (hrec : ∀ k, M (k + p + 1) = X * M (k + p) - C a * M k) :
    Polynomial.Sequence ℚ where
  elems' := M
  degree_eq' k := (polynomial_moment_monic_degree p a M hinit hrec k).2

theorem polynomial_moment_linearIndependent
    (p : ℕ) (a : ℚ) (M : ℕ → Polynomial ℚ)
    (hinit : ∀ k, k ≤ p → M k = X ^ k)
    (hrec : ∀ k, M (k + p + 1) = X * M (k + p) - C a * M k) :
    LinearIndependent ℚ M := by
  exact (polynomialMomentSequence p a M hinit hrec).linearIndependent

#print axioms OrbitTrace.polynomial_moment_monic_degree
#print axioms OrbitTrace.polynomial_moment_linearIndependent

end OrbitTrace
