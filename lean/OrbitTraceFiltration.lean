import OrbitTraceTransferOperator
import OrbitTraceNilpotence

/-!
# A genuine locally nilpotent polynomial transfer operator

The canonical transfer is a Q-linear map on Q[X]. The deviation
N = L - id sends each polynomial of degree <= d to a polynomial of
degree <= d - (p+1), and vanishes on degree <= p.

Consequently N is locally nilpotent: every polynomial is annihilated
after at most degree+1 iterations, without assuming a!=0. The precise
faster nilpotence index and all-degree Jordan ranks remain separate.
-/

namespace OrbitTrace

open Polynomial

private theorem polynomial_as_smul_monomials (P : Polynomial ℚ) :
    P = ∑ i ∈ P.support, P.coeff i • (X : Polynomial ℚ) ^ i := by
  classical
  calc
    P = P.sum (fun n c => monomial n c) := (sum_monomial_eq P).symm
    _ = ∑ i ∈ P.support, monomial i (P.coeff i) := rfl
    _ = ∑ i ∈ P.support, P.coeff i • (X : Polynomial ℚ) ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_X_eq_monomial]

theorem canonicalDelta_degree_bound (p : ℕ) (a : ℚ)
    (d : ℕ) (P : Polynomial ℚ) (hdegree : P.natDegree ≤ d) :
    (canonicalDelta p a P).degree ≤
      ((d - (p + 1) : ℕ) : WithBot ℕ) := by
  classical
  have hP := polynomial_as_smul_monomials P
  have hsum :
      canonicalDelta p a P =
        ∑ i ∈ P.support, P.coeff i •
          canonicalDelta p a ((X : Polynomial ℚ) ^ i) := by
    conv_lhs => rw [hP]
    simp only [map_sum, map_smul]
  rw [hsum]
  refine (degree_sum_le _ _).trans (Finset.sup_le fun i hi => ?_)
  have hcoeff : P.coeff i ≠ 0 := by
    simpa only [mem_support_iff] using hi
  have hiDegree : i ≤ d :=
    (le_natDegree_of_ne_zero hcoeff).trans hdegree
  by_cases hsmall : i ≤ p
  · have hzero : canonicalDelta p a ((X : Polynomial ℚ) ^ i) = 0 := by
      rw [canonicalDelta_X_pow, canonicalMoment_initial p i a hsmall, sub_self]
    rw [hzero, smul_zero]
    exact bot_le
  · have hbound :
        (canonicalDelta p a ((X : Polynomial ℚ) ^ i)).degree ≤
          ((i - (p + 1) : ℕ) : WithBot ℕ) := by
      rw [canonicalDelta_X_pow]
      exact polynomial_moment_q_gap p a (canonicalMoment p a)
        (by intro j hj; exact canonicalMoment_initial p j a hj)
        (by intro j; exact canonicalMoment_recurrence p j a)
        i
    calc
      (P.coeff i • canonicalDelta p a ((X : Polynomial ℚ) ^ i)).degree ≤
        (canonicalDelta p a ((X : Polynomial ℚ) ^ i)).degree :=
          degree_smul_le _ _
      _ ≤ ((i - (p + 1) : ℕ) : WithBot ℕ) := hbound
      _ ≤ ((d - (p + 1) : ℕ) : WithBot ℕ) := by
        norm_cast
        omega

theorem canonicalDelta_zero_of_low_degree (p : ℕ) (a : ℚ)
    (P : Polynomial ℚ) (hdegree : P.natDegree ≤ p) :
    canonicalDelta p a P = 0 := by
  classical
  have hP := polynomial_as_smul_monomials P
  rw [hP]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro i hi
  have hcoeff : P.coeff i ≠ 0 := by
    simpa only [mem_support_iff] using hi
  have hiDegree : i ≤ p :=
    (le_natDegree_of_ne_zero hcoeff).trans hdegree
  have hz : canonicalDelta p a ((X : Polynomial ℚ) ^ i) = 0 := by
    rw [canonicalDelta_X_pow, canonicalMoment_initial p i a hiDegree, sub_self]
  simp [hz]

theorem canonicalDelta_strict_degree_or_zero (p : ℕ) (a : ℚ)
    (P : Polynomial ℚ) (hP : P ≠ 0) :
    canonicalDelta p a P = 0 ∨
      (canonicalDelta p a P).natDegree < P.natDegree := by
  clear hP
  by_cases hsmall : P.natDegree ≤ p
  · exact Or.inl (canonicalDelta_zero_of_low_degree p a P hsmall)
  · right
    have hbound :=
      canonicalDelta_degree_bound p a P.natDegree P (le_refl _)
    have hnat :
        (canonicalDelta p a P).natDegree ≤ P.natDegree - (p + 1) :=
      (natDegree_le_iff_degree_le).2 hbound
    omega

theorem canonicalDelta_local_nilpotent (p : ℕ) (a : ℚ)
    (d : ℕ) (P : Polynomial ℚ) (hdegree : P.natDegree ≤ d) :
    iterDrop (fun Q : Polynomial ℚ => canonicalDelta p a Q) (d + 1) P = 0 := by
  exact polynomial_degree_drop_nilpotent (canonicalDelta p a)
    (by intro Q hQ; exact canonicalDelta_strict_degree_or_zero p a Q hQ)
    d P hdegree

#print axioms OrbitTrace.canonicalDelta_degree_bound
#print axioms OrbitTrace.canonicalDelta_zero_of_low_degree
#print axioms OrbitTrace.canonicalDelta_local_nilpotent

end OrbitTrace
