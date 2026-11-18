import Mathlib

/-!
# Euclidean-index decomposition for arbitrary Jordan chain lengths

For q = p+1, the integer degrees split uniquely by residues
r in {0,...,p} and levels m, with index r + m*q.
This is the combinatorial indexing used in the constructive Jordan
basis; it is deliberately separate from the proof that the actual
transfer operator has the required leading coefficients.
-/

namespace OrbitTrace

def chainLength (p d r : ℕ) : ℕ :=
  if r ≤ d then (d - r) / (p + 1) + 1 else 0

theorem chain_index_divmod (p k : ℕ) :
    k = k % (p + 1) + (k / (p + 1)) * (p + 1) := by
  simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div k (p + 1)).symm

theorem chain_index_bound (p d r m : ℕ)
    (hm : m < chainLength p d r) :
    r + m * (p + 1) ≤ d := by
  unfold chainLength at hm
  by_cases hr : r ≤ d
  · simp only [ite_eq_left hr] at hm
    have hml : m ≤ (d - r) / (p + 1) := by omega
    have hmul : m * (p + 1) ≤ ((d - r) / (p + 1)) * (p + 1) :=
      Nat.mul_le_mul_right (p + 1) hml
    have hbound : ((d - r) / (p + 1)) * (p + 1) ≤ d - r :=
      Nat.div_mul_le_self (d - r) (p + 1)
    omega
  · simp [hr] at hm

theorem chain_index_unique (p r s m n : ℕ)
    (hr : r ≤ p) (hs : s ≤ p)
    (hindex : r + m * (p + 1) = s + n * (p + 1)) :
    r = s ∧ m = n := by
  have hrlt : r < p + 1 := by omega
  have hslt : s < p + 1 := by omega
  have hmod := congrArg (fun k : ℕ => k % (p + 1)) hindex
  have hrs : r = s := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hrlt,
      Nat.mod_eq_of_lt hslt] using hmod
  subst s
  have hprod : m * (p + 1) = n * (p + 1) :=
    Nat.add_left_cancel hindex
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega) hprod⟩


theorem chain_index_exists (p d k : ℕ) (hk : k ≤ d) :
    ∃ r m : ℕ,
      r ≤ p ∧ m < chainLength p d r ∧ k = r + m * (p + 1) := by
  let r := k % (p + 1)
  let m := k / (p + 1)
  have hq : 0 < p + 1 := by omega
  have hrlt : r < p + 1 := Nat.mod_lt k hq
  have hrepr : k = r + m * (p + 1) := by
    simpa only [r, m] using chain_index_divmod p k
  have hrle : r ≤ d := by omega
  have hm_le : m ≤ (d - r) / (p + 1) := by
    apply (Nat.le_div_iff_mul_le hq).2
    omega
  have hm : m < chainLength p d r := by
    simp only [chainLength, ite_eq_left hrle]
    omega
  exact ⟨r, m, by omega, hm, hrepr⟩

#print axioms OrbitTrace.chain_index_exists

#print axioms OrbitTrace.chain_index_divmod
#print axioms OrbitTrace.chain_index_bound
#print axioms OrbitTrace.chain_index_unique

end OrbitTrace
