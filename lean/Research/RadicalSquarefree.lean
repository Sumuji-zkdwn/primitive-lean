import Mathlib

/-!
# The fixed points of the radical are the squarefree numbers

`docs/verification/2026-11-05-radical-f0-bridge.md` proves in
`linear_input/lean_check/RadicalF0Bridge.inc` that a nonzero squarefree number is fixed by
`radical(n) = ∏_{p ∣ n} p` (`squarefree_fixed`) and records that the reverse implication is
not formalized. This independent module copies the definition verbatim and proves:

* `radical_squarefree`: `radical n` is squarefree for `n ≠ 0`;
* `radical_eq_self_iff`: `radical n = n ↔ n = 0 ∨ Squarefree n` (the converse of
  `squarefree_fixed`, with the zero convention);
* `range_radical`: the image of `radical` is `{0} ∪ {squarefree numbers}`, which is also
  its fixed-point set;
* `squarefree_dvd_radical`, `radical_dvd`: `radical n` is the greatest squarefree divisor
  of `n ≠ 0` (every squarefree divisor divides it);
* `radical_mul_of_coprime`: `radical (a * b) = radical a * radical b` for coprime `a, b`.

No identification with the joint-checker declarations is made.
-/

namespace RadicalSquarefree

/-- Product of the distinct prime factors, with the conventional zero case
(copied from `RadicalF0Bridge.inc`). -/
def radical (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, p

theorem radical_eq_product {n : ℕ} (hn : n ≠ 0) : radical n = ∏ p ∈ n.primeFactors, p := by
  simp [radical, hn]

theorem radical_zero : radical 0 = 0 := by simp [radical]

theorem radical_ne_zero {n : ℕ} (hn : n ≠ 0) : radical n ≠ 0 := by
  rw [radical_eq_product hn]
  exact Finset.prod_ne_zero_iff.mpr fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem radical_squarefree {n : ℕ} (hn : n ≠ 0) : Squarefree (radical n) := by
  rw [radical_eq_product hn]
  exact Nat.squarefree_prod_primeFactors n

theorem radical_dvd (n : ℕ) : radical n ∣ n := by
  by_cases hn : n = 0
  · simp [hn, radical_zero]
  · rw [radical_eq_product hn]
    exact Nat.prod_primeFactors_dvd n

theorem radical_primeFactors (n : ℕ) : (radical n).primeFactors = n.primeFactors := by
  by_cases hn : n = 0
  · simp [hn, radical_zero]
  · rw [radical_eq_product hn]
    exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors hp

/-- **Converse of `squarefree_fixed`**: the fixed points of the radical are `0` and the
squarefree numbers. -/
theorem radical_eq_self_iff (n : ℕ) : radical n = n ↔ n = 0 ∨ Squarefree n := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exact Or.inl hn
    · exact Or.inr (h ▸ radical_squarefree hn)
  · rintro (rfl | hs)
    · exact radical_zero
    · rw [radical_eq_product hs.ne_zero]
      exact Nat.prod_primeFactors_of_squarefree hs

theorem radical_radical (n : ℕ) : radical (radical n) = radical n := by
  by_cases hn : n = 0
  · simp [hn, radical_zero]
  · exact (radical_eq_self_iff _).mpr (Or.inr (radical_squarefree hn))

/-- The image of the radical is `{0}` together with the squarefree numbers. -/
theorem range_radical : Set.range radical = {0} ∪ {n | Squarefree n} := by
  ext n
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, rfl⟩
    by_cases hm : m = 0
    · left; simp [hm, radical_zero]
    · right; exact radical_squarefree hm
  · intro h
    exact ⟨n, (radical_eq_self_iff n).mpr h⟩

/-- **The radical is the greatest squarefree divisor**: every squarefree divisor of a
nonzero `n` divides `radical n`. -/
theorem squarefree_dvd_radical {n d : ℕ} (hn : n ≠ 0) (hd : Squarefree d) (hdn : d ∣ n) :
    d ∣ radical n := by
  rw [← (radical_eq_self_iff d).mpr (Or.inr hd), radical_eq_product hd.ne_zero,
    radical_eq_product hn]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono hdn hn)

theorem radical_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    radical (a * b) = radical a * radical b := by
  rw [radical_eq_product (mul_ne_zero ha hb), radical_eq_product ha, radical_eq_product hb,
    Nat.Coprime.primeFactors_mul hab]
  exact Finset.prod_union hab.disjoint_primeFactors

/-- Concrete values: `rad 12 = 6`, `rad 30 = 30`, `rad 72 = 6`. -/
theorem radical_examples : radical 12 = 6 ∧ radical 30 = 30 ∧ radical 72 = 6 := by
  refine ⟨?_, ?_, ?_⟩
  · have : (12 : ℕ) = 4 * 3 := by norm_num
    rw [this, radical_mul_of_coprime (by norm_num) (by norm_num) (by norm_num)]
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, radical_eq_product (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      (radical_eq_self_iff 3).mpr (Or.inr (Nat.prime_three.squarefree))]
    simp
  · exact (radical_eq_self_iff 30).mpr (Or.inr (by
      rw [show (30 : ℕ) = 2 * 15 by norm_num]
      exact (Nat.squarefree_mul (by norm_num)).mpr ⟨Nat.prime_two.squarefree,
        (Nat.squarefree_mul (by norm_num)).mpr ⟨Nat.prime_three.squarefree,
          Nat.prime_five.squarefree⟩⟩))
  · have : (72 : ℕ) = 8 * 9 := by norm_num
    rw [this, radical_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      show (8 : ℕ) = 2 ^ 3 by norm_num, show (9 : ℕ) = 3 ^ 2 by norm_num,
      radical_eq_product (by norm_num), radical_eq_product (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
    simp

end RadicalSquarefree

#print axioms RadicalSquarefree.radical_squarefree
#print axioms RadicalSquarefree.radical_eq_self_iff
#print axioms RadicalSquarefree.range_radical
#print axioms RadicalSquarefree.squarefree_dvd_radical
#print axioms RadicalSquarefree.radical_mul_of_coprime
#print axioms RadicalSquarefree.radical_examples
