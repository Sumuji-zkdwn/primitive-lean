import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Basic

/-!
# Deterministic bounds for public reinterpretation updates

This file formalizes only the deterministic algebra used by the stage-two
finite models. It proves a finite counting bound for prepared columns, the
natural-number rearrangement of its certainty threshold, and identities for
repeated squaring in an abstract monoid.

The column counts represent distinct previously read bits. The counting theorem
does not itself prove that unread independent bits hide a parity, or that a
probability bound is optimal. The repeated-squaring identities provide caching
and related-input shortcuts; they are not a proof of sequential computational
hardness, cryptographic security, or a real-time deadline.
-/

namespace RetroactiveWorkBounds

open scoped BigOperators

section PreparedColumns

variable {ι : Type*}

/-- Columns with at least `d` distinct bits already inspected. -/
def coveredColumns (columns : Finset ι) (probes : ι → ℕ) (d : ℕ) : Finset ι :=
  columns.filter fun i => d ≤ probes i

theorem coveredColumns_subset (columns : Finset ι) (probes : ι → ℕ) (d : ℕ) :
    coveredColumns columns probes d ⊆ columns := by
  exact Finset.filter_subset _ _

theorem coveredColumns_card_le (columns : Finset ι) (probes : ι → ℕ) (d : ℕ) :
    (coveredColumns columns probes d).card ≤ columns.card := by
  exact Finset.card_le_card (coveredColumns_subset columns probes d)

/-- Each covered column consumes at least `d` of the total inspected bits.
This includes `d = 0`; positivity is needed only for the division corollary. -/
theorem coveredColumns_card_mul_le_budget
    (columns : Finset ι) (probes : ι → ℕ) (d p : ℕ)
    (hbudget : (∑ i ∈ columns, probes i) ≤ p) :
    (coveredColumns columns probes d).card * d ≤ p := by
  calc
    (coveredColumns columns probes d).card * d =
        ∑ _i ∈ coveredColumns columns probes d, d := by simp
    _ ≤ ∑ i ∈ coveredColumns columns probes d, probes i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i ∈ columns, probes i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (coveredColumns_subset columns probes d)
      intro i _ _
      exact Nat.zero_le (probes i)
    _ ≤ p := hbudget

/-- A positive threshold bounds the number of prepared columns by `p / d`. -/
theorem coveredColumns_card_le_div
    (columns : Finset ι) (probes : ι → ℕ) (d p : ℕ)
    (hd : 0 < d) (hbudget : (∑ i ∈ columns, probes i) ≤ p) :
    (coveredColumns columns probes d).card ≤ p / d := by
  apply (Nat.le_div_iff_mul_le hd).2
  exact coveredColumns_card_mul_le_budget columns probes d p hbudget

/-- There are also no more prepared columns than columns in the table. -/
theorem coveredColumns_card_le_min
    (columns : Finset ι) (probes : ι → ℕ) (d p : ℕ)
    (hd : 0 < d) (hbudget : (∑ i ∈ columns, probes i) ≤ p) :
    (coveredColumns columns probes d).card ≤ min columns.card (p / d) := by
  exact le_min (coveredColumns_card_le columns probes d)
    (coveredColumns_card_le_div columns probes d p hd hbudget)

/-- For `N` bits per column and fewer than `N` allowed subsequent probes,
the preparation threshold is the positive natural number `N - q`. -/
theorem readyColumns_card_le_min
    (columns : Finset ι) (probes : ι → ℕ) (N q p : ℕ)
    (hq : q < N) (hbudget : (∑ i ∈ columns, probes i) ≤ p) :
    (coveredColumns columns probes (N - q)).card ≤
      min columns.card (p / (N - q)) := by
  exact coveredColumns_card_le_min columns probes (N - q) p
    (Nat.sub_pos_of_lt hq) hbudget

end PreparedColumns

/-- With `q ≤ N`, preparing the remaining `N-q` bits in each of `M` columns
has the same natural-number threshold as `p + M*q ≥ N*M`.
No probability statement or attainability assumption is hidden in this lemma. -/
theorem certainty_budget_iff (N M q p : ℕ) (hq : q ≤ N) :
    M * (N - q) ≤ p ↔ N * M ≤ p + M * q := by
  have hsplit : M * (N - q) + M * q = N * M := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hq, Nat.mul_comm M N]
  constructor
  · intro h
    calc
      N * M = M * (N - q) + M * q := hsplit.symm
      _ ≤ p + M * q := Nat.add_le_add_right h (M * q)
  · intro h
    have h' : M * (N - q) + M * q ≤ p + M * q := by
      rw [hsplit]
      exact h
    exact Nat.le_of_add_le_add_right h'

section RepeatedSquaring

variable {G : Type*} [Monoid G]

/-- The result of `T` repeated squarings, as an algebraic value.
The definition does not specify the cost of evaluating that value. -/
def repeatedSquare (T : ℕ) (a : G) : G := a ^ (2 ^ T)

@[simp] theorem repeatedSquare_zero (a : G) : repeatedSquare 0 a = a := by
  simp [repeatedSquare]

theorem repeatedSquare_succ (T : ℕ) (a : G) :
    repeatedSquare (T + 1) a = (repeatedSquare T a) ^ 2 := by
  unfold repeatedSquare
  rw [pow_succ, pow_mul]

/-- A cached value at `T` can be advanced by applying only the `delta`-step
map. This identity does not claim that the resulting algorithm is optimal. -/
theorem repeatedSquare_add (T delta : ℕ) (a : G) :
    repeatedSquare (T + delta) a =
      repeatedSquare delta (repeatedSquare T a) := by
  unfold repeatedSquare
  rw [pow_add, pow_mul]

/-- Updating to a publicly related base `a^r` can reuse the old output.
This identity is valid even when the ambient monoid is noncommutative. -/
theorem repeatedSquare_pow (T r : ℕ) (a : G) :
    repeatedSquare T (a ^ r) = (repeatedSquare T a) ^ r := by
  unfold repeatedSquare
  rw [← pow_mul, ← pow_mul, Nat.mul_comm r (2 ^ T)]

end RepeatedSquaring

/-- A product of known bases gives a product of known outputs in a
commutative monoid. Commutativity is an explicit additional hypothesis. -/
theorem repeatedSquare_mul {G : Type*} [CommMonoid G]
    (T : ℕ) (a b : G) :
    repeatedSquare T (a * b) = repeatedSquare T a * repeatedSquare T b := by
  simp only [repeatedSquare, mul_pow]

end RetroactiveWorkBounds
