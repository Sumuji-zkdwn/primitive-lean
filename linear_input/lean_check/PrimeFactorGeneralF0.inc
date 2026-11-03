/-!
A canonical F0 operation on *arbitrary finite lists* of natural numbers.

F0 orders the entries of a list and discards their previous order.
It is idempotent and its observational kernel is precisely List.Perm.

When *each list entry is prime*, the kernel of list multiplication
coincides with the kernel of F0. The converse implication uses the
existing Mathlib theorem Nat.primeFactorsList_unique (the fundamental
theorem of arithmetic), not an independently derived uniqueness proof.

This proof does not count the runtime of sorting or factoring. It
does not assert that F0 coincides with any earlier concrete F0 map.
-/

namespace LinearInputPrimeFactorGeneralF0

/-- Sorting gives a computationally explicit canonical normal form. -/
def normalize (xs : List ℕ) : List ℕ :=
  ((xs : Multiset ℕ).sort (fun a b => a ≤ b))

/-- Converting the normal form back to a multiset forgets exactly
the ordering, without losing any multiplicities. -/
theorem normalize_multiset (xs : List ℕ) :
    (normalize xs : Multiset ℕ) = (xs : Multiset ℕ) := by
  simp [normalize]

/-- Sorting preserves the length of an arbitrary finite list. -/
theorem normalize_length (xs : List ℕ) :
    (normalize xs).length = xs.length := by
  simp [normalize]

/-- The normal form is a sorted list. -/
theorem normalize_sorted (xs : List ℕ) :
    List.Pairwise (fun a b : ℕ => a ≤ b) (normalize xs) := by
  exact Multiset.pairwise_sort (xs : Multiset ℕ) (fun a b => a ≤ b)

/-- This is an idempotent F0-style forgetting operator. -/
theorem normalize_idempotent (xs : List ℕ) :
    normalize (normalize xs) = normalize xs := by
  unfold normalize
  rw [Multiset.sort_eq]

/-- Equal normalized outputs iff the original lists were permutations. -/
theorem normalize_eq_iff_perm (xs ys : List ℕ) :
    normalize xs = normalize ys ↔ xs.Perm ys := by
  constructor
  · intro h
    have hcast := congrArg (fun l : List ℕ => (l : Multiset ℕ)) h
    have hbag : (xs : Multiset ℕ) = (ys : Multiset ℕ) := by
      calc
        (xs : Multiset ℕ) = (normalize xs : Multiset ℕ) :=
          (normalize_multiset xs).symm
        _ = (normalize ys : Multiset ℕ) := hcast
        _ = (ys : Multiset ℕ) := normalize_multiset ys
    exact Multiset.coe_eq_coe.mp hbag
  · intro h
    have hbag : (xs : Multiset ℕ) = (ys : Multiset ℕ) :=
      Multiset.coe_eq_coe.mpr h
    exact congrArg (fun s : Multiset ℕ =>
      s.sort (fun a b : ℕ => a ≤ b)) hbag

/-- Sorting retains the exact multiplication result even when entries
are not necessarily prime. -/
theorem normalize_preserves_product (xs : List ℕ) :
    (normalize xs).prod = xs.prod := by
  have h := congrArg (fun s : Multiset ℕ => s.prod)
    (normalize_multiset xs)
  simpa using h

/-- A function of lists factors through F0 iff it is permutation-invariant. -/
theorem factors_through_normalize_iff {β : Type*} (f : List ℕ → β) :
    (∃ g : List ℕ → β, ∀ xs, f xs = g (normalize xs)) ↔
    (∀ xs ys, xs.Perm ys → f xs = f ys) := by
  constructor
  · rintro ⟨g, hg⟩ xs ys hperm
    have hn := (normalize_eq_iff_perm xs ys).mpr hperm
    calc
      f xs = g (normalize xs) := hg xs
      _ = g (normalize ys) := congrArg g hn
      _ = f ys := (hg ys).symm
  · intro h
    refine ⟨f, ?_⟩
    intro xs
    exact h xs (normalize xs)
      (Multiset.coe_eq_coe.mp (normalize_multiset xs).symm)

/-- A list of primes has no non-prime entries. -/
def AllPrime (xs : List ℕ) : Prop :=
  ∀ p, p ∈ xs → Nat.Prime p

/-- Existing prime-factorization uniqueness identifies the kernel of
products of two arbitrary finite lists of primes with List.Perm. -/
theorem prime_product_eq_iff_perm (xs ys : List ℕ)
    (hxs : AllPrime xs) (hys : AllPrime ys) :
    xs.prod = ys.prod ↔ xs.Perm ys := by
  constructor
  · intro hprod
    have hx : xs.Perm xs.prod.primeFactorsList :=
      Nat.primeFactorsList_unique rfl hxs
    have hy : ys.Perm ys.prod.primeFactorsList :=
      Nat.primeFactorsList_unique rfl hys
    rw [hprod] at hx
    exact hx.trans hy.symm
  · intro hperm
    have hb : (xs : Multiset ℕ) = (ys : Multiset ℕ) :=
      Multiset.coe_eq_coe.mpr hperm
    have hv := congrArg (fun s : Multiset ℕ => s.prod) hb
    simpa using hv

/-- General product and F0 kernels coincide on any finite prime words.
This explicitly *uses* Mathlib's existing factorization uniqueness. -/
theorem prime_product_kernel_eq_normalize_kernel (xs ys : List ℕ)
    (hxs : AllPrime xs) (hys : AllPrime ys) :
    xs.prod = ys.prod ↔ normalize xs = normalize ys :=
  (prime_product_eq_iff_perm xs ys hxs hys).trans
    (normalize_eq_iff_perm xs ys).symm

/-- Any probe invariant on prime-product fibers is unchanged by sorting
when applied to lists of primes, provided the function itself is defined
on all lists. -/
theorem prime_product_invariant_of_normalize
    {β : Type*} (f : List ℕ → β)
    (h : ∀ xs ys, AllPrime xs → AllPrime ys →
       xs.prod = ys.prod → f xs = f ys)
    (xs : List ℕ) (hxs : AllPrime xs) :
    f (normalize xs) = f xs := by
  have hprime : AllPrime (normalize xs) := by
    intro p hp
    have hm : p ∈ (xs : Multiset ℕ) := by
      have hfrom : p ∈ (normalize xs : Multiset ℕ) := by
        simpa using hp
      simpa [normalize_multiset xs] using hfrom
    exact hxs p (by simpa using hm)
  apply h (normalize xs) xs hprime hxs
  exact normalize_preserves_product xs

end LinearInputPrimeFactorGeneralF0
