/-!
# Radical forgetting: a concrete arithmetic F0 and its dynamics

The radical discards *multiplicities* of prime factors, unlike the
prime-list sorting F0 (which discards only order).  Zero is kept at zero,
so the map is a well-defined natural-number retraction.

This is a specialization of the existing LinearInputF0 and
LinearInputF0Descent / LinearInputF0FutureMinimality machinery.
No abc inequality, factorization complexity bound, or nontrivial
Diophantine finiteness theorem is asserted.
-/

namespace LinearInputRadicalF0

/-- Product of the distinct prime factors, with the conventional zero case. -/
def radical (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, p

/-- Away from zero, radical is the product of the prime-support finset. -/
theorem radical_eq_product (n : ℕ) (hn : n ≠ 0) :
    radical n = ∏ p ∈ n.primeFactors, p := by
  simp [radical, hn]

theorem radical_zero : radical 0 = 0 := by
  simp [radical]

theorem radical_ne_zero {n : ℕ} (hn : n ≠ 0) :
    radical n ≠ 0 := by
  rw [radical_eq_product n hn]
  have hp : 0 < ∏ p ∈ n.primeFactors, p := by
    apply Finset.prod_pos
    intro p hp
    exact Nat.pos_of_mem_primeFactors hp
  exact Nat.ne_of_gt hp

theorem radical_eq_zero_iff (n : ℕ) :
    radical n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    exact radical_ne_zero hn h
  · rintro rfl
    exact radical_zero

/-- The full prime-support observation is invariant under radical. -/
theorem radical_primeFactors (n : ℕ) :
    (radical n).primeFactors = n.primeFactors := by
  by_cases hn : n = 0
  · subst n
    simp [radical]
  · rw [radical_eq_product n hn]
    exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)

/-- This is a genuine instance of the repository's F0 idempotence. -/
theorem radical_idempotent : LinearInputF0.Idempotent radical := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [radical]
  · have hrad : radical n ≠ 0 := radical_ne_zero hn
    calc
      radical (radical n) = ∏ p ∈ (radical n).primeFactors, p :=
        radical_eq_product (radical n) hrad
      _ = ∏ p ∈ n.primeFactors, p := by rw [radical_primeFactors]
      _ = radical n := (radical_eq_product n hn).symm

/-- Equality under forgetting means equality of prime support on positives. -/
theorem radical_kernel_iff (x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) :
    radical x = radical y ↔ x.primeFactors = y.primeFactors := by
  constructor
  · intro h
    calc
      x.primeFactors = (radical x).primeFactors := (radical_primeFactors x).symm
      _ = (radical y).primeFactors := congrArg Nat.primeFactors h
      _ = y.primeFactors := radical_primeFactors y
  · intro h
    calc
      radical x = ∏ p ∈ x.primeFactors, p := radical_eq_product x hx
      _ = ∏ p ∈ y.primeFactors, p := by rw [h]
      _ = radical y := (radical_eq_product y hy).symm

/-- A positive squarefree integer is a fixed representative of radical. -/
theorem squarefree_fixed (n : ℕ) (hn : n ≠ 0) (hs : Squarefree n) :
    radical n = n := by
  rw [radical_eq_product n hn]
  exact Nat.prod_primeFactors_of_squarefree hs

/-- On a prime, the radical is unchanged. -/
theorem radical_of_prime (p : ℕ) (hp : Nat.Prime p) :
    radical p = p := by
  rw [radical_eq_product p hp.ne_zero, hp.primeFactors]
  simp

/-- Explicitly identify the prime support of four as a singleton. -/
theorem primeFactors_four :
    (4 : ℕ).primeFactors = ({2} : Finset ℕ) := by
  have hp : Nat.Prime 2 := by decide
  calc
    (4 : ℕ).primeFactors = (2 * 2 : ℕ).primeFactors := by norm_num
    _ = (2 : ℕ).primeFactors ∪ (2 : ℕ).primeFactors :=
      Nat.primeFactors_mul (by norm_num) (by norm_num)
    _ = ({2} : Finset ℕ) := by simp [hp.primeFactors]

theorem radical_four : radical 4 = 2 := by
  rw [radical_eq_product 4 (by norm_num), primeFactors_four]
  simp

/-- Forgetting identifies the same support despite different exponents. -/
theorem two_four_same_radical : radical 2 = radical 4 := by
  calc
    radical 2 = 2 := radical_of_prime 2 (by decide)
    _ = radical 4 := radical_four.symm

/-- One successor step distinguishes the previously identified states. -/
theorem successors_distinguished :
    radical (Nat.succ 2) ≠ radical (Nat.succ 4) := by
  change radical 3 ≠ radical 5
  rw [radical_of_prime 3 (by decide), radical_of_prime 5 (by decide)]
  norm_num

/-- The successor operation does not respect radical's observational fibers. -/
theorem successor_not_fiber_respecting :
    ¬ LinearInputF0Descent.RespectsFibers radical Nat.succ := by
  intro h
  exact successors_distinguished (h 2 4 two_four_same_radical)

/-- Reuse the existing F0 iff: adding one does *not* descend through radical. -/
theorem successor_not_descending :
    ¬ LinearInputF0Descent.Descends radical Nat.succ := by
  intro h
  apply successor_not_fiber_respecting
  exact (LinearInputF0Descent.descends_iff_respects radical_idempotent).mp h

/-- No deterministic update on radical values alone predicts every successor. -/
theorem no_radical_successor_readout :
    ¬ ∃ g : ℕ → ℕ, ∀ n, radical (Nat.succ n) = g (radical n) := by
  rintro ⟨g, hg⟩
  apply successors_distinguished
  calc
    radical (Nat.succ 2) = g (radical 2) := hg 2
    _ = g (radical 4) := congrArg g two_four_same_radical
    _ = radical (Nat.succ 4) := (hg 4).symm

/-- The two states agree at time zero but not as future observation traces. -/
theorem future_separates_two_four :
    radical 2 = radical 4 ∧
      ¬ LinearInputFutureObservation.FutureEq radical Nat.succ 2 4 := by
  constructor
  · exact two_four_same_radical
  · intro hf
    apply successors_distinguished
    simpa only [Function.iterate_one] using hf 1

/-- Direct specialization of the repository's complete-prediction criterion. -/
theorem radical_not_complete_predictive_state :
    ¬ (∀ x y, LinearInputFutureObservation.FutureEq radical Nat.succ x y ↔
        radical x = radical y) := by
  intro h
  exact successor_not_descending
    ((LinearInputF0FutureMinimality.descends_iff_future_eq radical_idempotent).mpr h)

end LinearInputRadicalF0
