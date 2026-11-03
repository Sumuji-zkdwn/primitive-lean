/-!
# Genuine half-factoriality for ALL atomic words in the actual monoid <4,6,9>

The previous generator-count theorem is strengthened here using the
classification of every actual atom: each is 4, 6, or 9.
Each atom has total valuation v_2 + v_3 = 2.
By multiplicativity of Nat.factorization, every finite atomic word w
satisfies v_2(prod(w)) + v_3(prod(w)) = 2 * card(w).

Thus ALL irreducible decompositions of the same element have the same
length, without an assumption that the word was originally written
using the generator-count record.
-/

noncomputable section

namespace LinearInputAtomicHalfFactorial

open LinearInputGeneratedNonUnique
open LinearInputHalfFactorial
open LinearInputAtomicGeneratorClassification

/-- Every genuine relative atom carries total (2,3)-prime weight 2. -/
theorem atomic_weight_two (a : G) (ha : Atomic a) :
    a.val.factorization 2 + a.val.factorization 3 = 2 := by
  rcases atom_is_generator a ha with h4 | h6 | h9
  · subst a
    have h₂ : (four.val).factorization 2 = 2 := by
      simpa [four, value, signature] using
        (value_factorization_two (⟨1, 0, 0⟩ : Counts))
    have h₃ : (four.val).factorization 3 = 0 := by
      simpa [four, value, signature] using
        (value_factorization_three (⟨1, 0, 0⟩ : Counts))
    omega
  · subst a
    have h₂ : (six.val).factorization 2 = 1 := by
      simpa [six, value, signature] using
        (value_factorization_two (⟨0, 1, 0⟩ : Counts))
    have h₃ : (six.val).factorization 3 = 1 := by
      simpa [six, value, signature] using
        (value_factorization_three (⟨0, 1, 0⟩ : Counts))
    omega
  · subst a
    have h₂ : (nine.val).factorization 2 = 0 := by
      simpa [nine, value, signature] using
        (value_factorization_two (⟨0, 0, 1⟩ : Counts))
    have h₃ : (nine.val).factorization 3 = 2 := by
      simpa [nine, value, signature] using
        (value_factorization_three (⟨0, 0, 1⟩ : Counts))
    omega

/-- A multiset of genuine relative atoms has a total valuation which
equals twice the number of factors. -/
theorem atomic_multiset_weight (w : Multiset G) :
    (∀ a ∈ w, Atomic a) →
      (w.prod.val).factorization 2 +
      (w.prod.val).factorization 3 = 2 * w.card := by
  classical
  induction w using Multiset.induction_on with
  | empty =>
      intro _
      simp
  | @cons a rest ih =>
      intro hw
      have ha : Atomic a := hw a (by simp)
      have hrest : ∀ x ∈ rest, Atomic x := by
        intro x hx
        exact hw x (by simp [hx])
      have hrec := ih hrest
      have hatom := atomic_weight_two a ha
      have ha0 : a.val ≠ 0 := Nat.ne_of_gt (member_positive a)
      have hr0 : rest.prod.val ≠ 0 :=
        Nat.ne_of_gt (member_positive rest.prod)
      have hmul (p : ℕ) :
          ((a * rest.prod).val).factorization p =
            a.val.factorization p + rest.prod.val.factorization p := by
        change (a.val * rest.prod.val).factorization p =
          a.val.factorization p + rest.prod.val.factorization p
        rw [Nat.factorization_mul ha0 hr0]
        rfl
      simp only [Multiset.prod_cons, Multiset.card_cons]
      rw [hmul 2, hmul 3]
      omega

/-- Half-factoriality on ALL atomic multisets in the actual
cancellative commutative monoid, not just generator-labeled triples. -/
theorem all_atomic_factorizations_same_length
    (u v : Multiset G)
    (hu : ∀ a ∈ u, Atomic a)
    (hv : ∀ a ∈ v, Atomic a)
    (heval : u.prod = v.prod) :
    u.card = v.card := by
  have hwu := atomic_multiset_weight u hu
  have hwv := atomic_multiset_weight v hv
  have hv := congrArg Subtype.val heval
  have h2 := congrArg (fun n : ℕ => n.factorization 2) hv
  have h3 := congrArg (fun n : ℕ => n.factorization 3) hv
  omega

end LinearInputAtomicHalfFactorial
