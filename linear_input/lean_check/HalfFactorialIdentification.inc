/-!
# Half-factorial lengths and one probe for *all generator words* in <4,6,9>

The three legal generators are genuine irreducibles of the actual
commutative cancellative submonoid G of natural multiplication.
Represent a generator factor multiset by its multiplicities r,s,t.

Evaluation: 4^r * 6^s * 9^t.
Exponent signature: (2*r+s, s+2*t).
Length: r+s+t.
Observable extra probe: s = number of factors equal to 6.

Equal products imply equal signatures by the existing Mathlib
factorization function at primes 2 and 3. Therefore all generator
factorizations of a fixed element have equal length; the original
product plus one s-probe identifies the full generator factorization.

This statement concerns ALL generator words, not merely the two
factorizations of 36. A separate theorem that every atom of G
is one of these generators is needed to promote it to every
possible irreducible-word representation in G.
-/

noncomputable section

namespace LinearInputHalfFactorial

open LinearInputGeneratedNonUnique

structure Counts where
  c4 : ℕ
  c6 : ℕ
  c9 : ℕ
deriving DecidableEq, Repr

def value (w : Counts) : ℕ :=
  (4 : ℕ) ^ w.c4 * 6 ^ w.c6 * 9 ^ w.c9

def signature (w : Counts) : ℕ × ℕ :=
  (2 * w.c4 + w.c6, w.c6 + 2 * w.c9)

def length (w : Counts) : ℕ := w.c4 + w.c6 + w.c9

def countSix (w : Counts) : ℕ := w.c6

/-- The actual multiplication in G, not a free syntactic algebra. -/
def valueInG (w : Counts) : G :=
  four ^ w.c4 * six ^ w.c6 * nine ^ w.c9

theorem valueInG_val (w : Counts) :
    (valueInG w).val = value w := by
  rfl

theorem value_as_prime_powers (w : Counts) :
    value w = (2 : ℕ) ^ (2 * w.c4 + w.c6) *
      3 ^ (w.c6 + 2 * w.c9) := by
  unfold value
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
      show (6 : ℕ) = 2 * 3 by norm_num,
      show (9 : ℕ) = 3 ^ 2 by norm_num]
  rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [pow_add, pow_add]
  ring

/-- Independent prime multiplicities detect the two exponent coordinates. -/
theorem factorization_two (a b : ℕ) :
    ((2 : ℕ) ^ a * 3 ^ b).factorization 2 = a := by
  rw [Nat.factorization_mul (by positivity) (by positivity)]
  rw [(show Nat.Prime 2 by norm_num).factorization_pow,
      (show Nat.Prime 3 by norm_num).factorization_pow]
  simp

theorem factorization_three (a b : ℕ) :
    ((2 : ℕ) ^ a * 3 ^ b).factorization 3 = b := by
  rw [Nat.factorization_mul (by positivity) (by positivity)]
  rw [(show Nat.Prime 2 by norm_num).factorization_pow,
      (show Nat.Prime 3 by norm_num).factorization_pow]
  simp

theorem value_factorization_two (w : Counts) :
    (value w).factorization 2 = (signature w).1 := by
  rw [value_as_prime_powers]
  exact factorization_two _ _

theorem value_factorization_three (w : Counts) :
    (value w).factorization 3 = (signature w).2 := by
  rw [value_as_prime_powers]
  exact factorization_three _ _

/-- These are actual exponent identities extracted from equal products. -/
theorem same_value_same_signature (u v : Counts)
    (h : value u = value v) : signature u = signature v := by
  apply Prod.ext
  · have h2 := congrArg (fun n : ℕ => n.factorization 2) h
    simpa only [value_factorization_two] using h2
  · have h3 := congrArg (fun n : ℕ => n.factorization 3) h
    simpa only [value_factorization_three] using h3

/-- Half-factorial property for every generator decomposition. -/
theorem same_value_same_length (u v : Counts)
    (h : value u = value v) : length u = length v := by
  have hs := same_value_same_signature u v h
  have h2 := congrArg Prod.fst hs
  have h3 := congrArg Prod.snd hs
  dsimp [signature, length] at *
  omega

/-- Adding only the count of 6 factors identifies every generator word. -/
theorem value_and_six_injective :
    Function.Injective (fun w : Counts => (value w, countSix w)) := by
  intro u v h
  have he : value u = value v := congrArg Prod.fst h
  have h6 : countSix u = countSix v := congrArg Prod.snd h
  have hs := same_value_same_signature u v he
  have h2 := congrArg Prod.fst hs
  have h3 := congrArg Prod.snd hs
  cases u with
  | mk a b c =>
    cases v with
    | mk d e f =>
      simp only [signature, countSix] at h2 h3 h6
      have heq : a = d ∧ b = e ∧ c = f := by omega
      rcases heq with ⟨rfl, rfl, rfl⟩
      rfl

/-- The same theorem concerns the *actual* submonoid G. -/
theorem actual_G_value_and_six_injective :
    Function.Injective (fun w : Counts => (valueInG w, countSix w)) := by
  intro u v he
  apply value_and_six_injective
  apply Prod.ext
  · have hG : valueInG u = valueInG v := congrArg Prod.fst he
    have hv := congrArg Subtype.val hG
    simpa only [valueInG_val] using hv
  · exact congrArg Prod.snd he

theorem actual_G_same_length (u v : Counts)
    (h : valueInG u = valueInG v) : length u = length v := by
  apply same_value_same_length
  have hv := congrArg Subtype.val h
  simpa only [valueInG_val] using hv

def word49 : Counts := ⟨1, 0, 1⟩
def word66 : Counts := ⟨0, 2, 0⟩

theorem collision_example :
    value word49 = value word66 ∧ word49 ≠ word66 ∧
      length word49 = length word66 ∧
      countSix word49 ≠ countSix word66 := by
  norm_num [value, word49, word66, length, countSix]

/-- Zero extra probes fail; one fixed permitted count probe succeeds,
even on the entire infinite class of generator words. -/
theorem one_probe_necessary_and_sufficient :
    ¬ Function.Injective value ∧
      Function.Injective (fun w : Counts => (value w, countSix w)) := by
  constructor
  · intro h
    exact collision_example.2.1 (h collision_example.1)
  · exact value_and_six_injective

/-- Every element of the concrete generated submonoid has a
generator-multiplicity representation. -/
theorem every_element_has_generator_counts (x : G) :
    ∃ w : Counts, valueInG w = x := by
  have hx : ∃ w : Counts, value w = x.val := by
    refine Submonoid.closure_induction (s := generatorSet)
      (motive := fun n _ => ∃ w : Counts, value w = n) ?_ ?_ ?_ x.property
    · intro n hn
      simp only [generatorSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with hn | hn | hn
      · subst n
        exact ⟨⟨1, 0, 0⟩, by norm_num [value]⟩
      · subst n
        exact ⟨⟨0, 1, 0⟩, by norm_num [value]⟩
      · subst n
        exact ⟨⟨0, 0, 1⟩, by norm_num [value]⟩
    · exact ⟨⟨0, 0, 0⟩, by norm_num [value]⟩
    · intro a b ha hb hA hB
      obtain ⟨u, hu⟩ := hA
      obtain ⟨v, hv⟩ := hB
      refine ⟨⟨u.c4 + v.c4, u.c6 + v.c6, u.c9 + v.c9⟩, ?_⟩
      calc
        value ⟨u.c4 + v.c4, u.c6 + v.c6, u.c9 + v.c9⟩ =
          value u * value v := by
            simp [value, pow_add]
            ring
        _ = a * b := by rw [hu, hv]
  obtain ⟨w, hw⟩ := hx
  refine ⟨w, ?_⟩
  apply Subtype.ext
  simpa only [valueInG_val] using hw

end LinearInputHalfFactorial
