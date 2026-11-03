/-!
# Actual multiplicative factor-splitting rewrite and terminal identification

A step replaces one composite factor a*b by two factors a,b >= 2.
The operation never introduces 0 or 1 when starting from an admissible
word, and it preserves the final product. A terminal admissible word
contains only primes. Such terminal factor multisets are uniquely
identified by their product, so no extra observation is needed.

The theorem on counted split paths distinguishes the number of actual
binary splits from the number of kinds of operations or observations.
Existence of a splitting route to a prime word is not claimed here.
-/

noncomputable section

namespace LinearInputPrimeSplitNormalForm

open LinearInputDecompositionIdentification
open LinearInputPrimeFactorIdentification

/-- One binary factor split: a*b is replaced by a and b, both nonunits. -/
def SplitStep (s t : Multiset ℕ) : Prop :=
  ∃ a b : ℕ, ∃ rest : Multiset ℕ,
    2 ≤ a ∧ 2 ≤ b ∧
    s = (a * b) ::ₘ rest ∧
    t = a ::ₘ b ::ₘ rest

/-- The sole operation is ordinary multiplication in the opposite direction. -/
theorem split_preserves_product {s t : Multiset ℕ}
    (h : SplitStep s t) : s.prod = t.prod := by
  obtain ⟨a, b, rest, _, _, hs, ht⟩ := h
  rw [hs, ht]
  simp only [Multiset.prod_cons]
  ring

/-- Each binary split adds exactly one more factor. -/
theorem split_increases_count {s t : Multiset ℕ}
    (h : SplitStep s t) : s.card + 1 = t.card := by
  obtain ⟨a, b, rest, _, _, hs, ht⟩ := h
  rw [hs, ht]
  simp only [Multiset.card_cons]
  omega

/-- An integer-valued ranking potential on factor words. -/
def splitRank (s : Multiset ℕ) : ℕ :=
  (s.map (fun x => x - 1)).sum

/-- Strict descent:
(a*b-1) - ((a-1)+(b-1)) = (a-1)*(b-1) >= 1 for a,b >= 2. -/
theorem split_rank_decreases {s t : Multiset ℕ}
    (h : SplitStep s t) : splitRank t < splitRank s := by
  obtain ⟨a, b, rest, ha, hb, hs, ht⟩ := h
  rw [hs, ht]
  simp only [splitRank, Multiset.map_cons, Multiset.sum_cons]
  have ha1 : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
  have hb1 : b - 1 + 1 = b := Nat.sub_add_cancel (by omega)
  have hprod : a * b =
      (a - 1) * (b - 1) + (a - 1) + (b - 1) + 1 := by
    calc
      a * b = ((a - 1) + 1) * ((b - 1) + 1) := by rw [ha1, hb1]
      _ = (a - 1) * (b - 1) + (a - 1) + (b - 1) + 1 := by ring
  have hpositive : 0 < (a - 1) * (b - 1) :=
    Nat.mul_pos (by omega) (by omega)
  omega

/-- Splitting cannot continue indefinitely, including when the input
contains unmodified zeros or ones. This is a termination statement only. -/
theorem split_terminates_raw (s : Multiset ℕ) :
    ∃ t, Steps SplitStep s t ∧ Terminal SplitStep t :=
  terminating_normal_form SplitStep splitRank
    (fun h => split_rank_decreases h) s

/-- A word is admissible when all factors are nonunits >= 2. -/
def Admissible (s : Multiset ℕ) : Prop := ∀ a ∈ s, 2 ≤ a

/-- Splitting an admissible word produces another admissible word. -/
theorem split_preserves_admissible {s t : Multiset ℕ}
    (h : SplitStep s t) (hsGood : Admissible s) :
    Admissible t := by
  obtain ⟨a, b, rest, ha, hb, hs, ht⟩ := h
  intro x hx
  rw [ht] at hx
  simp only [Multiset.mem_cons] at hx
  rcases hx with hxa | hxb | hrest
  · subst x
    exact ha
  · subst x
    exact hb
  · apply hsGood x
    rw [hs]
    simp [hrest]

/-- For admissible inputs, being a terminal factor word is equivalent
to every remaining factor being prime. -/
theorem split_terminal_iff_all_prime {s : Multiset ℕ}
    (hs : Admissible s) :
    Terminal SplitStep s ↔ (∀ p ∈ s, Nat.Prime p) := by
  constructor
  · intro hterm p hp
    by_contra hnp
    have hp2 := hs p hp
    obtain ⟨a, b, halt, hblt, hab⟩ :=
      (Nat.not_prime_iff_exists_mul_eq hp2).mp hnp
    have ha : 2 ≤ a := by
      by_contra h
      have hsmall : a = 0 ∨ a = 1 := by omega
      rcases hsmall with hzero | hone
      · rw [hzero] at hab
        simp at hab
        omega
      · rw [hone] at hab
        simp at hab
        omega
    have hb : 2 ≤ b := by
      by_contra h
      have hsmall : b = 0 ∨ b = 1 := by omega
      rcases hsmall with hzero | hone
      · rw [hzero] at hab
        simp at hab
        omega
      · rw [hone] at hab
        simp at hab
        omega
    obtain ⟨rest, hsrest⟩ := Multiset.exists_cons_of_mem hp
    have hword : s = (a * b) ::ₘ rest := by
      calc
        s = p ::ₘ rest := hsrest
        _ = (a * b) ::ₘ rest := by rw [hab]
    have hstep : SplitStep s (a ::ₘ b ::ₘ rest) :=
      ⟨a, b, rest, ha, hb, hword, rfl⟩
    exact hterm _ hstep
  · intro hp t hstep
    obtain ⟨a, b, rest, ha, hb, hsrest, _⟩ := hstep
    have hpa : Nat.Prime (a * b) := hp (a * b) (by
      rw [hsrest]
      simp)
    rcases (Nat.prime_mul_iff.mp hpa) with ⟨_, heq⟩ | ⟨_, heq⟩
    · omega
    · omega

/-- Length-indexed splitting derivation; independent from probe cost. -/
def SplitChain : ℕ → Multiset ℕ → Multiset ℕ → Prop
  | 0, s, t => s = t
  | n + 1, s, t => ∃ u, SplitStep s u ∧ SplitChain n u t

/-- Splitting k times increases the factor count by precisely k. -/
theorem split_chain_count {k : ℕ} {s t : Multiset ℕ}
    (h : SplitChain k s t) : t.card = s.card + k := by
  induction k generalizing s with
  | zero =>
      change s = t at h
      subst t
      omega
  | succ k ih =>
      obtain ⟨u, hsu, hut⟩ := h
      have hc := split_increases_count hsu
      have hrest := ih hut
      omega

/-- Count of splits starting from a single composite factor. -/
theorem singleton_split_chain_count (n k : ℕ) {t : Multiset ℕ}
    (h : SplitChain k ({n} : Multiset ℕ) t) :
    t.card = k + 1 := by
  have hc := split_chain_count h
  simpa [Nat.add_comm] using hc

/-- The accepted domain excludes 0 and 1, including at intermediate steps. -/
abbrev FactorWord := {s : Multiset ℕ // Admissible s}

def FactorSplit (s t : FactorWord) : Prop := SplitStep s.val t.val

def factorWordValue (s : FactorWord) : ℕ := s.val.prod

theorem admissible_terminal_iff_prime (s : FactorWord) :
    Terminal FactorSplit s ↔ ∀ p ∈ s.val, Nat.Prime p := by
  constructor
  · intro hterm
    apply (split_terminal_iff_all_prime s.property).1
    intro t hstep
    have ht : Admissible t := split_preserves_admissible hstep s.property
    exact hterm ⟨t, ht⟩ hstep
  · intro hp t hstep
    exact ((split_terminal_iff_all_prime s.property).2 hp) t.val hstep

/-- The generic decreasing-rank theorem applies to the actual
multiplicative factor splitting relation on admissible words. -/
theorem admissible_split_terminates (s : FactorWord) :
    ∃ t, Steps FactorSplit s t ∧ Terminal FactorSplit t :=
  terminating_normal_form FactorSplit (fun x => splitRank x.val)
    (fun h => split_rank_decreases h) s

/-- Every admissible factor word has some finite splitting route
to a word containing only prime atoms. -/
theorem reachable_prime_normal_form (s : FactorWord) :
    ∃ t, Steps FactorSplit s t ∧
      (∀ p ∈ t.val, Nat.Prime p) := by
  obtain ⟨t, hpath, hterm⟩ := admissible_split_terminates s
  exact ⟨t, hpath, (admissible_terminal_iff_prime t).1 hterm⟩

theorem factor_split_preserves_value (s t : FactorWord)
    (h : FactorSplit s t) : factorWordValue s = factorWordValue t :=
  split_preserves_product h

/-- On the genuine splitting rewrite, evaluation is injective on terminal
normal forms, even though it is not injective on all composite words. -/
theorem terminal_factor_word_value_injective :
    TerminalValueInjective FactorSplit factorWordValue := by
  intro s t hs ht he
  have hps := (admissible_terminal_iff_prime s).1 hs
  have hpt := (admissible_terminal_iff_prime t).1 ht
  apply Subtype.ext
  exact natural_prime_multiset_injective s.val t.val hps hpt he

/-- Two terminal words from a common start have the same primes, with
multiplicities, independently of the chosen factor-splitting route. -/
theorem terminal_factor_words_unique {x s t : FactorWord}
    (hs : Steps FactorSplit x s) (ht : Steps FactorSplit x t)
    (hsTerm : Terminal FactorSplit s) (htTerm : Terminal FactorSplit t) :
    s = t := by
  exact normal_forms_unique_of_value FactorSplit factorWordValue
    factor_split_preserves_value terminal_factor_word_value_injective
    hs ht hsTerm htTerm

/-- The result of the generic minimum-probe predicate: zero additional
measurements suffice for terminal prime-only words. -/
theorem terminal_words_zero_extra_probes :
    IdentifiesWith FactorSplit factorWordValue
      (fun (_ : Fin 0) (_ : FactorWord) => PUnit.unit) ∅ := by
  exact (zero_extra_probes_iff FactorSplit factorWordValue
    (fun (_ : Fin 0) (_ : FactorWord) => PUnit.unit)).2
      terminal_factor_word_value_injective

end LinearInputPrimeSplitNormalForm
