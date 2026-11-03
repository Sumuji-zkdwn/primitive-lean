/-!
General finite-length observation model for prime factors 2, 3, 5.

For every n : Nat, a state is a length-(n+1) ordered sequence
represented as (n explicitly accessible factors, one final factor).
The probe library consists of its full product and each of the n
individual *nonfinal* factors. Therefore there are n+1 probes.

The exact non-adaptive observation-call minimum is n+1, with no bound
on internal cost of computing a probe. Repetitions are allowed in a
list of calls. This extends the three-factor result of PR #51 for
preselected probes, not the adaptive result of PR #52.

The number of unordered length-m prime-code multisets is choose (m+2) 2
by the mathlib symmetric-power cardinality theorem. We do not claim
to construct an arbitrary-length sorting map in this module.
-/

namespace LinearInputPrimeFactorFiniteLength

open LinearInputPrimeFactorObservation

abbrev Prefix (n : ℕ) := Fin n → Fin 3
abbrev Word (n : ℕ) := Prefix n × Fin 3
abbrev Probe (n : ℕ) := Option (Fin n)

/-- Product of the first n factors. -/
def prefixProduct (n : ℕ) (f : Prefix n) : ℕ :=
  ∏ i : Fin n, primeOf (f i)

/-- The full product of all n+1 factors. -/
def product (n : ℕ) (x : Word n) : ℕ :=
  prefixProduct n x.1 * primeOf x.2

/-- None = product, Some i = read factor i; no direct final-factor probe. -/
def probe (n : ℕ) : Probe n → Word n → ℕ
  | none, x => product n x
  | some i, x => primeOf (x.1 i)

/-- A set of probes separates states iff their joint observation is injective. -/
def Separates (n : ℕ) (s : Finset (Probe n)) : Prop :=
  ∀ x y : Word n, (∀ q ∈ s, probe n q x = probe n q y) → x = y

/-- Distinct prime codes have distinct values. -/
theorem primeOf_injective : Function.Injective primeOf := by decide

theorem prefix_product_pos (n : ℕ) (f : Prefix n) :
    0 < prefixProduct n f := by
  unfold prefixProduct
  apply Finset.prod_pos
  intro i hi
  exact (primeOf_is_prime (f i)).pos

/-- All n+1 permitted probes separate every ordered length-(n+1) word. -/
theorem full_library_separates (n : ℕ) :
    Separates n (Finset.univ : Finset (Probe n)) := by
  intro x y heq
  have hp : x.1 = y.1 := by
    funext i
    apply primeOf_injective
    exact heq (some i) (Finset.mem_univ _)
  have hprod : prefixProduct n x.1 * primeOf x.2 =
      prefixProduct n y.1 * primeOf y.2 :=
    heq none (Finset.mem_univ _)
  rw [← hp] at hprod
  have hlastval : primeOf x.2 = primeOf y.2 :=
    mul_left_cancel₀ (Nat.ne_of_gt (prefix_product_pos n x.1)) hprod
  exact Prod.ext hp (primeOf_injective hlastval)

/-- Every omitted probe has a specific counterexample pair. -/
def zeroPrefix (n : ℕ) : Prefix n := fun _ => 0

def bumpPrefix {n : ℕ} (i : Fin n) : Prefix n :=
  fun j => if j = i then 1 else 0

def others (n : ℕ) (i : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).erase i

/-- Swapping a 2 at position i with the final 3 preserves the product. -/
theorem bumped_prefix_swap_product (n : ℕ) (i : Fin n) :
    prefixProduct n (bumpPrefix i) * 2 =
      prefixProduct n (zeroPrefix n) * 3 := by
  classical
  have hzero : prefixProduct n (zeroPrefix n) =
      2 * (others n i).prod (fun _ => (2 : ℕ)) := by
    change (∏ _j : Fin n, (2 : ℕ)) =
      2 * (others n i).prod (fun _ => (2 : ℕ))
    simpa [others] using
      (Finset.mul_prod_erase
        (Finset.univ : Finset (Fin n))
        (fun _j : Fin n => (2 : ℕ)) (Finset.mem_univ i)).symm
  have hrest :
      (others n i).prod (fun j => if j = i then (3 : ℕ) else 2) =
        (others n i).prod (fun _ => (2 : ℕ)) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hji]
  have hbump : prefixProduct n (bumpPrefix i) =
      3 * (others n i).prod (fun _ => (2 : ℕ)) := by
    calc
      prefixProduct n (bumpPrefix i) =
          ∏ j : Fin n, if j = i then (3 : ℕ) else 2 := by
        unfold prefixProduct
        apply Finset.prod_congr rfl
        intro j hj
        by_cases hji : j = i <;> simp [bumpPrefix, primeOf, hji]
      _ = (if i = i then (3 : ℕ) else 2) *
          (others n i).prod (fun j => if j = i then (3 : ℕ) else 2) := by
        simpa [others] using
          (Finset.mul_prod_erase
            (Finset.univ : Finset (Fin n))
            (fun j : Fin n => if j = i then (3 : ℕ) else 2)
            (Finset.mem_univ i)).symm
      _ = 3 * (others n i).prod (fun _ => (2 : ℕ)) := by
        simpa [hrest]
  rw [hzero, hbump]
  ring

/-- Each permitted operation is indispensable: any omitted operation
leaves two different states that every other operation identifies. -/
theorem missing_probe_witness (n : ℕ) (q : Probe n) :
    ∃ x y : Word n, x ≠ y ∧
      ∀ r : Probe n, r ≠ q → probe n r x = probe n r y := by
  cases q with
  | none =>
      refine ⟨(zeroPrefix n, 0), (zeroPrefix n, 1), ?_, ?_⟩
      · intro he
        have hlast : (0 : Fin 3) = 1 := congrArg Prod.snd he
        exact (by decide : (0 : Fin 3) ≠ 1) hlast
      · intro r hr
        cases r with
        | none => exact False.elim (hr rfl)
        | some i => rfl
  | some i =>
      refine ⟨(zeroPrefix n, 1), (bumpPrefix i, 0), ?_, ?_⟩
      · intro he
        have hlast : (1 : Fin 3) = 0 := congrArg Prod.snd he
        exact (by decide : (1 : Fin 3) ≠ 0) hlast
      · intro r hr
        cases r with
        | none =>
            simpa [probe, product, primeOf] using
              (bumped_prefix_swap_product n i).symm
        | some j =>
            have hji : j ≠ i := by
              intro h
              subst j
              exact hr rfl
            simp [probe, zeroPrefix, bumpPrefix, hji, primeOf]

/-- If a set of probes identifies all states, every permitted probe
must actually belong to that set. -/
theorem needed_probe_of_separates (n : ℕ) (s : Finset (Probe n))
    (hs : Separates n s) (q : Probe n) : q ∈ s := by
  by_contra hn
  obtain ⟨x, y, hne, heq⟩ := missing_probe_witness n q
  apply hne
  apply hs x y
  intro r hr
  apply heq r
  intro h
  subst r
  exact hn hr

/-- The full library is the unique separating subset. -/
theorem separates_iff_univ (n : ℕ) (s : Finset (Probe n)) :
    Separates n s ↔ s = Finset.univ := by
  constructor
  · intro hs
    ext q
    simp only [Finset.mem_univ, iff_true]
    exact needed_probe_of_separates n s hs q
  · intro hs
    subst s
    exact full_library_separates n

/-- There are exactly n+1 available operations. -/
theorem probe_library_card (n : ℕ) :
    Fintype.card (Probe n) = n + 1 := by
  simp [Probe]

/-- Exact minimum number of distinct probes at arbitrary positive length:
if a set identifies every state, it contains all n+1 available probes. -/
theorem minimal_distinct_probe_count (n : ℕ) :
    (∃ s : Finset (Probe n), s.card = n + 1 ∧ Separates n s) ∧
    (∀ s : Finset (Probe n), s.card < n + 1 → ¬ Separates n s) := by
  constructor
  · refine ⟨Finset.univ, ?_, full_library_separates n⟩
    simpa using probe_library_card n
  · intro s hshort hs
    have hfull := (separates_iff_univ n s).mp hs
    subst s
    have hcard := probe_library_card n
    simp only [Finset.card_univ] at hshort
    omega

/-- Repeating a probe in a list cannot reduce the number of calls. -/
theorem separating_list_length_lower_bound (n : ℕ)
    (calls : List (Probe n))
    (h : Separates n calls.toFinset) : n + 1 ≤ calls.length := by
  have hall := (separates_iff_univ n calls.toFinset).mp h
  have hcard : calls.toFinset.card = n + 1 := by
    rw [hall]
    simpa using probe_library_card n
  calc
    n + 1 = calls.toFinset.card := hcard.symm
    _ ≤ calls.length := List.toFinset_card_le calls

/-- An explicit complete list: product, then each accessible factor. -/
def completeCalls (n : ℕ) : List (Probe n) :=
  none :: (List.finRange n).map some

theorem complete_calls_length (n : ℕ) :
    (completeCalls n).length = n + 1 := by
  simp [completeCalls]

theorem complete_calls_cover (n : ℕ) :
    (completeCalls n).toFinset = Finset.univ := by
  ext q
  cases q with
  | none => simp [completeCalls]
  | some i => simp [completeCalls]

/-- The exact non-adaptive minimum remains n+1 when calls may repeat. -/
theorem minimal_list_observation_count (n : ℕ) :
    (∃ calls : List (Probe n), calls.length = n + 1 ∧
      Separates n calls.toFinset) ∧
    (∀ calls : List (Probe n), calls.length < n + 1 →
      ¬ Separates n calls.toFinset) := by
  constructor
  · refine ⟨completeCalls n, complete_calls_length n, ?_⟩
    rw [complete_calls_cover]
    exact full_library_separates n
  · intro calls hshort hsep
    have hlower := separating_list_length_lower_bound n calls hsep
    omega

/-- Stars-and-bars: the unordered factor multisets of length m on the
three-element prime alphabet have (m+2).choose 2 possible states. -/
theorem unordered_factor_multiset_count (m : ℕ) :
    Fintype.card (Sym (Fin 3) m) = (m + 2).choose 2 := by
  calc
    Fintype.card (Sym (Fin 3) m) = (3 : ℕ).multichoose m := by
      exact Sym.card_sym_fin_eq_multichoose 3 m
    _ = (m + 2).choose m := by
      rw [Nat.multichoose_eq]
      congr 1
      omega
    _ = (m + 2).choose 2 := by
      simpa [Nat.add_comm] using
        (Nat.choose_symm_add (a := m) (b := 2))

end LinearInputPrimeFactorFiniteLength
