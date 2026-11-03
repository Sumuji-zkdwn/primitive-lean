/-!
Finite prime-factor observation (primes 2, 3, 5; exactly two factors).

This file is appended after FiniteObservationSeparation.inc. The state space
has nine *ordered* pairs. A multiset forgets the factor order; the canonical
subtype represents its six equivalence classes.

Allowed probes are explicitly restricted to the product and the first factor.
Two is the minimum number of probe calls for ordered pairs in that library;
one product observation suffices for the six unordered classes. This does not
assert a general factorization algorithm, observation bound, or time bound.
-/

namespace LinearInputPrimeFactorObservation

open LinearInputFiniteObservation

abbrev OrderedPair := Fin 3 × Fin 3

/-- Index 0, 1, 2 codes the prime 2, 3, 5 respectively. -/
def primeOf (i : Fin 3) : ℕ :=
  if i.val = 0 then 2 else if i.val = 1 then 3 else 5

/-- Ordered two-factor product. -/
def pairProduct (x : OrderedPair) : ℕ :=
  primeOf x.1 * primeOf x.2

/-- Genuine multiset of prime numbers, forgetting only the order. -/
def factorBag (x : OrderedPair) : Multiset ℕ :=
  (([primeOf x.1, primeOf x.2] : List ℕ) : Multiset ℕ)

/-- Ordered factor sequences (2,3) and (3,2) differ. -/
theorem swapped_order_distinct :
    ((0, 1) : OrderedPair) ≠ (1, 0) := by decide

/-- The product observation fails to distinguish their order. -/
theorem swapped_same_product :
    pairProduct (0, 1) = pairProduct (1, 0) := by decide

/-- Their unordered bags agree. -/
theorem swapped_same_bag :
    factorBag (0, 1) = factorBag (1, 0) := by decide

/-- In this nine-state model, equality of products exactly agrees with
    equality of unordered multisets. This is a finite computation, not a
    proof of the fundamental theorem of arithmetic. -/
theorem product_kernel_eq_bag_kernel (x y : OrderedPair) :
    pairProduct x = pairProduct y ↔ factorBag x = factorBag y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

/-- Canonical representatives of unordered pairs. -/
abbrev CanonicalPair := {x : OrderedPair // x.1 ≤ x.2}

def canonicalProduct (x : CanonicalPair) : ℕ := pairProduct x.1

/-- The product alone distinguishes the unordered classes. -/
theorem canonical_product_injective : Function.Injective canonicalProduct := by
  decide

/-- The product alone is not injective on ordered factor sequences. -/
theorem product_not_injective : ¬ Function.Injective pairProduct := by
  intro h
  exact swapped_order_distinct (h swapped_same_product)

/-- The first factor, when exposed as a probe result, is another lossy map. -/
def firstPrime (x : OrderedPair) : ℕ := primeOf x.1

theorem first_not_injective : ¬ Function.Injective firstPrime := by
  intro h
  have hsame : firstPrime (0, 0) = firstPrime (0, 1) := by decide
  have hbad : ((0, 0) : OrderedPair) = (0, 1) := h hsame
  exact (by decide : ((0, 0) : OrderedPair) ≠ (0, 1)) hbad

/-- Reuse PR #36's exact observational-kernel intersection theorem. -/
theorem product_first_kernel (x y : OrderedPair) :
    joint pairProduct firstPrime x = joint pairProduct firstPrime y ↔
      pairProduct x = pairProduct y ∧ firstPrime x = firstPrime y :=
  joint_eq_iff pairProduct firstPrime x y

/-- Product together with the first prime recovers the ordered pair. -/
theorem product_first_joint_injective :
    Function.Injective (joint pairProduct firstPrime) := by
  intro x y h
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all [joint, pairProduct, firstPrime, primeOf]

/-- The permitted finite observation library has exactly two members. -/
def permittedProbe (i : Fin 2) : OrderedPair → ℕ :=
  if i.val = 0 then pairProduct else firstPrime

theorem no_single_probe (i : Fin 2) :
    ¬ Function.Injective (permittedProbe i) := by
  fin_cases i
  · simpa [permittedProbe] using product_not_injective
  · simpa [permittedProbe] using first_not_injective

/-- A finite list of calls, recording every output in order. -/
def selectedObservations (choices : List (Fin 2)) (x : OrderedPair) : List ℕ :=
  choices.map (fun i => permittedProbe i x)

theorem empty_selection_not_injective :
    ¬ Function.Injective (selectedObservations []) := by
  intro h
  have hbad : ((0, 0) : OrderedPair) = (0, 1) :=
    h (by simp [selectedObservations])
  exact (by decide : ((0, 0) : OrderedPair) ≠ (0, 1)) hbad

theorem singleton_selection_not_injective (i : Fin 2) :
    ¬ Function.Injective (selectedObservations [i]) := by
  intro h
  apply no_single_probe i
  intro x y he
  apply h
  simp [selectedObservations, he]

/-- No zero- or one-call selection from this library identifies the state. -/
theorem fewer_than_two_not_injective (choices : List (Fin 2))
    (hshort : choices.length < 2) :
    ¬ Function.Injective (selectedObservations choices) := by
  cases choices with
  | nil => exact empty_selection_not_injective
  | cons i rest =>
      cases rest with
      | nil => exact singleton_selection_not_injective i
      | cons j tail =>
          simp only [List.length_cons] at hshort
          omega

/-- Calling both permitted probes is enough. -/
theorem two_selection_injective :
    Function.Injective (selectedObservations [0, 1]) := by
  intro x y h
  have hpair : pairProduct x = pairProduct y ∧ firstPrime x = firstPrime y := by
    simpa [selectedObservations, permittedProbe] using h
  exact product_first_joint_injective
    ((product_first_kernel x y).2 hpair)

/-- Exact minimum among finite sequences of permitted probe calls: two. -/
theorem minimal_ordered_observation_count :
    (∃ choices : List (Fin 2), choices.length = 2 ∧
      Function.Injective (selectedObservations choices)) ∧
    (∀ choices : List (Fin 2), choices.length < 2 →
      ¬ Function.Injective (selectedObservations choices)) := by
  constructor
  · exact ⟨[0, 1], by decide, two_selection_injective⟩
  · exact fewer_than_two_not_injective

end LinearInputPrimeFactorObservation
