/-!
Orbit kernels of finite prime-factor observations.

This separate module extends the verified two-factor experiment without
changing any prior proofs. The only allowed primes are 2, 3, and 5.

* Two-factor product equality is the orbit relation for swapping positions.
* Three-factor product equality is the orbit relation for the six explicit
  position permutations, and agrees with equality of prime multisets.
* The explicitly restricted triple probe library contains product, first
  factor, and second factor. Exactly three observation calls are needed
  to distinguish all 27 ordered triples.
* The product alone distinguishes all 10 unordered triple classes.

None of these results establishes general unique factorization, the cost of
computing any of these probe outputs, or a lower bound for unrestricted probes.
-/

namespace LinearInputPrimeFactorOrbits

open LinearInputFiniteObservation
open LinearInputPrimeFactorObservation

/-- Swapping the two factor positions realizes the nontrivial S2 action. -/
def swapPair (x : OrderedPair) : OrderedPair := (x.2, x.1)

theorem swap_pair_involutive (x : OrderedPair) :
    swapPair (swapPair x) = x := by
  cases x
  rfl

/-- Product equality is precisely the S2 orbit relation in this finite model. -/
theorem pair_product_eq_iff_swap_orbit (x y : OrderedPair) :
    pairProduct x = pairProduct y ↔ x = y ∨ x = swapPair y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    decide

/-- Equal unordered multisets are precisely the S2 orbits. -/
theorem pair_bag_eq_iff_swap_orbit (x y : OrderedPair) :
    factorBag x = factorBag y ↔ x = y ∨ x = swapPair y :=
  (product_kernel_eq_bag_kernel x y).symm.trans
    (pair_product_eq_iff_swap_orbit x y)

/-- The joint probe from PR #50 refines the S2 orbit kernel. -/
theorem pair_joint_refines_swap_orbit (x y : OrderedPair) :
    joint pairProduct firstPrime x = joint pairProduct firstPrime y ↔
      (x = y ∨ x = swapPair y) ∧ firstPrime x = firstPrime y := by
  rw [product_first_kernel, pair_product_eq_iff_swap_orbit]

/-- A genuinely ordered length-three state. -/
abbrev OrderedTriple := Fin 3 × (Fin 3 × Fin 3)

/-- The multiplication observation on three prime factors. -/
def tripleProduct (x : OrderedTriple) : ℕ :=
  primeOf x.1 * primeOf x.2.1 * primeOf x.2.2

/-- Forget ordering but retain repetitions of primes. -/
def tripleBag (x : OrderedTriple) : Multiset ℕ :=
  (([primeOf x.1, primeOf x.2.1, primeOf x.2.2] : List ℕ) : Multiset ℕ)

/-- Exhaustive enumeration of the six position permutations (the S3 action).
The indices encode abc, acb, bac, cba, bca, cab respectively. -/
def reorderTriple (σ : Fin 6) (x : OrderedTriple) : OrderedTriple :=
  if σ.val = 0 then x
  else if σ.val = 1 then (x.1, (x.2.2, x.2.1))
  else if σ.val = 2 then (x.2.1, (x.1, x.2.2))
  else if σ.val = 3 then (x.2.2, (x.2.1, x.1))
  else if σ.val = 4 then (x.2.1, (x.2.2, x.1))
  else (x.2.2, (x.1, x.2.1))

theorem six_permutations_count : Fintype.card (Fin 6) = 6 := by decide

/-- Each of the six explicit index permutations preserves the product. -/
theorem reorder_preserves_product (σ : Fin 6) (x : OrderedTriple) :
    tripleProduct (reorderTriple σ x) = tripleProduct x := by
  fin_cases σ <;>
    simp [reorderTriple, tripleProduct, mul_comm, mul_left_comm, mul_assoc]

/-- Product equality is exactly the orbit relation under all six
position permutations, in the finite 27-state model. -/
theorem triple_product_eq_iff_orbit (x y : OrderedTriple) :
    tripleProduct x = tripleProduct y ↔
      ∃ σ : Fin 6, x = reorderTriple σ y := by
  rcases x with ⟨a, ⟨b, c⟩⟩
  rcases y with ⟨d, ⟨e, f⟩⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;> decide

/-- This is a finite classification only: product equality equals multiset
equality for triples of 2, 3 and 5. -/
theorem triple_product_eq_iff_bag (x y : OrderedTriple) :
    tripleProduct x = tripleProduct y ↔ tripleBag x = tripleBag y := by
  rcases x with ⟨a, ⟨b, c⟩⟩
  rcases y with ⟨d, ⟨e, f⟩⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;> decide

/-- The multiset kernel and six-permutation orbit coincide. -/
theorem triple_bag_eq_iff_orbit (x y : OrderedTriple) :
    tripleBag x = tripleBag y ↔
      ∃ σ : Fin 6, x = reorderTriple σ y :=
  (triple_product_eq_iff_bag x y).symm.trans
    (triple_product_eq_iff_orbit x y)

theorem triple_state_count : Fintype.card OrderedTriple = 27 := by decide

/-- Nondecreasing triples are canonical representatives for unordered ones. -/
abbrev CanonicalTriple :=
  {x : OrderedTriple // x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2}

def canonicalTripleProduct (x : CanonicalTriple) : ℕ := tripleProduct x.1

theorem canonical_triple_count : Fintype.card CanonicalTriple = 10 := by decide

/-- A single product observation separates all ten unordered states. -/
theorem canonical_triple_product_injective :
    Function.Injective canonicalTripleProduct := by decide

/-- For unordered classes the allowed library consists only of product. -/
def canonicalTripleObservations (choices : List Unit)
    (x : CanonicalTriple) : List ℕ :=
  choices.map (fun _ => canonicalTripleProduct x)

def canonical222 : CanonicalTriple := ⟨(0, (0, 0)), by decide⟩
def canonical333 : CanonicalTriple := ⟨(1, (1, 1)), by decide⟩

theorem canonical_triple_empty_not_injective :
    ¬ Function.Injective (canonicalTripleObservations []) := by
  intro h
  have hbad : canonical222 = canonical333 := h rfl
  exact (by decide : canonical222 ≠ canonical333) hbad

theorem canonical_triple_one_injective :
    Function.Injective (canonicalTripleObservations [()]) := by
  intro x y h
  apply canonical_triple_product_injective
  simpa [canonicalTripleObservations] using h

/-- The restricted unordered-triple observation minimum is one. -/
theorem minimal_unordered_triple_observations :
    (∃ choices : List Unit, choices.length = 1 ∧
      Function.Injective (canonicalTripleObservations choices)) ∧
    (∀ choices : List Unit, choices.length < 1 →
      ¬ Function.Injective (canonicalTripleObservations choices)) := by
  constructor
  · exact ⟨[()], by decide, canonical_triple_one_injective⟩
  · intro choices hshort
    cases choices with
    | nil => exact canonical_triple_empty_not_injective
    | cons i rest =>
        simp only [List.length_cons] at hshort
        omega

/-- The other two observations expose the first and second factors. -/
def firstTripleFactor (x : OrderedTriple) : ℕ := primeOf x.1
def secondTripleFactor (x : OrderedTriple) : ℕ := primeOf x.2.1

/-- The only three permitted ordered-triple probes. -/
def tripleProbe (i : Fin 3) (x : OrderedTriple) : ℕ :=
  if i.val = 0 then tripleProduct x
  else if i.val = 1 then firstTripleFactor x
  else secondTripleFactor x

def tripleObservations (choices : List (Fin 3))
    (x : OrderedTriple) : List ℕ :=
  choices.map (fun i => tripleProbe i x)

/-- Any two probes, including duplicate choices, are insufficient. -/
theorem no_two_triple_probes (i j : Fin 3) :
    ¬ Function.Injective (fun x : OrderedTriple =>
      (tripleProbe i x, tripleProbe j x)) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The full triple of allowed observations is sufficient. -/
theorem three_triple_probes_injective :
    Function.Injective (tripleObservations [0, 1, 2]) := by decide

/-- The empty observation list cannot distinguish two different triples. -/
theorem empty_triple_observations_not_injective :
    ¬ Function.Injective (tripleObservations []) := by
  intro h
  have he : ((0, (0, 0)) : OrderedTriple) = (0, (0, 1)) :=
    h (by simp [tripleObservations])
  exact (by decide : ((0, (0, 0)) : OrderedTriple) ≠ (0, (0, 1))) he

theorem singleton_triple_observations_not_injective (i : Fin 3) :
    ¬ Function.Injective (tripleObservations [i]) := by
  intro h
  apply no_two_triple_probes i i
  intro x y hxy
  apply h
  have hi := congrArg Prod.fst hxy
  simpa [tripleObservations] using hi

theorem two_triple_observations_not_injective (i j : Fin 3) :
    ¬ Function.Injective (tripleObservations [i, j]) := by
  intro h
  apply no_two_triple_probes i j
  intro x y hxy
  have hi : tripleProbe i x = tripleProbe i y := congrArg Prod.fst hxy
  have hj : tripleProbe j x = tripleProbe j y := congrArg Prod.snd hxy
  apply h
  simpa [tripleObservations] using And.intro hi hj

/-- Any selection of fewer than three permitted calls fails. -/
theorem fewer_than_three_not_injective (choices : List (Fin 3))
    (hshort : choices.length < 3) :
    ¬ Function.Injective (tripleObservations choices) := by
  cases choices with
  | nil => exact empty_triple_observations_not_injective
  | cons i rest =>
      cases rest with
      | nil => exact singleton_triple_observations_not_injective i
      | cons j tail =>
          cases tail with
          | nil => exact two_triple_observations_not_injective i j
          | cons k more =>
              simp only [List.length_cons] at hshort
              omega

/-- Exact minimum is three for the product/first/second-factor library. -/
theorem minimal_ordered_triple_observations :
    (∃ choices : List (Fin 3), choices.length = 3 ∧
      Function.Injective (tripleObservations choices)) ∧
    (∀ choices : List (Fin 3), choices.length < 3 →
      ¬ Function.Injective (tripleObservations choices)) := by
  constructor
  · exact ⟨[0, 1, 2], by decide, three_triple_probes_injective⟩
  · exact fewer_than_three_not_injective

/-- Apply PR #36's kernel-intersection theorem to the triple model. -/
theorem triple_joint_kernel (x y : OrderedTriple) :
    joint tripleProduct
      (fun z => (firstTripleFactor z, secondTripleFactor z)) x =
    joint tripleProduct
      (fun z => (firstTripleFactor z, secondTripleFactor z)) y ↔
      tripleProduct x = tripleProduct y ∧
      (firstTripleFactor x, secondTripleFactor x) =
        (firstTripleFactor y, secondTripleFactor y) :=
  joint_eq_iff tripleProduct
    (fun z => (firstTripleFactor z, secondTripleFactor z)) x y

end LinearInputPrimeFactorOrbits
