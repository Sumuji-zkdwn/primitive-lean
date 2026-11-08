/-!
Finite factor normalization as an idempotent forgetting map, and adaptive
observation depth, extending PR #36, PR #50, PR #51.

Scope: fixed-length 3 with coded primes {2,3,5}; observation library
{product, first factor, second factor}. No unrestricted complexity claim.

The normalization sorts the *indices* of the factors. It is a retraction onto
the ten nondecreasing triples. Its kernel is exactly product equality and
hence the six-permutation orbit equivalence in PrimeFactorOrbits.inc.

Two adaptive queries (where the second probe depends on the first output)
still do not separate all 27 ordered triples; three fixed queries do.
-/

namespace LinearInputPrimeFactorF0

open LinearInputFiniteObservation
open LinearInputPrimeFactorObservation
open LinearInputPrimeFactorOrbits

/-- Fixed-length insertion sort on three encoded prime factors. -/
def normalizeTriple (x : OrderedTriple) : OrderedTriple :=
  if x.1 ≤ x.2.1 then
    if x.2.1 ≤ x.2.2 then x
    else if x.1 ≤ x.2.2 then (x.1, (x.2.2, x.2.1))
    else (x.2.2, (x.1, x.2.1))
  else
    if x.1 ≤ x.2.2 then (x.2.1, (x.1, x.2.2))
    else if x.2.1 ≤ x.2.2 then (x.2.1, (x.2.2, x.1))
    else (x.2.2, (x.2.1, x.1))

/-- Normalization selects exactly a canonical nondecreasing triple. -/
theorem normalize_is_sorted (x : OrderedTriple) :
    (normalizeTriple x).1 ≤ (normalizeTriple x).2.1 ∧
    (normalizeTriple x).2.1 ≤ (normalizeTriple x).2.2 := by
  rcases x with ⟨a, ⟨b, c⟩⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

/-- A canonical state is already a fixed point of normalization. -/
theorem normalize_of_sorted (x : OrderedTriple)
    (h : x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2) :
    normalizeTriple x = x := by
  simp [normalizeTriple, h.1, h.2]

/-- The sorting operation is an idempotent F0-style forgetting map. -/
theorem normalize_idempotent (x : OrderedTriple) :
    normalizeTriple (normalizeTriple x) = normalizeTriple x :=
  normalize_of_sorted (normalizeTriple x) (normalize_is_sorted x)

/-- Sorting does not change the multiplicative evaluation. -/
theorem normalize_preserves_product (x : OrderedTriple) :
    tripleProduct (normalizeTriple x) = tripleProduct x := by
  rcases x with ⟨a, ⟨b, c⟩⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

/-- Sorting also preserves the unordered multiset of prime factors. -/
theorem normalize_preserves_bag (x : OrderedTriple) :
    tripleBag (normalizeTriple x) = tripleBag x :=
  (triple_product_eq_iff_bag (normalizeTriple x) x).mp
    (normalize_preserves_product x)

/-- Product fibers and normalization fibers coincide exactly. -/
theorem product_kernel_eq_normalize_kernel (x y : OrderedTriple) :
    tripleProduct x = tripleProduct y ↔
      normalizeTriple x = normalizeTriple y := by
  constructor
  · intro h
    have heval :
        tripleProduct (normalizeTriple x) =
          tripleProduct (normalizeTriple y) := by
      calc
        tripleProduct (normalizeTriple x) = tripleProduct x :=
          normalize_preserves_product x
        _ = tripleProduct y := h
        _ = tripleProduct (normalizeTriple y) :=
          (normalize_preserves_product y).symm
    have hs : (⟨normalizeTriple x, normalize_is_sorted x⟩ : CanonicalTriple) =
        (⟨normalizeTriple y, normalize_is_sorted y⟩ : CanonicalTriple) :=
      canonical_triple_product_injective heval
    exact congrArg Subtype.val hs
  · intro h
    calc
      tripleProduct x = tripleProduct (normalizeTriple x) :=
        (normalize_preserves_product x).symm
      _ = tripleProduct (normalizeTriple y) := congrArg tripleProduct h
      _ = tripleProduct y := normalize_preserves_product y

/-- The F0 kernel is precisely the S3 position-orbit relation. -/
theorem normalize_kernel_eq_orbit (x y : OrderedTriple) :
    normalizeTriple x = normalizeTriple y ↔
      ∃ σ : Fin 6, x = reorderTriple σ y :=
  (product_kernel_eq_normalize_kernel x y).symm.trans
    (triple_product_eq_iff_orbit x y)

/-- The F0 kernel is also equality of prime multisets. -/
theorem normalize_kernel_eq_bag (x y : OrderedTriple) :
    normalizeTriple x = normalizeTriple y ↔
      tripleBag x = tripleBag y :=
  (product_kernel_eq_normalize_kernel x y).symm.trans
    (triple_product_eq_iff_bag x y)

/-- Fixed points are exactly the nondecreasing triples. -/
theorem normalize_fixed_iff_sorted (x : OrderedTriple) :
    normalizeTriple x = x ↔
      x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 := by
  constructor
  · intro h
    simpa [h] using normalize_is_sorted x
  · exact normalize_of_sorted x

/-- There are ten fixed points, the ten unordered triple classes. -/
theorem normalize_fixed_point_count :
    Fintype.card {x : OrderedTriple // normalizeTriple x = x} = 10 := by
  decide

/-- A canonical quotient representative obtained from any triple. -/
def canonicalOf (x : OrderedTriple) : CanonicalTriple :=
  ⟨normalizeTriple x, normalize_is_sorted x⟩

theorem canonical_of_fixed (x : CanonicalTriple) :
    canonicalOf x.1 = x := by
  apply Subtype.ext
  exact normalize_of_sorted x.1 x.2

theorem canonical_of_surjective : Function.Surjective canonicalOf := by
  intro x
  exact ⟨x.1, canonical_of_fixed x⟩

/-- Product is reconstructed from the canonical image: no extra information. -/
theorem product_descends_through_normalize :
    ∃ g : OrderedTriple → ℕ,
      ∀ x : OrderedTriple, tripleProduct x = g (normalizeTriple x) := by
  refine ⟨tripleProduct, ?_⟩
  intro x
  exact (normalize_preserves_product x).symm

/-- Universal factorization property: a probe factors through F0
exactly when it is constant on the multiplication fibers. -/
theorem factors_through_normalize_iff {β : Type*} (f : OrderedTriple → β) :
    (∃ g : OrderedTriple → β,
      ∀ x, f x = g (normalizeTriple x)) ↔
    (∀ x y, tripleProduct x = tripleProduct y → f x = f y) := by
  constructor
  · rintro ⟨g, hg⟩ x y hxy
    have hnorm := (product_kernel_eq_normalize_kernel x y).mp hxy
    calc
      f x = g (normalizeTriple x) := hg x
      _ = g (normalizeTriple y) := congrArg g hnorm
      _ = f y := (hg y).symm
  · intro h
    refine ⟨f, ?_⟩
    intro x
    exact h x (normalizeTriple x) (normalize_preserves_product x).symm

/-- Adding the product after canonicalization does not further refine F0. -/
theorem joint_normalize_product_same_kernel (x y : OrderedTriple) :
    joint normalizeTriple tripleProduct x =
      joint normalizeTriple tripleProduct y ↔
    normalizeTriple x = normalizeTriple y := by
  constructor
  · intro h
    exact ((joint_eq_iff normalizeTriple tripleProduct x y).mp h).1
  · intro h
    apply (joint_eq_iff normalizeTriple tripleProduct x y).mpr
    exact ⟨h, (product_kernel_eq_normalize_kernel x y).mpr h⟩

/-- At least one ordered-factor probe cannot be reconstructed from F0. -/
theorem first_factor_not_recoverable_from_normalize :
    ¬ ∃ g : OrderedTriple → ℕ,
        ∀ x, firstTripleFactor x = g (normalizeTriple x) := by
  apply no_factor_of_separation normalizeTriple firstTripleFactor
    (0, (1, 2)) (1, (0, 2))
  · decide
  · decide

/-- Hard first-observation fiber on which every possible second probe fails. -/
def hardFiberValue (first : Fin 3) : ℕ :=
  if first.val = 0 then 30 else 2

/-- For every first probe and every fixed second probe, there is a pair
on the same *chosen* first-answer fiber that remains indistinguishable. -/
theorem hard_fiber_second_probe_collision (first second : Fin 3) :
    ∃ x y : OrderedTriple,
      x ≠ y ∧
      tripleProbe first x = hardFiberValue first ∧
      tripleProbe first y = hardFiberValue first ∧
      tripleProbe second x = tripleProbe second y := by
  fin_cases first <;> fin_cases second <;> decide

/-- A two-stage adaptive transcript, choosing the second probe as a
function of the *first observed value*. -/
def adaptiveTwo (first : Fin 3) (choose : ℕ → Fin 3)
    (x : OrderedTriple) : ℕ × ℕ :=
  (tripleProbe first x, tripleProbe (choose (tripleProbe first x)) x)

/-- No deterministic adaptive protocol with at most two probes separates
all 27 ordered states, for the restricted library {product, first, second}. -/
theorem adaptive_two_not_injective (first : Fin 3)
    (choose : ℕ → Fin 3) :
    ¬ Function.Injective (adaptiveTwo first choose) := by
  obtain ⟨x, y, hne, hx, hy, hsecond⟩ :=
    hard_fiber_second_probe_collision first (choose (hardFiberValue first))
  intro h
  apply hne
  apply h
  change
    (tripleProbe first x, tripleProbe (choose (tripleProbe first x)) x) =
    (tripleProbe first y, tripleProbe (choose (tripleProbe first y)) y)
  rw [hx, hy]
  exact Prod.ext rfl hsecond

/-- Three (non-adaptive) permitted calls suffice, even when adaptive
selection is allowed; two do not, by the preceding theorem. -/
theorem adaptive_three_upper_bound :
    Function.Injective (tripleObservations [0, 1, 2]) :=
  three_triple_probes_injective

end LinearInputPrimeFactorF0
