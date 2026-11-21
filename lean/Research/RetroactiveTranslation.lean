import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-!
# Retroactive interpretation and the information retained by a summary

The source is the two-stage finite-model report on public interpretation
updates. This module proves only elementary, exact statements:

* a new reading descends to the reached summary image exactly when it is
  constant on old summary fibers;
* decoding every future coordinate forces an injective summary;
* accumulating fixed observations only removes consistent key candidates;
* an initial secret and a deterministic public input sequence determine a
  unique state trajectory, and a known current state suffices for its suffix.

The first and third statements hold for arbitrary types, not only finite
models. The cardinality corollary explicitly assumes a finite summary type.
No probability, entropy, query-complexity, cryptographic-security, or
wall-clock lower bound is asserted here. In particular, changing a current
reading is not a proof that previously learned information has been erased.

`ElasticaObservationBridge.run` and its observational quotient on main have
the same deterministic-action interpretation. We avoid importing their
geometric dependencies into this elementary module. The unmerged
`Research.ForgettingRoundTrips` is not a dependency: its concrete
non-descending observation example is related to the general fiber criterion
proved here, but its relational round-trip results are separate.
-/

namespace Elastica.RetroactiveTranslation

/-! ## Factorization through the reached summary image -/

/-- Only attained summary labels are needed; unused codomain labels impose
no nonemptiness or extension assumption on a decoder. -/
abbrev Reached {X A : Type*} (P : X → A) :=
  {a : A // ∃ x : X, P x = a}

/-- The summary as a map to its actual image. -/
def reachedSummary {X A : Type*} (P : X → A) (x : X) : Reached P :=
  ⟨P x, x, rfl⟩

/-- A requested reading loses no distinctions beyond those already lost by P. -/
def FiberConstant {X A B : Type*} (P : X → A) (Q : X → B) : Prop :=
  ∀ x y : X, P x = P y → Q x = Q y

/-- Exact recovery of a new reading from the attained old summary alone. -/
def FactorsThroughReached {X A B : Type*} (P : X → A) (Q : X → B) : Prop :=
  ∃ h : Reached P → B, ∀ x : X, h (reachedSummary P x) = Q x

/-- The needed and sufficient condition for a new reading to use only the
old summary. No surjectivity onto the original codomain is required. -/
theorem factors_through_reached_iff_fiber_constant {X A B : Type*}
    (P : X → A) (Q : X → B) :
    FactorsThroughReached P Q ↔ FiberConstant P Q := by
  constructor
  · rintro ⟨h, hh⟩ x y hxy
    have he : reachedSummary P x = reachedSummary P y := Subtype.ext hxy
    calc
      Q x = h (reachedSummary P x) := (hh x).symm
      _ = h (reachedSummary P y) := congrArg h he
      _ = Q y := hh y
  · intro h
    classical
    refine ⟨fun a => Q (Classical.choose a.property), ?_⟩
    intro x
    exact h _ x (Classical.choose_spec (reachedSummary P x).property)

/-- The decoder, when it exists, is unique on attained labels. -/
theorem reached_decoder_unique {X A B : Type*} (P : X → A) (Q : X → B)
    (h₁ h₂ : Reached P → B)
    (hh₁ : ∀ x, h₁ (reachedSummary P x) = Q x)
    (hh₂ : ∀ x, h₂ (reachedSummary P x) = Q x) : h₁ = h₂ := by
  funext a
  obtain ⟨x, hx⟩ := a.property
  have ha : reachedSummary P x = a := Subtype.ext hx
  rw [← ha]
  exact (hh₁ x).trans (hh₂ x).symm

/-- A single old-summary collision separated by a new reading rules out
every exact decoder that sees only that summary. -/
theorem collision_prevents_decoder {X A B : Type*} (P : X → A) (Q : X → B)
    (x y : X) (hP : P x = P y) (hQ : Q x ≠ Q y) :
    ¬ FactorsThroughReached P Q := by
  intro h
  exact hQ ((factors_through_reached_iff_fiber_constant P Q).mp h x y hP)

/-- Two bits suffice to witness the obstruction: retaining the first
coordinate does not permit recovery of the second coordinate. -/
theorem second_coordinate_not_from_first :
    ¬ FactorsThroughReached (Prod.fst : Bool × Bool → Bool)
      (Prod.snd : Bool × Bool → Bool) := by
  apply collision_prevents_decoder
    (Prod.fst : Bool × Bool → Bool) (Prod.snd : Bool × Bool → Bool)
    (false, false) (false, true) rfl
  intro h
  cases h

/-! ## The distinctions required by all future readings -/

/-- Equality of every permitted future reading. -/
def SameFuture {X U B : Type*} (Q : U → X → B) (x y : X) : Prop :=
  ∀ u : U, Q u x = Q u y

/-- A summary supports the entire future-query family exactly when its
fibers are contained in equality of all those future answers. -/
theorem all_future_decoders_iff {X A U B : Type*}
    (P : X → A) (Q : U → X → B) :
    (∀ u, FactorsThroughReached P (Q u)) ↔
      ∀ x y, P x = P y → SameFuture Q x y := by
  constructor
  · intro h x y hxy u
    exact (factors_through_reached_iff_fiber_constant P (Q u)).mp (h u) x y hxy
  · intro h u
    apply (factors_through_reached_iff_fiber_constant P (Q u)).mpr
    intro x y hxy
    exact h x y hxy u

/-- Arbitrary later coordinate queries require retention of all distinctions
between input functions. This is an injectivity result, not a time bound. -/
theorem coordinate_decoders_force_injective {ι B A : Type*}
    (P : (ι → B) → A)
    (h : ∀ i : ι, FactorsThroughReached P (fun x => x i)) :
    Function.Injective P := by
  intro x y hxy
  funext i
  exact (factors_through_reached_iff_fiber_constant P (fun z => z i)).mp
    (h i) x y hxy

/-- The exact finite state-count lower bound for summaries of arbitrary
d-bit inputs that must answer every later coordinate query. -/
theorem bit_summary_card_lower_bound {A : Type*} [Fintype A] (d : ℕ)
    (P : (Fin d → Bool) → A)
    (h : ∀ i : Fin d, FactorsThroughReached P (fun x => x i)) :
    2 ^ d ≤ Fintype.card A := by
  have hcard := Fintype.card_le_of_injective P
    (coordinate_decoders_force_injective P h)
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using hcard

/-! ## Fixed constraints accumulated in a public history -/

/-- Candidates compatible with every retained observation. `check` includes
the time/version of the observation when those matter. -/
def candidates {K E : Type*} (check : E → K → Prop)
    (history : List E) : Set K :=
  {k | ∀ e ∈ history, check e k}

/-- Appending observations intersects the old candidate set with the new
constraints. Earlier rejected candidates are not revived. -/
theorem candidates_append {K E : Type*} (check : E → K → Prop)
    (old fresh : List E) :
    candidates check (old ++ fresh) =
      candidates check old ∩ candidates check fresh := by
  apply Set.ext
  intro k
  change (∀ e ∈ old ++ fresh, check e k) ↔
    (∀ e ∈ old, check e k) ∧ (∀ e ∈ fresh, check e k)
  constructor
  · intro h
    constructor
    · intro e he
      exact h e (List.mem_append.mpr (Or.inl he))
    · intro e he
      exact h e (List.mem_append.mpr (Or.inr he))
  · rintro ⟨hOld, hFresh⟩ e he
    rcases List.mem_append.mp he with heOld | heFresh
    · exact hOld e heOld
    · exact hFresh e heFresh

/-- Candidate inclusion is opposite to inclusion of the retained constraints. -/
theorem candidates_antitone {K E : Type*} (check : E → K → Prop)
    (old fresh : List E) (h : ∀ e ∈ old, e ∈ fresh) :
    candidates check fresh ⊆ candidates check old := by
  intro k hk e he
  exact hk e (h e he)

theorem candidates_append_subset {K E : Type*} (check : E → K → Prop)
    (old fresh : List E) :
    candidates check (old ++ fresh) ⊆ candidates check old := by
  apply candidates_antitone check old (old ++ fresh)
  intro e he
  exact List.mem_append.mpr (Or.inl he)

theorem discarded_key_stays_discarded {K E : Type*} (check : E → K → Prop)
    (old fresh : List E) (k : K) (hk : k ∉ candidates check old) :
    k ∉ candidates check (old ++ fresh) := by
  intro hNew
  exact hk (candidates_append_subset check old fresh hNew)

/-- This conclusion uses one fixed target reading. It does not compare two
different targets chosen before and after a semantic update. -/
theorem fixed_reading_candidates_append_subset {K E B : Type*}
    (check : E → K → Prop) (read : K → B) (old fresh : List E) :
    read '' candidates check (old ++ fresh) ⊆ read '' candidates check old := by
  intro b hb
  obtain ⟨k, hk, hkb⟩ := hb
  exact ⟨k, candidates_append_subset check old fresh hk, hkb⟩

/-! ## Deterministic public updates and state recovery -/

/-- Every private initial value is represented by the key. The update and
input stream are public; there is no additional private input in this model. -/
def publicState {K S U : Type*} (initial : K → S) (step : U → S → S)
    (inputs : ℕ → U) (k : K) : ℕ → S
  | 0 => initial k
  | t + 1 => step (inputs t) (publicState initial step inputs k t)

/-- A trace satisfying the public recurrence is uniquely determined by its
initial key. This is exact determinism, not a complexity guarantee. -/
theorem public_state_unique {K S U : Type*} (initial : K → S)
    (step : U → S → S) (inputs : ℕ → U) (k : K) (trace : ℕ → S)
    (h₀ : trace 0 = initial k)
    (hStep : ∀ t, trace (t + 1) = step (inputs t) (trace t)) :
    trace = publicState initial step inputs k := by
  funext t
  induction t with
  | zero => exact h₀
  | succ t ih =>
      calc
        trace (t + 1) = step (inputs t) (trace t) := hStep t
        _ = step (inputs t) (publicState initial step inputs k t) :=
          congrArg (step (inputs t)) ih
        _ = publicState initial step inputs k (t + 1) := rfl

/-- Different key labels with the same initial state cannot generate new
distinct trajectories under the same deterministic public updates. -/
theorem public_states_eq_of_initial_eq {K S U : Type*} (initial : K → S)
    (step : U → S → S) (inputs : ℕ → U) (k l : K)
    (h : initial k = initial l) :
    publicState initial step inputs k = publicState initial step inputs l := by
  funext t
  induction t with
  | zero => exact h
  | succ t ih => exact congrArg (step (inputs t)) ih

/-- Once the complete current state is shared, every later state is shared
as well, provided no unknown private input is subsequently introduced. -/
theorem public_states_future_of_equal_current {K S U : Type*}
    (initial : K → S) (step : U → S → S) (inputs : ℕ → U)
    (k l : K) (offset : ℕ)
    (h : publicState initial step inputs k offset =
      publicState initial step inputs l offset) (n : ℕ) :
    publicState initial step inputs k (offset + n) =
      publicState initial step inputs l (offset + n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact congrArg (step (inputs (offset + n))) ih

/-- Future replay starts from the saved current state; the earlier prefix
need not be replayed once that state is available. -/
theorem public_state_suffix {K S U : Type*} (initial : K → S)
    (step : U → S → S) (inputs : ℕ → U) (k : K) (offset n : ℕ) :
    publicState initial step inputs k (offset + n) =
      publicState (fun _ : Unit => publicState initial step inputs k offset)
        step (fun t => inputs (offset + t)) () n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (step (inputs (offset + n))) ih

#print axioms factors_through_reached_iff_fiber_constant
#print axioms reached_decoder_unique
#print axioms collision_prevents_decoder
#print axioms second_coordinate_not_from_first
#print axioms all_future_decoders_iff
#print axioms coordinate_decoders_force_injective
#print axioms bit_summary_card_lower_bound
#print axioms candidates_append
#print axioms candidates_antitone
#print axioms candidates_append_subset
#print axioms discarded_key_stays_discarded
#print axioms fixed_reading_candidates_append_subset
#print axioms public_state_unique
#print axioms public_states_eq_of_initial_eq
#print axioms public_states_future_of_equal_current
#print axioms public_state_suffix

end Elastica.RetroactiveTranslation
