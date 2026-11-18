import Mathlib

/-!
# Chair, pie, and finite kill-spots

A finite universe of external permissions and a (potentially infinite) set of
internal operations generate permitted finite action words. Success is
existential reachability. We prove monotonicity of success in permission sets
and the classical finite duality between minimal successful permission sets
and sets of permissions whose removal blocks *all* successful words.

The labels "buyer" and "chair" in the examples are deliberately abstract.
No probabilistic, monetary, or real-world acquisition claim is made.

Independent finite tests: tests/test_chair_pie_killspot.py
-/

namespace Elastica.ChairPieKillSpot

/-- An action word is allowed when each externally labelled action belongs
    to the set of available external permissions. Every internal action is
    available by definition. -/
def Allowed {ι G : Type*} [DecidableEq G]
    (A : Finset G) (word : List (ι ⊕ G)) : Prop :=
  ∀ a ∈ word, match a with
    | Sum.inl _ => True
    | Sum.inr g => g ∈ A

/-- Deterministic interpretation of a finite word. -/
def run {ι G σ : Type*} (step : (ι ⊕ G) → σ → σ) :
    List (ι ⊕ G) → σ → σ
  | [], s => s
  | a :: rest, s => run step rest (step a s)

/-- Possible success means some permitted finite word reaches a goal.
    This is existential, not a probability or guarantee of external events. -/
def RevenuePossible {ι G σ : Type*} [DecidableEq G]
    (step : (ι ⊕ G) → σ → σ) (start : σ) (goal : σ → Prop)
    (A : Finset G) : Prop :=
  ∃ word : List (ι ⊕ G), Allowed A word ∧ goal (run step word start)

/-- Permitting additional external actions never invalidates an old word. -/
theorem allowed_mono {ι G : Type*} [DecidableEq G]
    {A B : Finset G} (hAB : A ⊆ B) (word : List (ι ⊕ G))
    (hw : Allowed A word) : Allowed B word := by
  intro a ha
  cases a with
  | inl i => trivial
  | inr g => exact hAB (hw _ ha)

/-- The finite-word reachability predicate is monotone in permissions. -/
theorem revenue_mono {ι G σ : Type*} [DecidableEq G]
    (step : (ι ⊕ G) → σ → σ) (start : σ) (goal : σ → Prop)
    {A B : Finset G} (hAB : A ⊆ B)
    (h : RevenuePossible step start goal A) :
    RevenuePossible step start goal B := by
  obtain ⟨word, hword, hgoal⟩ := h
  exact ⟨word, allowed_mono hAB word hword, hgoal⟩

/-- A minimal set of external conditions sufficient for an outcome. -/
def MinimalEnabler {G : Type*} [DecidableEq G]
    (f : Finset G → Prop) (E A : Finset G) : Prop :=
  A ⊆ E ∧ f A ∧ ∀ B : Finset G, B ⊂ A → ¬ f B

/-- A finite successful set contains an inclusion-minimal successful set.
    This does not require monotonicity. -/
private theorem exists_minimal_success {G : Type*} [DecidableEq G]
    (f : Finset G → Prop) (E : Finset G) (hE : f E) :
    ∃ A, MinimalEnabler f E A := by
  classical
  have aux : ∀ n : ℕ, ∀ S : Finset G, S.card = n → f S →
      ∃ A, MinimalEnabler f S A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hcard hS
        by_cases hsmaller : ∃ T : Finset G, T ⊂ S ∧ f T
        · obtain ⟨T, hTS, hT⟩ := hsmaller
          have hlt : T.card < n := by
            rw [← hcard]
            exact Finset.card_lt_card hTS
          obtain ⟨A, hAT, hfA, hMin⟩ := ih T.card hlt T rfl hT
          exact ⟨A, hAT.trans hTS.subset, hfA, hMin⟩
        · refine ⟨S, subset_rfl, hS, ?_⟩
          intro T hTS hT
          exact hsmaller ⟨T, hTS, hT⟩
  exact aux E.card E rfl hE

/-- Any reachable outcome has at least one minimal enabling certificate. -/
theorem minimal_enabler_exists_iff {G : Type*} [DecidableEq G]
    (f : Finset G → Prop)
    (hmono : ∀ A B : Finset G, A ⊆ B → f A → f B)
    (E : Finset G) :
    f E ↔ ∃ A, MinimalEnabler f E A := by
  constructor
  · intro hE
    exact exists_minimal_success f E hE
  · rintro ⟨A, hA, hfA, _⟩
    exact hmono A E hA hfA

/-- A kill-spot is a set of permissions whose removal prevents success. -/
def Blocks {G : Type*} [DecidableEq G]
    (f : Finset G → Prop) (E K : Finset G) : Prop :=
  ¬ f (E \ K)

/-- Removing K blocks all successful words exactly when K intersects
    *every* minimal enabling certificate. This is the hitting-set duality.
    K need not be contained in E: outside elements have no effect. -/
theorem blocks_iff_hits_minimal {G : Type*} [DecidableEq G]
    (f : Finset G → Prop)
    (hmono : ∀ A B : Finset G, A ⊆ B → f A → f B)
    (E K : Finset G) :
    Blocks f E K ↔
      ∀ A, MinimalEnabler f E A → (A ∩ K).Nonempty := by
  classical
  constructor
  · intro hblock A hA
    by_contra hnot
    have hdisj : ∀ x ∈ A, x ∉ K := by
      intro x hxA hxK
      exact hnot ⟨x, Finset.mem_inter.mpr ⟨hxA, hxK⟩⟩
    have hsubset : A ⊆ E \ K := by
      intro x hxA
      exact Finset.mem_sdiff.mpr ⟨hA.1 hxA, hdisj x hxA⟩
    exact hblock (hmono A (E \ K) hsubset hA.2.1)
  · intro hh hsuccess
    obtain ⟨A, hAsub, hAsucc, hAmin⟩ :=
      exists_minimal_success f (E \ K) hsuccess
    have hAE : A ⊆ E := hAsub.trans (Finset.sdiff_subset)
    obtain ⟨x, hx⟩ := hh A ⟨hAE, hAsucc, hAmin⟩
    have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
    have hxK : x ∈ K := (Finset.mem_inter.mp hx).2
    exact (Finset.mem_sdiff.mp (hAsub hxA)).2 hxK


/-- A minimal blocker is a smallest-by-inclusion set whose removal
    prevents all successes. This need not be a singleton. -/
def MinimalBlocker {G : Type*} [DecidableEq G]
    (f : Finset G → Prop) (E K : Finset G) : Prop :=
  K ⊆ E ∧ Blocks f E K ∧
    ∀ L : Finset G, L ⊂ K → ¬ Blocks f E L

/-- If revenue cannot be reached without external permission, at least
    one minimal blocking set exists: removing all of E is a blocker. -/
theorem minimal_blocker_exists_of_no_free_success {G : Type*} [DecidableEq G]
    (f : Finset G → Prop) (E : Finset G) (hfree : ¬ f ∅) :
    ∃ K, MinimalBlocker f E K := by
  have hblock : Blocks f E E := by
    simpa [Blocks] using hfree
  change ∃ K, MinimalEnabler (Blocks f E) E K
  exact exists_minimal_success (Blocks f E) E hblock

/-- Minimal blockers are exactly inclusion-minimal hitting sets of all
    minimal enablers. This is the exact classification implemented in Python. -/
theorem minimal_blocker_iff_minimal_hitting {G : Type*} [DecidableEq G]
    (f : Finset G → Prop)
    (hmono : ∀ A B : Finset G, A ⊆ B → f A → f B)
    (E K : Finset G) :
    MinimalBlocker f E K ↔
      K ⊆ E ∧
      (∀ A, MinimalEnabler f E A → (A ∩ K).Nonempty) ∧
      (∀ L : Finset G, L ⊂ K →
        ¬ (∀ A, MinimalEnabler f E A → (A ∩ L).Nonempty)) := by
  constructor
  · rintro ⟨hKE, hblock, hminimal⟩
    refine ⟨hKE, (blocks_iff_hits_minimal f hmono E K).mp hblock, ?_⟩
    intro L hL hhits
    exact (hminimal L hL) ((blocks_iff_hits_minimal f hmono E L).mpr hhits)
  · rintro ⟨hKE, hhits, hminimal⟩
    refine ⟨hKE, (blocks_iff_hits_minimal f hmono E K).mpr hhits, ?_⟩
    intro L hL hblock
    exact (hminimal L hL) ((blocks_iff_hits_minimal f hmono E L).mp hblock)

/-- The main theorem applied to finite-word action systems. -/
theorem revenue_blocks_iff {ι G σ : Type*} [DecidableEq G]
    (step : (ι ⊕ G) → σ → σ) (start : σ) (goal : σ → Prop)
    (E K : Finset G) :
    Blocks (RevenuePossible step start goal) E K ↔
      ∀ A, MinimalEnabler (RevenuePossible step start goal) E A →
        (A ∩ K).Nonempty := by
  apply blocks_iff_hits_minimal
  intro A B hAB hA
  exact revenue_mono step start goal hAB hA

/-- Three abstract permissions: buyer = 0, chair A = 1, chair B = 2. -/
def SharedBuyer (A : Finset (Fin 3)) : Prop :=
  (0 : Fin 3) ∈ A ∧ ((1 : Fin 3) ∈ A ∨ (2 : Fin 3) ∈ A)

/-- Adding a permission never invalidates a sale in the two-chair model. -/
theorem shared_buyer_mono (A B : Finset (Fin 3)) (hAB : A ⊆ B) :
    SharedBuyer A → SharedBuyer B := by
  rintro ⟨hbuyer, hchairs⟩
  refine ⟨hAB hbuyer, ?_⟩
  rcases hchairs with hA | hB
  · exact Or.inl (hAB hA)
  · exact Or.inr (hAB hB)

/-- Neither chair is sufficient when there is no common buyer. -/
theorem two_chairs_without_buyer :
    ¬ SharedBuyer ({1, 2} : Finset (Fin 3)) := by
  simp [SharedBuyer]

/-- The common buyer is a single-point kill-spot for both chairs. -/
theorem shared_buyer_killspot :
    Blocks SharedBuyer Finset.univ ({0} : Finset (Fin 3)) := by
  simp [Blocks, SharedBuyer]

end Elastica.ChairPieKillSpot

#print axioms Elastica.ChairPieKillSpot.revenue_mono
#print axioms Elastica.ChairPieKillSpot.minimal_enabler_exists_iff
#print axioms Elastica.ChairPieKillSpot.blocks_iff_hits_minimal
#print axioms Elastica.ChairPieKillSpot.minimal_blocker_exists_of_no_free_success
#print axioms Elastica.ChairPieKillSpot.minimal_blocker_iff_minimal_hitting
#print axioms Elastica.ChairPieKillSpot.revenue_blocks_iff
#print axioms Elastica.ChairPieKillSpot.two_chairs_without_buyer
#print axioms Elastica.ChairPieKillSpot.shared_buyer_killspot
