/-!
# Parallel partial-write gluing: an exact overlap criterion

A local operation proposes a partial assignment of values to a shared
coordinate space. Arbitrary finite families of proposals can be combined
into ONE global state exactly when their overlapping assigned values agree.

This is a constructive gluing criterion, not merely individual success
or sequential reachability. A priority-based first-write algorithm
produces a canonical amalgamation relative to an existing base state.

We also give a sharply scoped temporal result: with an explicit policy
which permits later local actions iff two concurrent proposals glue,
conflicting writes force all local operation domains to be empty and
hence falsify PR #65's historical preservation property. Compatible
writes permit a faithful successor embedding under that same policy.

The global state type and observer are held fixed. This module does not
claim that arbitrary asynchronous distributed execution, concurrency
scheduling, causal effects, or physics obeys this simple write model.
-/

section

namespace LinearInputParallelGluing

open LinearInputHistoryNonpreservation
open LinearInputTemporalExtinction
open LinearInputFiniteSelfSynthesis

/-- Local proposals agree wherever they both assign a value. -/
def Compatible {I V : Type*} (p q : I → Option V) : Prop :=
  ∀ i a b, p i = some a → q i = some b → a = b

/-- A global state realizes every assignment made by a local proposal. -/
def Realizes {I V : Type*} (s : I → V) (p : I → Option V) : Prop :=
  ∀ i a, p i = some a → s i = a

/-- Choose values from p first, from q second, or from the base state. -/
def glue {I V : Type*}
    (base : I → V) (p q : I → Option V) : I → V :=
  fun i => match p i with
  | some v => v
  | none => (q i).getD (base i)

theorem compatible_symm {I V : Type*}
    (p q : I → Option V)
    (h : Compatible p q) : Compatible q p := by
  intro i a b hq hp
  exact (h i b a hp hq).symm

theorem glue_realizes_left {I V : Type*}
    (base : I → V) (p q : I → Option V) :
    Realizes (glue base p q) p := by
  intro i a hp
  simp [glue, hp]

theorem glue_realizes_right {I V : Type*}
    (base : I → V) (p q : I → Option V)
    (h : Compatible p q) :
    Realizes (glue base p q) q := by
  intro i b hq
  cases hp : p i with
  | none =>
      simp [glue, hp, hq]
  | some a =>
      have hab : a = b := h i a b hp hq
      simp [glue, hp, hab]

/-- Exact necessary-and-sufficient criterion for two simultaneous
partial state updates to possess a common global realization. -/
theorem compatible_iff_exists_glue {I V : Type*}
    (base : I → V) (p q : I → Option V) :
    Compatible p q ↔
      ∃ s : I → V, Realizes s p ∧ Realizes s q := by
  constructor
  · intro h
    exact ⟨glue base p q,
      glue_realizes_left base p q,
      glue_realizes_right base p q h⟩
  · rintro ⟨s, hp, hq⟩ i a b hpa hqb
    exact (hp i a hpa).symm.trans (hq i b hqb)

/-- The constructive glue retains the base on untouched coordinates. -/
theorem glue_untouched {I V : Type*}
    (base : I → V) (p q : I → Option V) (i : I)
    (hp : p i = none) (hq : q i = none) :
    glue base p q i = base i := by
  simp [glue, hp, hq]

/-- The first nonempty write in a finite family is used for each index. -/
def firstWrite {I V : Type*} :
    List (I → Option V) → I → Option V
  | [], _ => none
  | p :: ps, i =>
      match p i with
      | some v => some v
      | none => firstWrite ps i

def glueAll {I V : Type*}
    (base : I → V) (ps : List (I → Option V)) : I → V :=
  fun i => (firstWrite ps i).getD (base i)

/-- All overlapping assignments from any two members agree. -/
def PairwiseCompatible {I V : Type*}
    (ps : List (I → Option V)) : Prop :=
  ∀ p, p ∈ ps → ∀ q, q ∈ ps → Compatible p q

theorem firstWrite_some_has_member {I V : Type*}
    (ps : List (I → Option V)) (i : I) (v : V)
    (h : firstWrite ps i = some v) :
    ∃ p, p ∈ ps ∧ p i = some v := by
  induction ps with
  | nil =>
      simp [firstWrite] at h
  | cons p rest ih =>
      cases hp : p i with
      | none =>
          have ht : firstWrite rest i = some v := by
            simpa [firstWrite, hp] using h
          obtain ⟨q, hmem, hq⟩ := ih ht
          exact ⟨q, List.mem_cons_of_mem p hmem, hq⟩
      | some w =>
          have hw : w = v := by
            simpa [firstWrite, hp] using h
          subst v
          exact ⟨p, by simp, hp⟩

theorem firstWrite_exists_of_member {I V : Type*}
    (ps : List (I → Option V)) (p : I → Option V)
    (hmem : p ∈ ps) (i : I) (v : V) (hp : p i = some v) :
    ∃ w, firstWrite ps i = some w := by
  induction ps with
  | nil =>
      simp at hmem
  | cons q rest ih =>
      cases hq : q i with
      | some w =>
          exact ⟨w, by simp [firstWrite, hq]⟩
      | none =>
          rcases List.mem_cons.mp hmem with heq | hr
          · subst p
            rw [hq] at hp
            cases hp
          · obtain ⟨w, hw⟩ := ih hr
            exact ⟨w, by simpa [firstWrite, hq] using hw⟩

theorem firstWrite_eq_of_member {I V : Type*}
    (ps : List (I → Option V)) (hpair : PairwiseCompatible ps)
    (p : I → Option V) (hmem : p ∈ ps)
    (i : I) (v : V) (hp : p i = some v) :
    firstWrite ps i = some v := by
  obtain ⟨w, hw⟩ :=
    firstWrite_exists_of_member ps p hmem i v hp
  obtain ⟨q, hq, hqval⟩ :=
    firstWrite_some_has_member ps i w hw
  have hwv : w = v := hpair q hq p hmem i w v hqval hp
  simpa [hwv] using hw

theorem glueAll_realizes_of_pairwise {I V : Type*}
    (base : I → V) (ps : List (I → Option V))
    (hpair : PairwiseCompatible ps)
    (p : I → Option V) (hp : p ∈ ps) :
    Realizes (glueAll base ps) p := by
  intro i v hwrite
  have hfirst := firstWrite_eq_of_member ps hpair p hp i v hwrite
  simp [glueAll, hfirst]

/-- Main finite-family gluing theorem. Every finite collection of local
partial updates has a joint global state iff all overlaps agree pairwise.
The forward direction is constructive via firstWrite and the base state. -/
theorem pairwise_iff_exists_global {I V : Type*}
    (base : I → V) (ps : List (I → Option V)) :
    PairwiseCompatible ps ↔
      ∃ s : I → V, ∀ p, p ∈ ps → Realizes s p := by
  constructor
  · intro h
    exact ⟨glueAll base ps,
      fun p hp => glueAll_realizes_of_pairwise base ps h p hp⟩
  · rintro ⟨s, hs⟩ p hp q hq i a b hpa hqb
    exact ((hs p hp) i a hpa).symm.trans ((hs q hq) i b hqb)

theorem firstWrite_none_of_unwritten {I V : Type*}
    (ps : List (I → Option V)) (i : I) :
    (∀ p, p ∈ ps → p i = none) →
      firstWrite ps i = none := by
  induction ps with
  | nil =>
      intro _
      rfl
  | cons p rest ih =>
      intro h
      have hp : p i = none := h p (by simp)
      have hr : ∀ q, q ∈ rest → q i = none := by
        intro q hq
        exact h q (List.mem_cons_of_mem p hq)
      simpa [firstWrite, hp] using ih hr

theorem glueAll_untouched {I V : Type*}
    (base : I → V) (ps : List (I → Option V))
    (i : I) (h : ∀ p, p ∈ ps → p i = none) :
    glueAll base ps i = base i := by
  have hn := firstWrite_none_of_unwritten ps i h
  simp [glueAll, hn]

theorem all_realizations_agree_on_written_coordinates {I V : Type*}
    (base : I → V) (ps : List (I → Option V))
    (hpair : PairwiseCompatible ps)
    (s : I → V)
    (hs : ∀ p, p ∈ ps → Realizes s p)
    (i : I) (hcovered : ∃ p, p ∈ ps ∧ ∃ v, p i = some v) :
    s i = glueAll base ps i := by
  obtain ⟨p, hp, v, hv⟩ := hcovered
  have h1 := (hs p hp) i v hv
  have h2 := (glueAll_realizes_of_pairwise base ps hpair p hp) i v hv
  exact h1.trans h2.symm

/-- Concrete overlapping destructive writes disagree on coordinate zero. -/
def conflictingLeft (i : Fin 2) : Option Bool :=
  if i = 0 then some true else none

def conflictingRight (i : Fin 2) : Option Bool :=
  if i = 0 then some false else none

theorem conflicting_writes_do_not_glue :
    ¬ Compatible conflictingLeft conflictingRight := by
  intro h
  have hc : (true : Bool) = false :=
    h 0 true false (by decide) (by decide)
  cases hc

theorem conflicting_family_has_no_global_state :
    ¬ ∃ s : Fin 2 → Bool,
      Realizes s conflictingLeft ∧ Realizes s conflictingRight := by
  intro h
  exact conflicting_writes_do_not_glue
    ((compatible_iff_exists_glue (fun _ : Fin 2 => false)
      conflictingLeft conflictingRight).mpr h)

/-- In the noninterfering comparison, each local writes its own index. -/
def disjointLeft (i : Fin 2) : Option Bool :=
  if i = 0 then some true else none

def disjointRight (i : Fin 2) : Option Bool :=
  if i = 1 then some true else none

theorem disjoint_writes_compatible :
    Compatible disjointLeft disjointRight := by
  intro i a b ha hb
  fin_cases i
  · have hn : disjointRight 0 = none := rfl
    rw [hn] at hb
    cases hb
  · have hn : disjointLeft 1 = none := rfl
    rw [hn] at ha
    cases ha

theorem disjoint_glue_fulfills_both :
    glue (fun _ : Fin 2 => false) disjointLeft disjointRight 0 = true ∧
      glue (fun _ : Fin 2 => false) disjointLeft disjointRight 1 = true := by
  decide

/-- Even overlapping writes are admissible when they agree in value. -/
theorem equal_overlapping_writes_compatible :
    Compatible conflictingLeft conflictingLeft := by
  intro i a b ha hb
  rw [ha] at hb
  exact Option.some.inj hb

/-- The destructive total-state proposals of PR #69 conflict on overlap,
while the incremental writes can be glued. -/
def destructiveWholeA (i : Fin 2) : Option Bool :=
  if i = 0 then some true else some false

def destructiveWholeB (i : Fin 2) : Option Bool :=
  if i = 0 then some false else some true

theorem destructive_whole_writes_incompatible :
    ¬ Compatible destructiveWholeA destructiveWholeB := by
  intro h
  have hc : (true : Bool) = false :=
    h 0 true false (by decide) (by decide)
  cases hc

/-- This exact Boolean gate is an explicit operational policy:
after time zero, keep local operations available iff both simultaneous
partial updates admit a coherent global state. -/
def compatibleFlag (p q : Fin 2 → Option Bool) : Bool :=
  decide (Compatible p q)

theorem compatibleFlag_iff (p q : Fin 2 → Option Bool) :
    compatibleFlag p q = true ↔ Compatible p q := by
  simp [compatibleFlag]

def parallelTimeline (p q : Fin 2 → Option Bool) :
    LocalTimeline (Fin 2) Unit (Fin 2) :=
  ⟨[0, 1],
    (fun t _ _ => if t = 0 then true else compatibleFlag p q),
    (fun _ => LinearInputTemporalExtinction.flip),
    (fun _ _ => ())⟩

theorem parallelTimeline_step_zero (p q : Fin 2 → Option Bool)
    (x : Fin 2) :
    stepAt (parallelTimeline p q) 0 x =
      LinearInputTemporalExtinction.flip x := by
  rfl

theorem parallelTimeline_step_one_of_compatible
    (p q : Fin 2 → Option Bool) (hc : Compatible p q)
    (x : Fin 2) :
    stepAt (parallelTimeline p q) 1 x =
      LinearInputTemporalExtinction.flip x := by
  have hb : compatibleFlag p q = true :=
    (compatibleFlag_iff p q).mpr hc
  simp [stepAt, parallelTimeline, hb, chooseTarget]

theorem parallelTimeline_extinct_of_incompatible
    (p q : Fin 2 → Option Bool) (hc : ¬ Compatible p q) :
    AllExtinct (parallelTimeline p q) 1 := by
  intro x loc _
  have hb : compatibleFlag p q = false := by
    simp [compatibleFlag, hc]
  simp [parallelTimeline, hb]

theorem parallel_no_preservation_of_incompatible
    (p q : Fin 2 → Option Bool) (hc : ¬ Compatible p q) :
    ¬ Preserves (historyAt (parallelTimeline p q) 0)
      (historyAt (parallelTimeline p q) 1) := by
  have hmove :
      stepAt (parallelTimeline p q) 0 (0 : Fin 2) ≠ 0 := by
    rw [parallelTimeline_step_zero]
    decide
  exact extinction_forces_nonpreservation
    (parallelTimeline p q) 0 1 (0 : Fin 2) hmove
    (parallelTimeline_extinct_of_incompatible p q hc)

theorem parallel_preservation_of_compatible
    (p q : Fin 2 → Option Bool) (hc : Compatible p q) :
    Preserves (historyAt (parallelTimeline p q) 0)
      (historyAt (parallelTimeline p q) 1) := by
  refine ⟨fun x => x, ?_, ?_, ?_⟩
  · intro x y h
    exact h
  · intro x
    rfl
  · intro x
    change stepAt (parallelTimeline p q) 0 x =
      stepAt (parallelTimeline p q) 1 x
    rw [parallelTimeline_step_zero,
      parallelTimeline_step_one_of_compatible p q hc]

/-- An exact temporal boundary under the stated gate and fixed dynamics,
not a universal equivalence for unconstrained distributed systems. -/
theorem parallel_history_preserved_iff_compatible
    (p q : Fin 2 → Option Bool) :
    Preserves (historyAt (parallelTimeline p q) 0)
        (historyAt (parallelTimeline p q) 1) ↔
      Compatible p q := by
  constructor
  · intro h
    by_contra hc
    exact (parallel_no_preservation_of_incompatible p q hc) h
  · exact parallel_preservation_of_compatible p q

theorem conflict_causes_historical_nonpreservation :
    ¬ Preserves
      (historyAt (parallelTimeline conflictingLeft conflictingRight) 0)
      (historyAt (parallelTimeline conflictingLeft conflictingRight) 1) :=
  parallel_no_preservation_of_incompatible conflictingLeft conflictingRight
    conflicting_writes_do_not_glue

theorem disjoint_gluing_avoids_history_loss :
    Preserves
      (historyAt (parallelTimeline disjointLeft disjointRight) 0)
      (historyAt (parallelTimeline disjointLeft disjointRight) 1) :=
  parallel_preservation_of_compatible disjointLeft disjointRight
    disjoint_writes_compatible

end LinearInputParallelGluing
