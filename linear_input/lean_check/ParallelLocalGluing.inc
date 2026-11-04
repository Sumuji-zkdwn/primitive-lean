/-!
# Simultaneous local-to-global gluing and operational realization

A local subsystem supplies a PARTIAL assignment on a common coordinate type:
some v fixes the coordinate; none leaves it unspecified. Under a nonempty
value type, a family of partial assignments can be merged into one global
assignment if and only if their values agree wherever they overlap.

This plain gluing theorem is distinct from two stronger requirements:
a global admissibility predicate, and reachability under the actual
operator vocabulary. Under full coordinate coverage, operational gluing
has an exact factorization into (i) overlap agreement, (ii) admissibility
of the unique canonical global state, and (iii) its operational reachability.

Finite countermodels distinguish incompatible overlapping full results,
compatible but globally forbidden non-overlapping demands, and compatible
goals unreachable by any destructive operator word. A non-destructive
control permits a word that realizes the common global state.

Preservation is never assumed as a universal axiom. No claim is made
that all physical or logical systems obey this partial-function model.
-/

noncomputable section

namespace LinearInputParallelGluing

open LinearInputOperatorWords
open LinearInputCooperativeGluing

/-- Local partial assignments agree wherever their domains overlap. -/
def PairwiseCompatible {Λ I V : Type*}
    (locals : List Λ) (part : Λ → I → Option V) : Prop :=
  ∀ l, l ∈ locals → ∀ m, m ∈ locals →
    ∀ i a b, part l i = some a → part m i = some b → a = b

/-- A global assignment respects every specified local value. -/
def Represents {Λ I V : Type*}
    (locals : List Λ) (part : Λ → I → Option V)
    (g : I → V) : Prop :=
  ∀ l, l ∈ locals → ∀ i v, part l i = some v → g i = v

def HasGlue {Λ I V : Type*}
    (locals : List Λ) (part : Λ → I → Option V) : Prop :=
  ∃ g, Represents locals part g

/-- Every global coordinate is specified by at least one local subsystem. -/
def CoversCoordinates {Λ I V : Type*}
    (locals : List Λ) (part : Λ → I → Option V) : Prop :=
  ∀ i, ∃ l, l ∈ locals ∧ ∃ v, part l i = some v

/-- Construct a canonical global assignment from a family of local
values, using a default only at unspecified coordinates. The choice
is coherent precisely when overlaps agree. -/
def canonical {Λ I V : Type*} [Inhabited V]
    (locals : List Λ) (part : Λ → I → Option V) (i : I) : V := by
  classical
  exact if h : ∃ v : V, ∃ l, l ∈ locals ∧ part l i = some v
    then Classical.choose h else default

theorem canonical_respects {Λ I V : Type*} [Inhabited V]
    (locals : List Λ) (part : Λ → I → Option V)
    (hc : PairwiseCompatible locals part)
    (l : Λ) (hl : l ∈ locals) (i : I) (v : V)
    (hv : part l i = some v) :
    canonical locals part i = v := by
  classical
  have hex : ∃ value : V, ∃ m, m ∈ locals ∧ part m i = some value :=
    ⟨v, l, hl, hv⟩
  have hvalue : canonical locals part i = Classical.choose hex := by
    simp only [canonical, dif_pos hex]
  rw [hvalue]
  obtain ⟨m, hm, hmv⟩ := Classical.choose_spec hex
  exact hc m hm l hl i (Classical.choose hex) v hmv hv

/-- Necessity: the same global value cannot equal two different local
values on an overlapping coordinate. -/
theorem gluing_implies_compatibility {Λ I V : Type*}
    (locals : List Λ) (part : Λ → I → Option V)
    (g : I → V) (h : Represents locals part g) :
    PairwiseCompatible locals part := by
  intro l hl m hm i a b ha hb
  exact (h l hl i a ha).symm.trans (h m hm i b hb)

/-- Exact unconstrained gluing criterion, for a nonempty value type. -/
theorem gluing_iff_pairwise_compatible {Λ I V : Type*} [Inhabited V]
    (locals : List Λ) (part : Λ → I → Option V) :
    HasGlue locals part ↔ PairwiseCompatible locals part := by
  constructor
  · rintro ⟨g, h⟩
    exact gluing_implies_compatibility locals part g h
  · intro hc
    exact ⟨canonical locals part,
      fun l hl i v hv => canonical_respects locals part hc l hl i v hv⟩

/-- If all coordinates are covered, an agreeing global assignment is
not only possible but UNIQUE. -/
theorem gluing_unique_under_full_coverage {Λ I V : Type*} [Inhabited V]
    (locals : List Λ) (part : Λ → I → Option V)
    (hc : PairwiseCompatible locals part)
    (hcover : CoversCoordinates locals part)
    (g : I → V) (hg : Represents locals part g) :
    g = canonical locals part := by
  funext i
  obtain ⟨l, hl, v, hv⟩ := hcover i
  calc
    g i = v := hg l hl i v hv
    _ = canonical locals part i :=
      (canonical_respects locals part hc l hl i v hv).symm

/-- Admissible gluing requires the resulting global state to satisfy
an additional global constraint not represented by overlap agreement. -/
def AdmissibleGlue {Λ I V : Type*}
    (locals : List Λ) (part : Λ → I → Option V)
    (valid : (I → V) → Prop) : Prop :=
  ∃ g, Represents locals part g ∧ valid g

theorem admissible_glue_iff {Λ I V : Type*} [Inhabited V]
    (locals : List Λ) (part : Λ → I → Option V)
    (valid : (I → V) → Prop)
    (hcover : CoversCoordinates locals part) :
    AdmissibleGlue locals part valid ↔
      PairwiseCompatible locals part ∧ valid (canonical locals part) := by
  constructor
  · rintro ⟨g, hrep, hvalid⟩
    have hc := gluing_implies_compatibility locals part g hrep
    have heq :=
      gluing_unique_under_full_coverage locals part hc hcover g hrep
    refine ⟨hc, ?_⟩
    simpa only [heq] using hvalid
  · rintro ⟨hc, hvalid⟩
    exact ⟨canonical locals part,
      (fun l hl i v hv => canonical_respects locals part hc l hl i v hv),
      hvalid⟩

/-- A valid global state must also be realizable by the original
operator word language from the actual initial underlying state. -/
def OperationalGlue {Λ I V S Op : Type*}
    (locals : List Λ) (part : Λ → I → Option V)
    (observe : S → I → V)
    (step : Op → S → S) (start : S)
    (valid : (I → V) → Prop) : Prop :=
  ∃ word : List Op,
    Represents locals part (observe (run step word start)) ∧
    valid (observe (run step word start))

/-- Exact simultaneous operational gluing criterion. Under full
coverage it factors into (1) local overlap compatibility,
(2) global admissibility, and (3) reachability of the unique glued
observation by an actual operator word. -/
theorem operational_gluing_iff {Λ I V S Op : Type*} [Inhabited V]
    (locals : List Λ) (part : Λ → I → Option V)
    (observe : S → I → V)
    (step : Op → S → S) (start : S)
    (valid : (I → V) → Prop)
    (hcover : CoversCoordinates locals part) :
    OperationalGlue locals part observe step start valid ↔
      PairwiseCompatible locals part ∧
      valid (canonical locals part) ∧
      ∃ word : List Op,
        observe (run step word start) = canonical locals part := by
  constructor
  · rintro ⟨word, hrep, hvalid⟩
    have hc := gluing_implies_compatibility locals part
      (observe (run step word start)) hrep
    have heq :=
      gluing_unique_under_full_coverage locals part hc hcover
        (observe (run step word start)) hrep
    refine ⟨hc, ?_, ⟨word, heq⟩⟩
    simpa only [heq] using hvalid
  · rintro ⟨hc, hvalid, ⟨word, heq⟩⟩
    refine ⟨word, ?_, ?_⟩
    · rw [heq]
      exact fun l hl i v hv =>
        canonical_respects locals part hc l hl i v hv
    · rw [heq]
      exact hvalid

/-- Distinct local write footprints can be consistent, even though
the actions that produced them have destructive side effects. -/
def disjointWrites (loc i : Fin 2) : Option Bool :=
  if loc = i then some true else none

theorem disjoint_writes_are_compatible :
    PairwiseCompatible ([0, 1] : List (Fin 2)) disjointWrites := by
  intro l hl m hm i a b ha hb
  fin_cases l <;> fin_cases m <;> fin_cases i <;>
    cases a <;> cases b <;>
    simp_all [disjointWrites]

theorem disjoint_writes_cover_coordinates :
    CoversCoordinates ([0, 1] : List (Fin 2)) disjointWrites := by
  intro i
  refine ⟨i, ?_, true, ?_⟩
  · fin_cases i <;> simp
  · simp [disjointWrites]

theorem disjoint_writes_have_glue :
    HasGlue ([0, 1] : List (Fin 2)) disjointWrites := by
  exact (gluing_iff_pairwise_compatible
    ([0, 1] : List (Fin 2)) disjointWrites).mpr
    disjoint_writes_are_compatible

def excludesBoth (g : Fin 2 → Bool) : Prop :=
  ¬ (g 0 = true ∧ g 1 = true)

/-- Even perfectly compatible partial data need not satisfy a
separately imposed global admissibility constraint. -/
theorem disjoint_writes_fail_global_policy :
    ¬ AdmissibleGlue ([0, 1] : List (Fin 2))
      disjointWrites excludesBoth := by
  rintro ⟨g, hg, hpolicy⟩
  have h0 : g 0 = true := hg 0 (by decide) 0 true (by decide)
  have h1 : g 1 = true := hg 1 (by decide) 1 true (by decide)
  exact hpolicy ⟨h0, h1⟩

def pairReadout (state : Bool × Bool) (i : Fin 2) : Bool :=
  if i = 0 then state.1 else state.2

/-- Reported FULL states after the destructive primitives overlap
with conflicting values. Their full outcomes cannot be glued. -/
def destructiveSnapshots (loc i : Fin 2) : Option Bool :=
  some (pairReadout (destructive loc (false, false)) i)

theorem destructive_full_snapshots_conflict :
    ¬ PairwiseCompatible ([0, 1] : List (Fin 2))
      destructiveSnapshots := by
  intro hc
  have hcontr : true = false :=
    hc 0 (by decide) 1 (by decide) 0 true false
      (by decide) (by decide)
  cases hcontr

theorem destructive_full_snapshots_have_no_glue :
    ¬ HasGlue ([0, 1] : List (Fin 2))
      destructiveSnapshots := by
  rintro ⟨g, hg⟩
  exact destructive_full_snapshots_conflict
    (gluing_implies_compatibility
      ([0, 1] : List (Fin 2)) destructiveSnapshots g hg)

/-- Unspecified destructive side effects can be hidden by partial
reports: compatible local success reports do not imply a reachable
joint state in the actual destructive operator algebra. -/
theorem disjoint_writes_not_operationally_gluable_destructively :
    ¬ OperationalGlue ([0, 1] : List (Fin 2))
      disjointWrites pairReadout destructive (false, false)
      (fun _ => True) := by
  rintro ⟨word, hrep, _⟩
  have h0 : (run destructive word (false, false)).1 = true := by
    simpa [pairReadout] using
      (hrep 0 (by decide) 0 true (by decide))
  have h1 : (run destructive word (false, false)).2 = true := by
    simpa [pairReadout] using
      (hrep 1 (by decide) 1 true (by decide))
  exact collective_coverage_does_not_glue.2
    ⟨word, ⟨h0, h1⟩⟩

theorem disjoint_writes_operationally_gluable_cumulatively :
    OperationalGlue ([0, 1] : List (Fin 2))
      disjointWrites pairReadout cumulative (false, false)
      (fun _ => True) := by
  refine ⟨[0, 1], ?_, trivial⟩
  intro l hl i v hv
  fin_cases l <;> fin_cases i <;> cases v <;>
    simp_all [disjointWrites, pairReadout, run, cumulative]

end LinearInputParallelGluing
