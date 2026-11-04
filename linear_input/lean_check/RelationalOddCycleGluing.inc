/-!
# Relational constraints: pairwise feasibility does not imply gluing

PR #69 proves that separate local operations can fulfill different
requirements without a common reachable state. Fixed partial-write
proposals admit a stronger overlap-agreement gluing criterion, but
general local RELATIONAL constraints need not.

We prove a strict logical hierarchy:
  common global witness => pairwise common witnesses => individual ones.
Both reverse implications fail in small finite constructive models.
The decisive counterexample is the odd three-cycle of Boolean
disequality relations: every two local relations admit a shared global
assignment, but all three do not.

This is NOT the pairwise overlap-compatibility criterion for concrete
partial assignments; pairwise SAT can use a different whole state
for each tested pair. The old history is not assumed preserved, and
absence of a global witness alone does not imply local extinction.
-/

section

namespace LinearInputRelationalGluing

/-- Local constraint systems indexed by a set of observers/operations. -/
def IndividuallyFeasible {I S : Type*}
    (condition : I → S → Prop) : Prop :=
  ∀ i, ∃ s, condition i s

/-- Each PAIR has a joint witness, which may depend on the pair. -/
def PairwiseFeasible {I S : Type*}
    (condition : I → S → Prop) : Prop :=
  ∀ i j, ∃ s, condition i s ∧ condition j s

/-- One global witness satisfies ALL indexed local constraints. -/
def GloballyFeasible {I S : Type*}
    (condition : I → S → Prop) : Prop :=
  ∃ s, ∀ i, condition i s

theorem global_implies_pairwise {I S : Type*}
    (condition : I → S → Prop)
    (h : GloballyFeasible condition) :
    PairwiseFeasible condition := by
  obtain ⟨s, hs⟩ := h
  intro i j
  exact ⟨s, hs i, hs j⟩

theorem pairwise_implies_individual {I S : Type*}
    (condition : I → S → Prop)
    (h : PairwiseFeasible condition) :
    IndividuallyFeasible condition := by
  intro i
  obtain ⟨s, hi, _⟩ := h i i
  exact ⟨s, hi⟩

theorem global_implies_individual {I S : Type*}
    (condition : I → S → Prop)
    (h : GloballyFeasible condition) :
    IndividuallyFeasible condition :=
  pairwise_implies_individual condition
    (global_implies_pairwise condition h)

/-- First strict counterexample: contradictory exact Boolean values.
Each local request is individually satisfiable; the pair is not. -/
def Opposing (i : Fin 2) (s : Bool) : Prop :=
  if i = 0 then s = true else s = false

theorem opposing_individually_feasible :
    IndividuallyFeasible Opposing := by
  intro i
  fin_cases i
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

theorem opposing_not_pairwise :
    ¬ PairwiseFeasible Opposing := by
  intro h
  obtain ⟨s, htrue, hfalse⟩ := h (0 : Fin 2) (1 : Fin 2)
  have ht : s = true := by simpa [Opposing] using htrue
  have hf : s = false := by simpa [Opposing] using hfalse
  have hab : true = false := ht.symm.trans hf
  cases hab

theorem individual_does_not_imply_pairwise :
    IndividuallyFeasible Opposing ∧
      ¬ PairwiseFeasible Opposing :=
  ⟨opposing_individually_feasible, opposing_not_pairwise⟩

/-- Each local relation demands a different bit on an edge of an
odd three-cycle. The shared state is one assignment of three bits. -/
def OddCycleEdge (edge : Fin 3) (s : Fin 3 → Bool) : Prop :=
  if edge = 0 then s 0 ≠ s 1
  else if edge = 1 then s 1 ≠ s 2
  else s 2 ≠ s 0

/-- Individual local constraints can be realized by finite assignments. -/
theorem odd_cycle_each_locally_possible :
    IndividuallyFeasible OddCycleEdge := by
  exact pairwise_implies_individual OddCycleEdge
    (by decide : PairwiseFeasible OddCycleEdge)

/-- Every pair of relation constraints has a common global assignment,
but the witness is allowed to depend on the pair. -/
theorem odd_cycle_pairwise_feasible :
    PairwiseFeasible OddCycleEdge := by
  decide

/-- Three Boolean "must differ" edges cannot be realized by a single
assignment on an odd cycle. -/
theorem odd_cycle_not_globally_feasible :
    ¬ GloballyFeasible OddCycleEdge := by
  decide

theorem pairwise_feasibility_does_not_imply_global :
    PairwiseFeasible OddCycleEdge ∧
      ¬ GloballyFeasible OddCycleEdge :=
  ⟨odd_cycle_pairwise_feasible,
   odd_cycle_not_globally_feasible⟩

/-- A sharper result: the identical three-variable state space
supports each pair, but requires contradictory global constraints. -/
theorem every_two_compatible_but_three_incompatible :
    (∀ i j : Fin 3, ∃ s : Fin 3 → Bool,
      OddCycleEdge i s ∧ OddCycleEdge j s) ∧
    ¬ ∃ s : Fin 3 → Bool, ∀ i : Fin 3, OddCycleEdge i s :=
  pairwise_feasibility_does_not_imply_global

/-- The odd-cycle obstruction is not an effect of having three
constraints alone: an even cycle admits a valid two-colouring. -/
def EvenCycleEdge (edge : Fin 4) (s : Fin 4 → Bool) : Prop :=
  if edge = 0 then s 0 ≠ s 1
  else if edge = 1 then s 1 ≠ s 2
  else if edge = 2 then s 2 ≠ s 3
  else s 3 ≠ s 0

theorem even_cycle_globally_feasible :
    GloballyFeasible EvenCycleEdge := by
  decide

theorem even_cycle_pairwise_feasible :
    PairwiseFeasible EvenCycleEdge :=
  global_implies_pairwise EvenCycleEdge even_cycle_globally_feasible

/-- An independently supplied positive global state is enough to
glue all relations: this is the exact global requirement, distinct
from pairwise testing. -/
theorem global_gluing_iff_one_common_witness {I S : Type*}
    (condition : I → S → Prop) :
    GloballyFeasible condition ↔
      ∃ s : S, ∀ i, condition i s := by
  rfl

end LinearInputRelationalGluing
