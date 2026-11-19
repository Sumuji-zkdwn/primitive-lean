/-! The one-channel threshold-3 Economy from PR #145, with disabled actions
totalized as self-loops. Its 32 states are unchanged by adding make-chair.
The Python checker compares every nontrivial transition to the upstream model. -/
namespace Elastica.ChairInternalGeneration

open LinearInputOperatorReachability LinearInputProjectionReachability
open Elastica.ChairPieProjection Elastica.ChairPieKillSpot

inductive Gate | chair | demand deriving DecidableEq, Repr
inductive Internal | grow | sale deriving DecidableEq, Repr

structure State where
  capability : Fin 4
  chair : Bool
  demand : Bool
  paid : Bool
  deriving DecidableEq, Repr

def initial : State := ⟨0, false, false, false⟩
def goal (s : State) : Prop := s.paid = true

def oldStep : (Internal ⊕ Gate) → State → State
  | .inl .grow, s =>
      {s with capability := ⟨min 3 (s.capability.val + 1), by omega⟩}
  | .inl .sale, s =>
      if s.capability = 3 ∧ s.chair = true ∧ s.demand = true
      then {s with paid := true} else s
  | .inr .chair, s => {s with chair := true}
  | .inr .demand, s => {s with demand := true}

def newStep : ((Internal ⊕ Unit) ⊕ Gate) → State → State
  | .inl (.inl i), s => oldStep (.inl i) s
  | .inl (.inr _), s => if s.capability = 3 then {s with chair := true} else s
  | .inr g, s => oldStep (.inr g) s

private def oldInv (A : Finset Gate) (s : State) : Prop :=
  (s.chair = true → Gate.chair ∈ A) ∧
  (s.demand = true → Gate.demand ∈ A) ∧
  (s.paid = true → Gate.chair ∈ A ∧ Gate.demand ∈ A)

private theorem old_stable (A : Finset Gate) :
    Stable (permittedStep oldStep A) (oldInv A) := by
  rintro ⟨a, ha⟩ s ⟨hc, hd, hp⟩
  cases a with
  | inl i =>
      cases i with
      | grow => exact ⟨hc, hd, hp⟩
      | sale =>
          change oldInv A (if s.capability = 3 ∧ s.chair = true ∧ s.demand = true
            then {s with paid := true} else s)
          split_ifs with h
          · exact ⟨hc, hd, fun _ => ⟨hc h.2.1, hd h.2.2⟩⟩
          · exact ⟨hc, hd, hp⟩
  | inr g =>
      have hg : g ∈ A := ha (.inr g) (by simp)
      cases g with
      | chair => exact ⟨fun _ => hg, hd, hp⟩
      | demand => exact ⟨hc, fun _ => hg, hp⟩

/-- Exact permission predicate of the old threshold-3 one-channel model. -/
theorem old_possible_iff (A : Finset Gate) :
    RevenuePossible oldStep initial goal A ↔ Gate.chair ∈ A ∧ Gate.demand ∈ A := by
  constructor
  · intro h
    obtain ⟨s, hs, hg⟩ := (revenue_iff_reachable oldStep A initial goal).mp h
    have hi := reachable_preserves_invariant (permittedStep oldStep A) (oldInv A)
      (old_stable A) hs (by simp [oldInv, initial])
    exact hi.2.2 hg
  · rintro ⟨hc, hd⟩
    refine ⟨[.inl .grow, .inl .grow, .inl .grow,
      .inr .chair, .inr .demand, .inl .sale], ?_, ?_⟩
    · simp [Allowed, hc, hd]
    · rfl

private def newInv (A : Finset Gate) (s : State) : Prop :=
  (s.demand = true → Gate.demand ∈ A) ∧ (s.paid = true → Gate.demand ∈ A)

private theorem new_stable (A : Finset Gate) :
    Stable (permittedStep newStep A) (newInv A) := by
  rintro ⟨a, ha⟩ s ⟨hd, hp⟩
  cases a with
  | inl j =>
      cases j with
      | inl i =>
          cases i with
          | grow => exact ⟨hd, hp⟩
          | sale =>
              change newInv A (if s.capability = 3 ∧ s.chair = true ∧ s.demand = true
                then {s with paid := true} else s)
              split_ifs with h
              · exact ⟨hd, fun _ => hd h.2.2⟩
              · exact ⟨hd, hp⟩
      | inr _ =>
          change newInv A (if s.capability = 3 then {s with chair := true} else s)
          split_ifs <;> exact ⟨hd, hp⟩
  | inr g =>
      have hg : g ∈ A := ha (.inr g) (by simp)
      cases g with
      | chair => exact ⟨hd, hp⟩
      | demand => exact ⟨fun _ => hg, hp⟩

/-- Internal generation removes the chair permission requirement, but does
not remove the remaining abstract demand permission. -/
theorem new_possible_iff (A : Finset Gate) :
    RevenuePossible newStep initial goal A ↔ Gate.demand ∈ A := by
  constructor
  · intro h
    obtain ⟨s, hs, hg⟩ := (revenue_iff_reachable newStep A initial goal).mp h
    have hi := reachable_preserves_invariant (permittedStep newStep A) (newInv A)
      (new_stable A) hs (by simp [newInv, initial])
    exact hi.2 hg
  · intro hd
    refine ⟨[.inl (.inl .grow), .inl (.inl .grow), .inl (.inl .grow),
      .inl (.inr ()), .inr .demand, .inl (.inl .sale)], ?_, ?_⟩
    · simp [Allowed, hd]
    · rfl

theorem same_permissions_separate :
    ¬ RevenuePossible oldStep initial goal {Gate.demand} ∧
      RevenuePossible newStep initial goal {Gate.demand} := by
  constructor
  · rw [old_possible_iff]
    simp
  · rw [new_possible_iff]
    simp

theorem no_external_success : ¬ RevenuePossible newStep initial goal ∅ := by
  rw [new_possible_iff]
  simp

theorem chair_not_simulated :
    ¬ PermissionSimulation oldStep newStep {Gate.demand} {Gate.demand} id := by
  intro h
  exact same_permissions_separate.1
    (revenue_of_permission_simulation oldStep newStep _ _ id initial goal h
      same_permissions_separate.2)

theorem chair_strict_gain :
    StrictGain (permittedStep oldStep {Gate.demand})
      (permittedStep newStep {Gate.demand}) id initial := by
  obtain ⟨s, hs, hg⟩ := (revenue_iff_reachable newStep _ initial goal).mp
    same_permissions_separate.2
  refine ⟨s, hs, ?_⟩
  intro h
  exact same_permissions_separate.1
    ((revenue_iff_reachable oldStep _ initial goal).mpr ⟨s, h, hg⟩)

/-- Every old path is retained for every permission set and every start.
Together with chair_strict_gain, this gives strict inclusion of reachable sets. -/
theorem chair_retains_old (A : Finset Gate) {s t : State}
    (h : Reachable (permittedStep oldStep A) s t) :
    Reachable (permittedStep newStep A) s t := by
  apply projection_reachable (permittedStep newStep A) (permittedStep oldStep A) id ?_ h
  rintro ⟨a, ha⟩ y
  cases a with
  | inl i => exact ⟨[⟨.inl (.inl i), by simp [Allowed]⟩], rfl⟩
  | inr g =>
      have hg : g ∈ A := ha (.inr g) (by simp)
      exact ⟨[⟨.inr g, by simp [Allowed, hg]⟩], rfl⟩

/-- Internal generation can be simulated if the old external chair action
is actually allowed. The old word may be empty below the capability threshold. -/
theorem chair_simulated_when_chair_available (A : Finset Gate)
    (hc : Gate.chair ∈ A) : PermissionSimulation oldStep newStep A A id := by
  rintro ⟨a, ha⟩ s
  cases a with
  | inl j =>
      cases j with
      | inl i =>
          exact ⟨[⟨.inl i, by simp [Allowed]⟩], rfl⟩
      | inr _ =>
          by_cases h : s.capability = 3
          · refine ⟨[⟨.inr Gate.chair, by simp [Allowed, hc]⟩], ?_⟩
            simp [LinearInputOperatorWords.run, permittedStep, newStep, oldStep, h]
          · refine ⟨[], ?_⟩
            simp [LinearInputOperatorWords.run, permittedStep, newStep, h]
  | inr g =>
      have hg : g ∈ A := ha (.inr g) (by simp)
      exact ⟨[⟨.inr g, by simp [Allowed, hg]⟩], rfl⟩

end Elastica.ChairInternalGeneration
