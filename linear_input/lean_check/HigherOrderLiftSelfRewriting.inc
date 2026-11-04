/-!
# Finite higher-order lift rewriting

The machine stores its lift program as finite data. A newly learned operator
may install another lift rule through the machine's finite edit table. The
interpreter and the edit table remain fixed in this experiment.
-/

section

namespace LinearInputHigherOrderLiftSelfRewriting

open LinearInputOperatorWords
open LinearInputOperatorRefinement
open LinearInputFiniteSelfSynthesis
open LinearInputRuleSelfModification
open LinearInputMetaRuleExtension

abbrev HigherMetaRule (α : Type*) := α × (α × α)
abbrev HigherLiftRule (α : Type*) := α × HigherMetaRule α
abbrev HigherLiftEdit (α : Type*) := α × HigherLiftRule α

structure HigherMachine (α : Type*) where
  known : List α
  edges : List (α × α)
  metaRules : List (HigherMetaRule α)
  liftRules : List (HigherLiftRule α)
  liftEdits : List (HigherLiftEdit α)
deriving DecidableEq

def lower {α : Type*} (s : HigherMachine α) :
    LinearInputMetaRuleExtension.MetaMachine α :=
  ⟨s.known, s.edges, s.metaRules⟩

def higherFrontier {α : Type*} [DecidableEq α]
    (s : HigherMachine α) : List α :=
  LinearInputRuleSelfModification.frontier
    (⟨s.known, s.edges⟩ :
      LinearInputRuleSelfModification.RuleMachine α)

/-- Apply the machine-resident edit table to its current lift program. -/
def applyLiftEdits {α : Type*} [DecidableEq α]
    (edits : List (HigherLiftEdit α))
    (rules : List (HigherLiftRule α)) (learned : α) :
    List (HigherLiftRule α) :=
  rules ++ edits.filterMap (fun edit =>
    if edit.1 = learned then some edit.2 else none)

/-- Interpret the current lift program as a finite table of meta-rule outputs. -/
def runLift {α : Type*} [DecidableEq α]
    (rules : List (HigherLiftRule α)) (learned : α) :
    List (HigherMetaRule α) :=
  rules.filterMap (fun rule =>
    if rule.1 = learned then some rule.2 else none)

/-- The fixed interpreter executes a state-resident, mutable lift program.
The new meta rules enter state now; object edges for this transition still
use the pre-step meta-rule table, preserving PR #64's update order. -/
def higherStep {α : Type*} [DecidableEq α]
    (viable : α → Bool) (s : HigherMachine α) :
    Option (HigherMachine α) :=
  (LinearInputFiniteSelfSynthesis.chooseTarget
    (higherFrontier s) viable).map (fun target =>
      let nextLiftRules :=
        applyLiftEdits s.liftEdits s.liftRules target
      let nextMetaRules :=
        s.metaRules ++ runLift nextLiftRules target
      { known := s.known ++ [target],
        edges := s.edges ++
          LinearInputMetaRuleExtension.interpretMeta
            s.metaRules target,
        metaRules := nextMetaRules,
        liftRules := nextLiftRules,
        liftEdits := s.liftEdits })

theorem higherStep_sound {α : Type*} [DecidableEq α]
    (viable : α → Bool) (s next : HigherMachine α)
    (h : higherStep viable s = some next) :
    ∃ target, target ∈ higherFrontier s ∧ target ∉ s.known ∧
      viable target = true ∧
      next.known = s.known ++ [target] ∧
      next.liftRules = applyLiftEdits s.liftEdits s.liftRules target ∧
      next.metaRules =
        s.metaRules ++ runLift
          (applyLiftEdits s.liftEdits s.liftRules target) target ∧
      next.edges = s.edges ++
        LinearInputMetaRuleExtension.interpretMeta
          s.metaRules target ∧
      next.liftEdits = s.liftEdits := by
  unfold higherStep at h
  cases hc : LinearInputFiniteSelfSynthesis.chooseTarget
      (higherFrontier s) viable with
  | none =>
      simp [hc] at h
  | some target =>
      have heq : next =
          { known := s.known ++ [target],
            edges := s.edges ++
              LinearInputMetaRuleExtension.interpretMeta
                s.metaRules target,
            metaRules := s.metaRules ++ runLift
              (applyLiftEdits s.liftEdits s.liftRules target)
              target,
            liftRules :=
              applyLiftEdits s.liftEdits s.liftRules target,
            liftEdits := s.liftEdits } := by
        simpa [hc, applyLiftEdits, runLift] using h.symm
      obtain ⟨hfront, hv⟩ :=
        LinearInputFiniteSelfSynthesis.chooseTarget_sound
          (higherFrontier s) viable target hc
      have hnew : target ∉ s.known :=
        ((LinearInputRecursiveReentry.novelFrontier_mem_iff
          (LinearInputRuleSelfModification.children
            (⟨s.known, s.edges⟩ :
              LinearInputRuleSelfModification.RuleMachine α))
          s.known target).mp hfront).2
      have hknown : next.known = s.known ++ [target] := by
        simp [heq]
      have hlift : next.liftRules =
          applyLiftEdits s.liftEdits s.liftRules target := by
        simp [heq]
      have hmeta : next.metaRules =
          s.metaRules ++ runLift
            (applyLiftEdits s.liftEdits s.liftRules target) target := by
        simp [heq]
      have hedges : next.edges = s.edges ++
          LinearInputMetaRuleExtension.interpretMeta s.metaRules target := by
        simp [heq]
      have hedits : next.liftEdits = s.liftEdits := by
        simp [heq]
      exact ⟨target, hfront, hnew, hv, hknown, hlift,
        hmeta, hedges, hedits⟩

theorem higherStep_strict_growth {α : Type*} [DecidableEq α]
    (viable : α → Bool) (s next : HigherMachine α)
    (h : higherStep viable s = some next) :
    s.known.length < next.known.length := by
  obtain ⟨target, _, _, _, hk, _, _, _, _⟩ :=
    higherStep_sound viable s next h
  rw [hk]
  simp

theorem higherStep_preserves_known {α : Type*} [DecidableEq α]
    (viable : α → Bool) (s next : HigherMachine α)
    (h : higherStep viable s = some next)
    (x : α) (hx : x ∈ s.known) : x ∈ next.known := by
  obtain ⟨target, _, _, _, hk, _, _, _, _⟩ :=
    higherStep_sound viable s next h
  rw [hk]
  exact List.mem_append.mpr (Or.inl hx)

theorem higherStep_preserves_edges {α : Type*} [DecidableEq α]
    (viable : α → Bool) (s next : HigherMachine α)
    (h : higherStep viable s = some next)
    (edge : α × α) (hedge : edge ∈ s.edges) :
    edge ∈ next.edges := by
  obtain ⟨target, _, _, _, _, _, _, he, _⟩ :=
    higherStep_sound viable s next h
  rw [he]
  exact List.mem_append.mpr (Or.inl hedge)

theorem higherStep_preserves_meta {α : Type*} [DecidableEq α]
    (viable : α → Bool) (s next : HigherMachine α)
    (h : higherStep viable s = some next)
    (rule : HigherMetaRule α) (hrule : rule ∈ s.metaRules) :
    rule ∈ next.metaRules := by
  obtain ⟨target, _, _, _, _, _, hm, _, _⟩ :=
    higherStep_sound viable s next h
  rw [hm]
  exact List.mem_append.mpr (Or.inl hrule)

theorem higherStep_preserves_liftRules {α : Type*} [DecidableEq α]
    (viable : α → Bool) (s next : HigherMachine α)
    (h : higherStep viable s = some next)
    (rule : HigherLiftRule α) (hrule : rule ∈ s.liftRules) :
    rule ∈ next.liftRules := by
  obtain ⟨target, _, _, _, _, hl, _, _, _⟩ :=
    higherStep_sound viable s next h
  rw [hl]
  exact List.mem_append.mpr (Or.inl hrule)

theorem higherStep_preserves_liftEdits {α : Type*} [DecidableEq α]
    (viable : α → Bool) (s next : HigherMachine α)
    (h : higherStep viable s = some next) :
    next.liftEdits = s.liftEdits := by
  obtain ⟨target, _, _, _, _, _, _, _, he⟩ :=
    higherStep_sound viable s next h
  exact he

theorem higherStep_complete {α : Type*} [DecidableEq α]
    (viable : α → Bool) (s : HigherMachine α)
    (hex : ∃ target, target ∈ higherFrontier s ∧
      viable target = true) :
    ∃ next, higherStep viable s = some next := by
  obtain ⟨target, ht⟩ :=
    LinearInputFiniteSelfSynthesis.chooseTarget_complete
      (higherFrontier s) viable hex
  refine ⟨{
    known := s.known ++ [target],
    edges := s.edges ++
      LinearInputMetaRuleExtension.interpretMeta
        s.metaRules target,
    metaRules := s.metaRules ++ runLift
      (applyLiftEdits s.liftEdits s.liftRules target) target,
    liftRules := applyLiftEdits s.liftEdits s.liftRules target,
    liftEdits := s.liftEdits
  }, ?_⟩
  simp [higherStep, ht, applyLiftEdits, runLift]

theorem higherStep_none_certificate {α : Type*} [DecidableEq α]
    (viable : α → Bool) (s : HigherMachine α)
    (h : higherStep viable s = none) :
    ∀ target, target ∈ higherFrontier s →
      viable target = false := by
  have hc : LinearInputFiniteSelfSynthesis.chooseTarget
      (higherFrontier s) viable = none := by
    unfold higherStep at h
    cases hh : LinearInputFiniteSelfSynthesis.chooseTarget
        (higherFrontier s) viable with
    | none => rfl
    | some target => simp [hh] at h
  exact LinearInputFiniteSelfSynthesis.chooseTarget_none_exhaustive
    (higherFrontier s) viable hc

def iterateHigher {α : Type*} [DecidableEq α]
    (viable : α → Bool) : ℕ → HigherMachine α → HigherMachine α
  | 0, s => s
  | n + 1, s =>
      match higherStep viable s with
      | none => s
      | some next => iterateHigher viable n next

theorem iterateHigher_stable_of_none {α : Type*} [DecidableEq α]
    (viable : α → Bool) (s : HigherMachine α) (n : ℕ)
    (h : higherStep viable s = none) :
    iterateHigher viable n s = s := by
  cases n with
  | zero => rfl
  | succ n => simp [iterateHigher, h]

def bootM12 : HigherMetaRule (Fin 4) := (1, (1, 2))
def bootM23 : HigherMetaRule (Fin 4) := (2, (2, 3))
def bootLiftEdit : HigherLiftEdit (Fin 4) :=
  (1, (1, (2, (2, 3))))
def bootViable (_ : Fin 4) : Bool := true

def seed : HigherMachine (Fin 4) :=
  ⟨[0], [(0, 1)], [bootM12], [], [bootLiftEdit]⟩

def stage1 : HigherMachine (Fin 4) :=
  ⟨[0, 1], [(0, 1), (1, 2)], [bootM12, bootM23],
    [(1, bootM23)], [bootLiftEdit]⟩

def stage2 : HigherMachine (Fin 4) :=
  ⟨[0, 1, 2], [(0, 1), (1, 2), (2, 3)],
    [bootM12, bootM23], [(1, bootM23)], [bootLiftEdit]⟩

def stage3 : HigherMachine (Fin 4) :=
  ⟨[0, 1, 2, 3], [(0, 1), (1, 2), (2, 3)],
    [bootM12, bootM23], [(1, bootM23)], [bootLiftEdit]⟩

def frozen1 : HigherMachine (Fin 4) :=
  ⟨[0, 1], [(0, 1), (1, 2)], [bootM12], [], []⟩

def frozen2 : HigherMachine (Fin 4) :=
  ⟨[0, 1, 2], [(0, 1), (1, 2)], [bootM12], [], []⟩

theorem higher_boot_first : higherStep bootViable seed = some stage1 := by
  decide

theorem higher_boot_second : higherStep bootViable stage1 = some stage2 := by
  decide

theorem higher_boot_third : higherStep bootViable stage2 = some stage3 := by
  decide

theorem higher_boot_saturated : higherStep bootViable stage3 = none := by
  decide

theorem higher_boot_frozen_second :
    higherStep bootViable frozen1 = some frozen2 := by
  decide

theorem higher_boot_frozen_stalls :
    higherStep bootViable frozen2 = none := by
  decide

theorem higher_boot_rule_changed :
    seed.liftRules ≠ stage1.liftRules := by
  decide

theorem higher_boot_lower_projection :
    lower stage1 = LinearInputMetaRuleExtension.stage1 ∧
    lower stage2 = LinearInputMetaRuleExtension.stage2 ∧
    lower stage3 = LinearInputMetaRuleExtension.stage3 ∧
    lower frozen1 = LinearInputMetaRuleExtension.frozen1 ∧
    lower frozen2 = LinearInputMetaRuleExtension.frozen2 := by
  decide

theorem higher_boot_three_rounds :
    iterateHigher bootViable 3 seed = stage3 := by
  decide

theorem higher_boot_after_saturation (n : ℕ) :
    iterateHigher bootViable n stage3 = stage3 :=
  iterateHigher_stable_of_none bootViable stage3 n higher_boot_saturated

def observableTargets {α : Type*} [DecidableEq α]
    (s : HigherMachine α) (operator : α) : List α :=
  LinearInputRuleSelfModification.children
    (⟨s.known, s.edges⟩ :
      LinearInputRuleSelfModification.RuleMachine α) operator

def observedBehaviors (s : HigherMachine (Fin 4)) : List (List (Fin 4)) :=
  s.known.map (observableTargets s)

theorem higher_boot_behavior_classes :
    (observedBehaviors stage3).length = 4 ∧
    (observedBehaviors frozen2).length = 3 ∧
    (observedBehaviors stage3).Nodup ∧
    (observedBehaviors frozen2).Nodup := by
  decide

theorem higher_boot_identification_gain :
    (observedBehaviors frozen2).length <
      (observedBehaviors stage3).length := by
  decide

end LinearInputHigherOrderLiftSelfRewriting
