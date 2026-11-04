/-!
# Finite self-modification of object-level operator rules

PR #62 reused a fixed child function. Here the mutable state includes
both known operator descriptors and an explicit rule-edge table.
Learning a descriptor calls a fixed meta-compiler to modify that table.
Thus the rule *data* changes internally, but the meta-compiler is fixed.

The frozen-rule control has the same learned descriptors but cannot
advance. The modified-rule machine can advance, then saturates.
No unbounded growth or autonomous discovery of a new meta-compiler.
-/

section

namespace LinearInputRuleSelfModification

open LinearInputOperatorWords
open LinearInputOperatorRefinement
open LinearInputSemanticIntervals
open LinearInputFiniteSelfSynthesis
open LinearInputRecursiveReentry

structure RuleMachine (α : Type*) where
  known : List α
  edges : List (α × α)
deriving DecidableEq

def children {α : Type*} [DecidableEq α]
    (s : RuleMachine α) (x : α) : List α :=
  s.edges.filterMap (fun e => if e.1 = x then some e.2 else none)

def frontier {α : Type*} [DecidableEq α]
    (s : RuleMachine α) : List α :=
  novelFrontier (children s) s.known

/-- Generated operator descriptors also install new generation edges. -/
def modifyStep {α : Type*} [DecidableEq α]
    (compile : α → List (α × α)) (viable : α → Bool)
    (s : RuleMachine α) : Option (RuleMachine α) :=
  (chooseTarget (frontier s) viable).map (fun target =>
    { known := s.known ++ [target], edges := s.edges ++ compile target })

theorem modifyStep_sound {α : Type*} [DecidableEq α]
    (compile : α → List (α × α)) (viable : α → Bool)
    (s next : RuleMachine α)
    (h : modifyStep compile viable s = some next) :
    ∃ target, target ∈ frontier s ∧ target ∉ s.known ∧
      viable target = true ∧
      next.known = s.known ++ [target] ∧
      next.edges = s.edges ++ compile target := by
  unfold modifyStep at h
  cases hc : chooseTarget (frontier s) viable with
  | none =>
      simp [hc] at h
  | some target =>
      have heq : next =
          { known := s.known ++ [target],
            edges := s.edges ++ compile target } := by
        simpa [hc] using h.symm
      obtain ⟨hfront, hv⟩ :=
        chooseTarget_sound (frontier s) viable target hc
      have hnew : target ∉ s.known :=
        ((novelFrontier_mem_iff (children s) s.known target).mp hfront).2
      exact ⟨target, hfront, hnew, hv,
        congrArg RuleMachine.known heq, congrArg RuleMachine.edges heq⟩

theorem modifyStep_strict_growth {α : Type*} [DecidableEq α]
    (compile : α → List (α × α)) (viable : α → Bool)
    (s next : RuleMachine α)
    (h : modifyStep compile viable s = some next) :
    s.known.length < next.known.length := by
  obtain ⟨t, _, _, _, ht, _⟩ := modifyStep_sound compile viable s next h
  rw [ht]
  simp

theorem modifyStep_preserves_known {α : Type*} [DecidableEq α]
    (compile : α → List (α × α)) (viable : α → Bool)
    (s next : RuleMachine α)
    (h : modifyStep compile viable s = some next)
    (x : α) (hx : x ∈ s.known) : x ∈ next.known := by
  obtain ⟨t, _, _, _, ht, _⟩ := modifyStep_sound compile viable s next h
  rw [ht]
  exact List.mem_append.mpr (Or.inl hx)

theorem modifyStep_preserves_edges {α : Type*} [DecidableEq α]
    (compile : α → List (α × α)) (viable : α → Bool)
    (s next : RuleMachine α)
    (h : modifyStep compile viable s = some next)
    (e : α × α) (he : e ∈ s.edges) : e ∈ next.edges := by
  obtain ⟨t, _, _, _, _, ht⟩ := modifyStep_sound compile viable s next h
  rw [ht]
  exact List.mem_append.mpr (Or.inl he)

theorem modifyStep_complete {α : Type*} [DecidableEq α]
    (compile : α → List (α × α)) (viable : α → Bool)
    (s : RuleMachine α)
    (h : ∃ t, t ∈ frontier s ∧ viable t = true) :
    ∃ next, modifyStep compile viable s = some next := by
  obtain ⟨t, ht⟩ := chooseTarget_complete (frontier s) viable h
  exact ⟨{ known := s.known ++ [t], edges := s.edges ++ compile t },
    by simp [modifyStep, ht]⟩

theorem modifyStep_none_certificate {α : Type*} [DecidableEq α]
    (compile : α → List (α × α)) (viable : α → Bool)
    (s : RuleMachine α)
    (h : modifyStep compile viable s = none) :
    ∀ t, t ∈ frontier s → viable t = false := by
  have hc : chooseTarget (frontier s) viable = none := by
    unfold modifyStep at h
    cases hh : chooseTarget (frontier s) viable with
    | none => rfl
    | some t => simp [hh] at h
  exact chooseTarget_none_exhaustive (frontier s) viable hc

/-- Rule-table modification is necessary for reactivation if the
known descriptor set and viability predicate have not changed. -/
theorem reactivation_requires_rule_edit {α : Type*} [DecidableEq α]
    (compile : α → List (α × α)) (viable : α → Bool)
    (stalled active : RuleMachine α)
    (hstop : modifyStep compile viable stalled = none)
    (hgo : ∃ next, modifyStep compile viable active = some next)
    (hk : stalled.known = active.known) :
    stalled.edges ≠ active.edges := by
  intro he
  have heq : stalled = active := by
    cases stalled with
    | mk k e =>
        cases active with
        | mk k' e' =>
            cases hk
            cases he
            rfl
  obtain ⟨next, hn⟩ := hgo
  rw [← heq] at hn
  rw [hstop] at hn
  cases hn

/-- A successful rule-modified primitive can be an indispensable
one-step repair, under the separate extinction/viability assumptions. -/
theorem modified_rule_repair_survives {α σ ι : Type*} [DecidableEq α]
    (compile : α → List (α × α))
    (alive : ℕ → σ → α → Prop) (region : α → Prop)
    (old : ι → α → α) (start : α)
    (s next : RuleMachine α) (locals : List σ)
    (accepts : σ → α → Bool)
    (hmatch : ∀ x, (∃ loc, loc ∈ locals ∧ accepts loc x = true) ↔
      HasLocal alive 1 x)
    (hi : OldInvariant region old) (hx : region start)
    (he : TerminalExtinction alive region 1)
    (hzero : HasLocal alive 0 start)
    (hstep : modifyStep compile (someLocal locals accepts) s = some next) :
    ∃ target, target ∈ frontier s ∧ target ∉ s.known ∧
      IntervalSurvival alive
        (sumStep old (fun _ : Unit => patch start target))
        [Sum.inr ()] start ∧
      (∀ word : List ι, run old word start ≠ patch start target start) := by
  obtain ⟨t, hf, hn, hv, _, _⟩ :=
    modifyStep_sound compile (someLocal locals accepts) s next hstep
  have hlocal : HasLocal alive 1 t :=
    (hmatch t).mp ((someLocal_spec locals accepts t).mp hv)
  have hterminal : HasLocal alive 1 (patch start t start) := by
    simpa [patch] using hlocal
  exact ⟨t, hf, hn,
    one_step_interval alive
      (sumStep old (fun _ : Unit => patch start t))
      (Sum.inr ()) start hzero hterminal,
    viable_repair_not_old_generated alive region old 1 start
      hi hx he (patch start t) hterminal⟩

/-- Iteration changes both descriptors and the installed rule table. -/
def iterateMachine {α : Type*} [DecidableEq α]
    (compile : α → List (α × α)) (viable : α → Bool) :
    ℕ → RuleMachine α → RuleMachine α
  | 0, s => s
  | n + 1, s =>
      match modifyStep compile viable s with
      | none => s
      | some next => iterateMachine compile viable n next

theorem iterateMachine_stops {α : Type*} [DecidableEq α]
    (compile : α → List (α × α)) (viable : α → Bool)
    (s : RuleMachine α) (n : ℕ)
    (hn : modifyStep compile viable s = none) :
    iterateMachine compile viable n s = s := by
  cases n with
  | zero => rfl
  | succ n => simp [iterateMachine, hn]

/-- A finite fixed meta-compiler can install new object-level rules. -/
def bootCompiler (t : Fin 4) : List (Fin 4 × Fin 4) :=
  if t = 1 then [(1, 2)]
  else if t = 2 then [(2, 3)]
  else []

def bootViable (_ : Fin 4) : Bool := true

def seed : RuleMachine (Fin 4) := ⟨[0], [(0, 1)]⟩
def stage1 : RuleMachine (Fin 4) := ⟨[0, 1], [(0, 1), (1, 2)]⟩
def stage2 : RuleMachine (Fin 4) :=
  ⟨[0, 1, 2], [(0, 1), (1, 2), (2, 3)]⟩
def stage3 : RuleMachine (Fin 4) :=
  ⟨[0, 1, 2, 3], [(0, 1), (1, 2), (2, 3)]⟩
def frozen : RuleMachine (Fin 4) := ⟨[0, 1], [(0, 1)]⟩

theorem boot_first : modifyStep bootCompiler bootViable seed = some stage1 := by
  decide
theorem boot_second : modifyStep bootCompiler bootViable stage1 = some stage2 := by
  decide
theorem boot_third : modifyStep bootCompiler bootViable stage2 = some stage3 := by
  decide
theorem boot_saturated : modifyStep bootCompiler bootViable stage3 = none := by
  decide
theorem frozen_stalls : modifyStep bootCompiler bootViable frozen = none := by
  decide

theorem boot_rule_edit_necessary : frozen.edges ≠ stage1.edges := by
  exact reactivation_requires_rule_edit bootCompiler bootViable
    frozen stage1 frozen_stalls ⟨stage2, boot_second⟩ rfl

theorem boot_three_rounds :
    iterateMachine bootCompiler bootViable 3 seed = stage3 := by
  decide

theorem boot_after_saturation (n : ℕ) :
    iterateMachine bootCompiler bootViable n stage3 = stage3 :=
  iterateMachine_stops bootCompiler bootViable stage3 n boot_saturated

end LinearInputRuleSelfModification
