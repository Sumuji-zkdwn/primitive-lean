/-!
# Finite metaRules-rule self-extension

The object-level operator-generation rules are part of the state, as in PR #63.
Here the next higher rule layer is ALSO stored in the machine state. Learning
a descriptor installs new object-level rules according to the current metaRules
table, and modifies that metaRules table according to a fixed higher-order lift.

A frozen-metaRules control holds exactly the same known operators and object
rules, but has different subsequent generation possibilities.
The lift function is fixed: this is not unrestricted self-reproduction.
-/

section

namespace LinearInputMetaRuleExtension

open LinearInputOperatorWords
open LinearInputOperatorRefinement
open LinearInputSemanticIntervals
open LinearInputFiniteSelfSynthesis
open LinearInputRecursiveReentry

structure MetaMachine (α : Type*) where
  known : List α
  edges : List (α × α)
  metaRules : List (α × (α × α))
deriving DecidableEq

def lower {α : Type*} (s : MetaMachine α) :
    LinearInputRuleSelfModification.RuleMachine α :=
  ⟨s.known, s.edges⟩

def frontier {α : Type*} [DecidableEq α]
    (s : MetaMachine α) : List α :=
  LinearInputRuleSelfModification.frontier (lower s)

/-- Interpret a mutable metaRules-rule table as new object-level edges. -/
def interpretMeta {α : Type*} [DecidableEq α]
    (metaRules : List (α × (α × α))) (learned : α) : List (α × α) :=
  metaRules.filterMap (fun e => if e.1 = learned then some e.2 else none)

/-- A fixed lift supplies new *metaRules* rules after a successful learning step. -/
def metaStep {α : Type*} [DecidableEq α]
    (lift : α → List (α × (α × α))) (viable : α → Bool)
    (s : MetaMachine α) : Option (MetaMachine α) :=
  (chooseTarget (frontier s) viable).map (fun t =>
    { known := s.known ++ [t],
      edges := s.edges ++ interpretMeta s.metaRules t,
      metaRules := s.metaRules ++ lift t })

theorem metaStep_sound {α : Type*} [DecidableEq α]
    (lift : α → List (α × (α × α))) (viable : α → Bool)
    (s next : MetaMachine α)
    (h : metaStep lift viable s = some next) :
    ∃ t, t ∈ frontier s ∧ t ∉ s.known ∧ viable t = true ∧
      next.known = s.known ++ [t] ∧
      next.edges = s.edges ++ interpretMeta s.metaRules t ∧
      next.metaRules = s.metaRules ++ lift t := by
  unfold metaStep at h
  cases hc : chooseTarget (frontier s) viable with
  | none =>
      simp [hc] at h
  | some t =>
      have heq : next =
          { known := s.known ++ [t],
            edges := s.edges ++ interpretMeta s.metaRules t,
            metaRules := s.metaRules ++ lift t } := by
        simpa [hc] using h.symm
      obtain ⟨hfront, hv⟩ :=
        chooseTarget_sound (frontier s) viable t hc
      have hnew : t ∉ s.known :=
        ((novelFrontier_mem_iff
          (LinearInputRuleSelfModification.children (lower s))
          s.known t).mp hfront).2
      exact ⟨t, hfront, hnew, hv,
        congrArg MetaMachine.known heq,
        congrArg MetaMachine.edges heq,
        congrArg MetaMachine.metaRules heq⟩

theorem metaStep_strict_growth {α : Type*} [DecidableEq α]
    (lift : α → List (α × (α × α))) (viable : α → Bool)
    (s next : MetaMachine α)
    (h : metaStep lift viable s = some next) :
    s.known.length < next.known.length := by
  obtain ⟨t, _, _, _, hk, _, _⟩ := metaStep_sound lift viable s next h
  rw [hk]
  simp

theorem metaStep_preserves_known {α : Type*} [DecidableEq α]
    (lift : α → List (α × (α × α))) (viable : α → Bool)
    (s next : MetaMachine α)
    (h : metaStep lift viable s = some next)
    (x : α) (hx : x ∈ s.known) : x ∈ next.known := by
  obtain ⟨t, _, _, _, hk, _, _⟩ := metaStep_sound lift viable s next h
  rw [hk]
  exact List.mem_append.mpr (Or.inl hx)

theorem metaStep_preserves_edges {α : Type*} [DecidableEq α]
    (lift : α → List (α × (α × α))) (viable : α → Bool)
    (s next : MetaMachine α)
    (h : metaStep lift viable s = some next)
    (x : α × α) (hx : x ∈ s.edges) : x ∈ next.edges := by
  obtain ⟨t, _, _, _, _, he, _⟩ := metaStep_sound lift viable s next h
  rw [he]
  exact List.mem_append.mpr (Or.inl hx)

theorem metaStep_preserves_meta {α : Type*} [DecidableEq α]
    (lift : α → List (α × (α × α))) (viable : α → Bool)
    (s next : MetaMachine α)
    (h : metaStep lift viable s = some next)
    (x : α × (α × α)) (hx : x ∈ s.metaRules) : x ∈ next.metaRules := by
  obtain ⟨t, _, _, _, _, _, hm⟩ := metaStep_sound lift viable s next h
  rw [hm]
  exact List.mem_append.mpr (Or.inl hx)

theorem metaStep_complete {α : Type*} [DecidableEq α]
    (lift : α → List (α × (α × α))) (viable : α → Bool)
    (s : MetaMachine α)
    (hex : ∃ t, t ∈ frontier s ∧ viable t = true) :
    ∃ next, metaStep lift viable s = some next := by
  obtain ⟨t, ht⟩ := chooseTarget_complete (frontier s) viable hex
  exact ⟨{ known := s.known ++ [t],
           edges := s.edges ++ interpretMeta s.metaRules t,
           metaRules := s.metaRules ++ lift t },
    by simp [metaStep, ht]⟩

theorem metaStep_none_certificate {α : Type*} [DecidableEq α]
    (lift : α → List (α × (α × α))) (viable : α → Bool)
    (s : MetaMachine α)
    (h : metaStep lift viable s = none) :
    ∀ t, t ∈ frontier s → viable t = false := by
  have hc : chooseTarget (frontier s) viable = none := by
    unfold metaStep at h
    cases hh : chooseTarget (frontier s) viable with
    | none => rfl
    | some t => simp [hh] at h
  exact chooseTarget_none_exhaustive (frontier s) viable hc

/-- Same low-level machine and unchanged viability/lift cannot yield
different next lower-level rule tables unless the metaRules table differs. -/
theorem divergent_next_edges_require_meta_difference
    {α : Type*} [DecidableEq α]
    (lift : α → List (α × (α × α))) (viable : α → Bool)
    (s t s' t' : MetaMachine α)
    (hk : s.known = t.known) (he : s.edges = t.edges)
    (hs : metaStep lift viable s = some s')
    (ht : metaStep lift viable t = some t')
    (hdiff : s'.edges ≠ t'.edges) :
    s.metaRules ≠ t.metaRules := by
  intro hm
  have hsame : s = t := by
    cases s with
    | mk sk se sm =>
        cases t with
        | mk tk te tm =>
            cases hk
            cases he
            cases hm
            rfl
  rw [← hsame] at ht
  have hsome : (some s' : Option (MetaMachine α)) = some t' :=
    hs.symm.trans ht
  have hnext : s' = t' := Option.some.inj hsome
  exact hdiff (congrArg MetaMachine.edges hnext)

/-- Bound the number of updates; fail-closed when no new viable operator
is available at the current object-level frontier. -/
def iterateMeta {α : Type*} [DecidableEq α]
    (lift : α → List (α × (α × α))) (viable : α → Bool) :
    ℕ → MetaMachine α → MetaMachine α
  | 0, s => s
  | n + 1, s =>
      match metaStep lift viable s with
      | none => s
      | some next => iterateMeta lift viable n next

theorem iterateMeta_stable_of_none {α : Type*} [DecidableEq α]
    (lift : α → List (α × (α × α))) (viable : α → Bool)
    (s : MetaMachine α) (n : ℕ)
    (hn : metaStep lift viable s = none) :
    iterateMeta lift viable n s = s := by
  cases n with
  | zero => rfl
  | succ n => simp [iterateMeta, hn]

/-- The generated descriptor can also construct a one-step repair
under the independently stated local-extinction hypotheses of PR #60. -/
theorem meta_repair_survives {α σ ι : Type*} [DecidableEq α]
    (lift : α → List (α × (α × α)))
    (alive : ℕ → σ → α → Prop) (region : α → Prop)
    (old : ι → α → α) (start : α)
    (s next : MetaMachine α) (locals : List σ)
    (accepts : σ → α → Bool)
    (hmatch : ∀ x, (∃ loc, loc ∈ locals ∧ accepts loc x = true) ↔
      HasLocal alive 1 x)
    (hi : OldInvariant region old) (hx : region start)
    (he : TerminalExtinction alive region 1)
    (hzero : HasLocal alive 0 start)
    (hstep : metaStep lift (someLocal locals accepts) s = some next) :
    ∃ target, target ∈ frontier s ∧ target ∉ s.known ∧
      IntervalSurvival alive
        (sumStep old (fun _ : Unit => patch start target))
        [Sum.inr ()] start ∧
      (∀ word : List ι, run old word start ≠ patch start target start) := by
  obtain ⟨target, hf, hn, hv, _, _, _⟩ :=
    metaStep_sound lift (someLocal locals accepts) s next hstep
  have hlocal : HasLocal alive 1 target :=
    (hmatch target).mp
      ((someLocal_spec locals accepts target).mp hv)
  have hterminal : HasLocal alive 1 (patch start target start) := by
    simpa [patch] using hlocal
  exact ⟨target, hf, hn,
    one_step_interval alive
      (sumStep old (fun _ : Unit => patch start target))
      (Sum.inr ()) start hzero hterminal,
    viable_repair_not_old_generated alive region old 1 start
      hi hx he (patch start target) hterminal⟩

/-- Finite witness: the first learned descriptor inserts a NEW metaRules rule
that determines which object rule will be installed in the next round. -/
def bootLift (x : Fin 4) : List (Fin 4 × (Fin 4 × Fin 4)) :=
  if x = 1 then [(2, (2, 3))] else []

def bootViable (_ : Fin 4) : Bool := true

def seed : MetaMachine (Fin 4) :=
  ⟨[0], [(0, 1)], [(1, (1, 2))]⟩
def stage1 : MetaMachine (Fin 4) :=
  ⟨[0, 1], [(0, 1), (1, 2)],
    [(1, (1, 2)), (2, (2, 3))]⟩
def stage2 : MetaMachine (Fin 4) :=
  ⟨[0, 1, 2], [(0, 1), (1, 2), (2, 3)],
    [(1, (1, 2)), (2, (2, 3))]⟩
def stage3 : MetaMachine (Fin 4) :=
  ⟨[0, 1, 2, 3], [(0, 1), (1, 2), (2, 3)],
    [(1, (1, 2)), (2, (2, 3))]⟩

/-- Frozen control: same known operators and object rules as stage1,
but without the newly acquired second-order rule. -/
def frozen1 : MetaMachine (Fin 4) :=
  ⟨[0, 1], [(0, 1), (1, 2)], [(1, (1, 2))]⟩
def frozen2 : MetaMachine (Fin 4) :=
  ⟨[0, 1, 2], [(0, 1), (1, 2)], [(1, (1, 2))]⟩

theorem boot_first : metaStep bootLift bootViable seed = some stage1 := by decide
theorem boot_second : metaStep bootLift bootViable stage1 = some stage2 := by decide
theorem boot_third : metaStep bootLift bootViable stage2 = some stage3 := by decide
theorem boot_saturated : metaStep bootLift bootViable stage3 = none := by decide
theorem frozen_second : metaStep bootLift bootViable frozen1 = some frozen2 := by decide
theorem frozen_stalls : metaStep bootLift bootViable frozen2 = none := by decide

theorem meta_change_explains_divergent_rule_output :
    frozen1.metaRules ≠ stage1.metaRules := by
  exact divergent_next_edges_require_meta_difference
    bootLift bootViable frozen1 stage1 frozen2 stage2
    rfl rfl frozen_second boot_second (by decide)

theorem boot_three_rounds :
    iterateMeta bootLift bootViable 3 seed = stage3 := by decide

theorem boot_after_saturation (n : ℕ) :
    iterateMeta bootLift bootViable n stage3 = stage3 :=
  iterateMeta_stable_of_none bootLift bootViable stage3 n boot_saturated

theorem frozen_after_two_rounds (n : ℕ) :
    iterateMeta bootLift bootViable n frozen2 = frozen2 :=
  iterateMeta_stable_of_none bootLift bootViable frozen2 n frozen_stalls

end LinearInputMetaRuleExtension
