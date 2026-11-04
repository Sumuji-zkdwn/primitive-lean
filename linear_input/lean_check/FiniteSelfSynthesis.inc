/-!
# Finite internal construction of a repair operator

Relative to the finite, explicit candidate-state and local-acceptance
tables, chooseTarget and synthesizeFromLocals are executable search
procedures, not an existence axiom or an unrestricted discovery oracle.

Soundness and completeness are limited to the supplied candidate list.
Under the verified interval-extinction hypotheses of PR #60, a successfully
synthesized one-point patch preserves one time step and cannot coincide
with any old operator word at the initial state.

The full state space is not enlarged; the new alphabet includes the
generated patch. Unbounded generation, repair feasibility from extinction
alone, continuous time, and physical information creation are not asserted.
-/

section

namespace LinearInputFiniteSelfSynthesis

open LinearInputOperatorWords
open LinearInputOperatorRefinement
open LinearInputSemanticIntervals

/-- Deterministically choose the first terminal-viable state in a finite catalog. -/
def chooseTarget {α : Type*} : List α → (α → Bool) → Option α
  | [], _ => none
  | a :: rest, viable =>
      if viable a then some a else chooseTarget rest viable

theorem chooseTarget_sound {α : Type*}
    (candidates : List α) (viable : α → Bool) (target : α)
    (h : chooseTarget candidates viable = some target) :
    target ∈ candidates ∧ viable target = true := by
  induction candidates with
  | nil =>
      simp [chooseTarget] at h
  | cons a tail ih =>
      cases ha : viable a with
      | false =>
          have ht : chooseTarget tail viable = some target := by
            simpa [chooseTarget, ha] using h
          obtain ⟨hmem, hvalid⟩ := ih ht
          exact ⟨List.mem_cons_of_mem a hmem, hvalid⟩
      | true =>
          have ht : a = target := by
            simpa [chooseTarget, ha] using h
          subst target
          exact ⟨by simp, ha⟩

/-- If a candidate exists, the finite search returns a candidate. -/
theorem chooseTarget_complete {α : Type*}
    (candidates : List α) (viable : α → Bool)
    (hex : ∃ target, target ∈ candidates ∧ viable target = true) :
    ∃ target, chooseTarget candidates viable = some target := by
  induction candidates with
  | nil =>
      obtain ⟨target, hmem, _⟩ := hex
      simp at hmem
  | cons a tail ih =>
      cases ha : viable a with
      | true =>
          exact ⟨a, by simp [chooseTarget, ha]⟩
      | false =>
          have htail : ∃ target, target ∈ tail ∧ viable target = true := by
            obtain ⟨target, hmem, hvalid⟩ := hex
            rcases List.mem_cons.mp hmem with heq | hm
            · subst target
              simp [ha] at hvalid
            · exact ⟨target, hm, hvalid⟩
          obtain ⟨target, ht⟩ := ih htail
          exact ⟨target, by simpa [chooseTarget, ha] using ht⟩

theorem chooseTarget_none_exhaustive {α : Type*}
    (candidates : List α) (viable : α → Bool)
    (h : chooseTarget candidates viable = none) :
    ∀ target, target ∈ candidates → viable target = false := by
  intro target hmem
  cases hv : viable target with
  | false => rfl
  | true =>
      obtain ⟨x, hx⟩ := chooseTarget_complete candidates viable
        ⟨target, hmem, hv⟩
      rw [h] at hx
      cases hx

/-- Insert a one-point repair action, without changing other states. -/
def patch {α : Type*} [DecidableEq α]
    (start target : α) : α → α :=
  fun x => if x = start then target else x

theorem patch_start {α : Type*} [DecidableEq α]
    (start target : α) : patch start target start = target := by
  simp [patch]

theorem patch_other {α : Type*} [DecidableEq α]
    (start target x : α) (hx : x ≠ start) :
    patch start target x = x := by
  simp [patch, hx]

/-- A search result becomes a concrete new state transformer. -/
def generate {α : Type*} [DecidableEq α]
    (candidates : List α) (viable : α → Bool) (start : α) :
    Option (α → α) :=
  (chooseTarget candidates viable).map (patch start)

theorem generate_sound {α : Type*} [DecidableEq α]
    (candidates : List α) (viable : α → Bool) (start : α)
    (operation : α → α)
    (h : generate candidates viable start = some operation) :
    viable (operation start) = true := by
  cases hc : chooseTarget candidates viable with
  | none =>
      simp [generate, hc] at h
  | some target =>
      have ho : patch start target = operation := by
        simpa [generate, hc] using h
      have hv := (chooseTarget_sound candidates viable target hc).2
      simpa [← ho, patch] using hv

theorem generate_complete {α : Type*} [DecidableEq α]
    (candidates : List α) (viable : α → Bool) (start : α)
    (hex : ∃ target, target ∈ candidates ∧ viable target = true) :
    ∃ operation, generate candidates viable start = some operation := by
  obtain ⟨target, ht⟩ := chooseTarget_complete candidates viable hex
  exact ⟨patch start target, by simp [generate, ht]⟩

theorem generate_none_exhaustive {α : Type*} [DecidableEq α]
    (candidates : List α) (viable : α → Bool) (start : α)
    (h : generate candidates viable start = none) :
    ∀ target, target ∈ candidates → viable target = false := by
  have hnone : chooseTarget candidates viable = none := by
    cases hc : chooseTarget candidates viable with
    | none => rfl
    | some target =>
        simp [generate, hc] at h
  exact chooseTarget_none_exhaustive candidates viable hnone

/-- Finite local systems are part of the input, not an abstract repair oracle. -/
def someLocal {α σ : Type*} :
    List σ → (σ → α → Bool) → α → Bool
  | [], _, _ => false
  | loc :: rest, accepts, x =>
      if accepts loc x then true else someLocal rest accepts x

theorem someLocal_spec {α σ : Type*}
    (locals : List σ) (accepts : σ → α → Bool) (x : α) :
    someLocal locals accepts x = true ↔
      ∃ loc, loc ∈ locals ∧ accepts loc x = true := by
  induction locals with
  | nil =>
      simp [someLocal]
  | cons a tail ih =>
      cases ha : accepts a x with
      | true =>
          constructor
          · intro _
            exact ⟨a, by simp, ha⟩
          · intro _
            simp [someLocal, ha]
      | false =>
          constructor
          · intro h
            have ht : someLocal tail accepts x = true := by
              simpa [someLocal, ha] using h
            obtain ⟨loc, hm, hv⟩ := ih.mp ht
            exact ⟨loc, List.mem_cons_of_mem a hm, hv⟩
          · rintro ⟨loc, hm, hv⟩
            rcases List.mem_cons.mp hm with heq | htail
            · subst loc
              simp [ha] at hv
            · have ht : someLocal tail accepts x = true :=
                ih.mpr ⟨loc, htail, hv⟩
              simpa [someLocal, ha] using ht

/-- Search a finite local catalog and construct a one-point repair action. -/
def synthesizeFromLocals {α σ : Type*} [DecidableEq α]
    (candidates : List α) (locals : List σ)
    (accepts : σ → α → Bool) (start : α) : Option (α → α) :=
  generate candidates (someLocal locals accepts) start

theorem synthesizeFromLocals_sound {α σ : Type*} [DecidableEq α]
    (candidates : List α) (locals : List σ)
    (accepts : σ → α → Bool) (start : α) (operation : α → α)
    (h : synthesizeFromLocals candidates locals accepts start = some operation) :
    ∃ loc, loc ∈ locals ∧ accepts loc (operation start) = true := by
  exact (someLocal_spec locals accepts (operation start)).mp
    (generate_sound candidates (someLocal locals accepts) start operation h)

theorem synthesizeFromLocals_complete {α σ : Type*} [DecidableEq α]
    (candidates : List α) (locals : List σ)
    (accepts : σ → α → Bool) (start : α)
    (hex : ∃ target, target ∈ candidates ∧
      ∃ loc, loc ∈ locals ∧ accepts loc target = true) :
    ∃ operation, synthesizeFromLocals candidates locals accepts start =
      some operation := by
  have hv : ∃ target, target ∈ candidates ∧
      someLocal locals accepts target = true := by
    obtain ⟨target, hc, hloc⟩ := hex
    exact ⟨target, hc, (someLocal_spec locals accepts target).2 hloc⟩
  exact generate_complete candidates (someLocal locals accepts) start hv

/-- If the local Boolean table exactly describes terminal viability, the
finite search constructs a fresh action whose one-step use preserves
the entire interval and is unattainable by old finite words. -/
theorem viable_internal_synthesis {α σ ι : Type*} [DecidableEq α]
    (alive : ℕ → σ → α → Prop) (region : α → Prop)
    (old : ι → α → α) (start : α)
    (candidates : List α) (locals : List σ)
    (accepts : σ → α → Bool)
    (hmatch : ∀ x, (∃ loc, loc ∈ locals ∧ accepts loc x = true) ↔
      HasLocal alive 1 x)
    (hi : OldInvariant region old) (hx : region start)
    (he : TerminalExtinction alive region 1)
    (hzero : HasLocal alive 0 start)
    (hex : ∃ target, target ∈ candidates ∧
      ∃ loc, loc ∈ locals ∧ accepts loc target = true) :
    ∃ operation : α → α,
      synthesizeFromLocals candidates locals accepts start = some operation ∧
      IntervalSurvival alive (sumStep old (fun _ : Unit => operation))
        [Sum.inr ()] start ∧
      (∀ word : List ι, run old word start ≠ operation start) := by
  obtain ⟨operation, hgen⟩ :=
    synthesizeFromLocals_complete candidates locals accepts start hex
  have hvalid : HasLocal alive 1 (operation start) :=
    (hmatch (operation start)).mp
      (synthesizeFromLocals_sound candidates locals accepts
        start operation hgen)
  refine ⟨operation, hgen, ?_, ?_⟩
  · exact one_step_interval alive (sumStep old (fun _ : Unit => operation))
      (Sum.inr ()) start hzero hvalid
  · exact viable_repair_not_old_generated alive region old 1 start
      hi hx he operation hvalid

/-- Concrete finite sensor/repair catalog for the verified Fin 3 witness. -/
def witnessCandidates : List (Fin 3) := [0, 1, 2]

def witnessLocals : List (Fin 2) := [0, 1]

def witnessAccepts (loc : Fin 2) (x : Fin 3) : Bool :=
  decide (loc = 1 ∧ x = 2)

theorem witnessLocalTable_exact (x : Fin 3) :
    (∃ loc, loc ∈ witnessLocals ∧ witnessAccepts loc x = true) ↔
      HasLocal witnessAlive 1 x := by
  constructor
  · rintro ⟨loc, _, hacc⟩
    have hpair : loc = 1 ∧ x = 2 := by
      simpa [witnessAccepts] using hacc
    exact ⟨loc, Or.inr ⟨rfl, hpair.1, hpair.2⟩⟩
  · rintro ⟨loc, halive⟩
    change (1 = 0 ∧ loc = 0 ∧ x = 1) ∨
      (1 = 1 ∧ loc = 1 ∧ x = 2) at halive
    rcases halive with hzero | hone
    · have hz : (1 : ℕ) = 0 := hzero.1
      omega
    · refine ⟨loc, ?_, ?_⟩
      · fin_cases loc <;> simp [witnessLocals]
      · have hpair : loc = 1 ∧ x = 2 := ⟨hone.2.1, hone.2.2⟩
        simpa [witnessAccepts] using hpair

theorem witnessInternalFeasible :
    ∃ target, target ∈ witnessCandidates ∧
      ∃ loc, loc ∈ witnessLocals ∧ witnessAccepts loc target = true := by
  exact ⟨2, by simp [witnessCandidates], 1,
    by simp [witnessLocals], by decide⟩

/-- The repair primitive of the interval theorem is actually produced by
the finite search. No repair operator is inserted into the conclusion. -/
theorem witnessInternalGenerator :
    synthesizeFromLocals witnessCandidates witnessLocals
      witnessAccepts (1 : Fin 3) = some (witnessFresh ()) := by
  rfl

/-- The finite Boolean search itself reduces in Lean's computational kernel. -/
theorem witnessGeneratorEvaluates :
    (synthesizeFromLocals witnessCandidates witnessLocals
      witnessAccepts (1 : Fin 3)).isSome = true := by
  decide

theorem witnessSelfGeneratedExtension :
    (∃ operation : Fin 3 → Fin 3,
      synthesizeFromLocals witnessCandidates witnessLocals
        witnessAccepts 1 = some operation ∧
      IntervalSurvival witnessAlive
        (sumStep baseStep (fun _ : Unit => operation))
        [Sum.inr ()] 1 ∧
      (∀ word : List Unit,
        run baseStep word 1 ≠ operation 1)) ∧
    ¬ Function.Injective (forget exampleK baseStep witnessFresh) := by
  constructor
  · exact viable_internal_synthesis witnessAlive witnessRegion baseStep 1
      witnessCandidates witnessLocals witnessAccepts
      witnessLocalTable_exact witness_old_invariant
      (by simp [witnessRegion]) witness_terminal_extinct
      witness_start_alive witnessInternalFeasible
  · exact witness_forget_not_injective

/-- A finite catalog without a viable terminal state fails explicitly. -/
def noneAccepts (_ : Fin 2) (_ : Fin 3) : Bool := false

theorem noViableTargetIsNotFabricated :
    synthesizeFromLocals witnessCandidates witnessLocals
      noneAccepts (1 : Fin 3) = none := by
  rfl

end LinearInputFiniteSelfSynthesis
