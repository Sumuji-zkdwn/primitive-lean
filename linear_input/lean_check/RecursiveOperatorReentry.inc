/-!
# Recursive re-entry of newly constructed finite operators

This additive module extends FiniteSelfSynthesis (PR #61) with a finite
catalogue of operation descriptors. An accepted, previously unknown
descriptor becomes a one-point patch operator. In the next round that
descriptor is itself an input to the fixed child-generation rule.

The result is a *bounded, explicitly ruled* feedback loop, not an
unrestricted automatic invention engine. Soundness, newness, completeness
within the child frontier, preservation of prior descriptors, a conditional
one-step viability bridge, and a three-round saturation witness are proved.

A new intensional operator need not refine observational equivalence.
-/

section

namespace LinearInputRecursiveReentry

open LinearInputFiniteSelfSynthesis
open LinearInputSemanticIntervals
open LinearInputOperatorWords
open LinearInputOperatorRefinement

/-- Child descriptors of all known primitive patches, excluding already
known descriptors. A descriptor t denotes the patch `patch start t`. -/
def novelFrontier {α : Type*} [DecidableEq α]
    (children : α → List α) (known : List α) : List α :=
  (known.flatMap children).filter (fun x => decide (x ∉ known))

theorem novelFrontier_mem_iff {α : Type*} [DecidableEq α]
    (children : α → List α) (known : List α) (x : α) :
    x ∈ novelFrontier children known ↔
      x ∈ known.flatMap children ∧ x ∉ known := by
  simp [novelFrontier]

/-- Add the first viable fresh operator descriptor to the known library. -/
def reenter {α : Type*} [DecidableEq α]
    (children : α → List α) (viable : α → Bool)
    (known : List α) : Option (List α) :=
  (chooseTarget (novelFrontier children known) viable).map
    (fun target => known ++ [target])

/-- Every successful re-entry was generated from an old descriptor,
was not previously present, and passed the viability test. -/
theorem reenter_sound {α : Type*} [DecidableEq α]
    (children : α → List α) (viable : α → Bool)
    (known next : List α)
    (h : reenter children viable known = some next) :
    ∃ target,
      target ∈ known.flatMap children ∧
      target ∉ known ∧ viable target = true ∧
      next = known ++ [target] := by
  unfold reenter at h
  cases hc : chooseTarget (novelFrontier children known) viable with
  | none =>
      simp [hc] at h
  | some target =>
      have heq : known ++ [target] = next := by
        simpa [hc] using h
      obtain ⟨hfront, hviable⟩ :=
        chooseTarget_sound (novelFrontier children known) viable target hc
      obtain ⟨hchild, hnew⟩ :=
        (novelFrontier_mem_iff children known target).mp hfront
      exact ⟨target, hchild, hnew, hviable, heq.symm⟩

/-- Strict growth is not postulated: it follows from the successful
one-step library update. -/
theorem reenter_strict_length {α : Type*} [DecidableEq α]
    (children : α → List α) (viable : α → Bool)
    (known next : List α)
    (h : reenter children viable known = some next) :
    known.length < next.length := by
  obtain ⟨target, _, _, _, heq⟩ := reenter_sound children viable known next h
  rw [heq]
  simp

theorem reenter_preserves_known {α : Type*} [DecidableEq α]
    (children : α → List α) (viable : α → Bool)
    (known next : List α)
    (h : reenter children viable known = some next)
    (x : α) (hx : x ∈ known) : x ∈ next := by
  obtain ⟨target, _, _, _, heq⟩ := reenter_sound children viable known next h
  rw [heq]
  exact List.mem_append.mpr (Or.inl hx)

/-- The catalogue procedure is complete *relative to the current
children* (not relative to all conceivable operators). -/
theorem reenter_complete {α : Type*} [DecidableEq α]
    (children : α → List α) (viable : α → Bool)
    (known : List α)
    (h : ∃ target, target ∈ known.flatMap children ∧
      target ∉ known ∧ viable target = true) :
    ∃ next, reenter children viable known = some next := by
  obtain ⟨target, hchild, hnew, hv⟩ := h
  have hfront : target ∈ novelFrontier children known :=
    (novelFrontier_mem_iff children known target).mpr ⟨hchild, hnew⟩
  obtain ⟨chosen, hchosen⟩ :=
    chooseTarget_complete (novelFrontier children known) viable
      ⟨target, hfront, hv⟩
  exact ⟨known ++ [chosen], by simp [reenter, hchosen]⟩

/-- Failure is a finite local saturation certificate: no new *viable*
child exists in the current generated frontier. -/
theorem reenter_none_certificate {α : Type*} [DecidableEq α]
    (children : α → List α) (viable : α → Bool)
    (known : List α)
    (h : reenter children viable known = none) :
    ∀ target, target ∈ known.flatMap children →
      target ∈ known ∨ viable target = false := by
  have hn : chooseTarget (novelFrontier children known) viable = none := by
    unfold reenter at h
    cases hc : chooseTarget (novelFrontier children known) viable with
    | none => exact hc
    | some target => simp [hc] at h
  intro target hchild
  by_cases hm : target ∈ known
  · exact Or.inl hm
  · right
    apply chooseTarget_none_exhaustive
      (novelFrontier children known) viable hn target
    exact (novelFrontier_mem_iff children known target).mpr ⟨hchild, hm⟩

/-- Distinct patch targets define distinct *functions*, not only names. -/
theorem patch_target_injective {α : Type*} [DecidableEq α]
    (start x y : α) (heq : patch start x = patch start y) : x = y := by
  have h := congrArg (fun f : α → α => f start) heq
  simpa [patch] using h

/-- The new patch is not any existing patch in the registered library.
This does NOT assert observationally distinct quotient behavior. -/
theorem reenter_fresh_operator {α : Type*} [DecidableEq α]
    (children : α → List α) (viable : α → Bool)
    (known next : List α) (start : α)
    (h : reenter children viable known = some next) :
    ∃ target, target ∈ next ∧
      ∀ oldTarget, oldTarget ∈ known →
        patch start target ≠ patch start oldTarget := by
  obtain ⟨target, _, hnew, _, heq⟩ :=
    reenter_sound children viable known next h
  refine ⟨target, ?_, ?_⟩
  · rw [heq]
    simp
  · intro oldTarget hmem hequal
    have hto : target = oldTarget :=
      patch_target_injective start target oldTarget hequal
    subst oldTarget
    exact hnew hmem

/-- A given finite number of rounds, with failure preserving the last
valid catalogue. Newly generated descriptors are re-input at every step. -/
def iterateReentry {α : Type*} [DecidableEq α]
    (children : α → List α) (viable : α → Bool) :
    ℕ → List α → List α
  | 0, known => known
  | n + 1, known =>
      match reenter children viable known with
      | none => known
      | some next => iterateReentry children viable n next

theorem iterateReentry_preserves_known {α : Type*} [DecidableEq α]
    (children : α → List α) (viable : α → Bool)
    (n : ℕ) (known : List α) (x : α)
    (hx : x ∈ known) :
    x ∈ iterateReentry children viable n known := by
  induction n generalizing known with
  | zero =>
      simpa [iterateReentry] using hx
  | succ n ih =>
      cases hs : reenter children viable known with
      | none =>
          simpa [iterateReentry, hs] using hx
      | some next =>
          have hnext : x ∈ next :=
            reenter_preserves_known children viable known next hs x hx
          simpa [iterateReentry, hs] using ih next hnext

/-- The generator reaches a fixed point whenever no viable new child
is available. This does not assert that the full universe is explored. -/
theorem iterateReentry_stable_of_none {α : Type*} [DecidableEq α]
    (children : α → List α) (viable : α → Bool)
    (known : List α) (n : ℕ)
    (hnone : reenter children viable known = none) :
    iterateReentry children viable n known = known := by
  cases n with
  | zero => rfl
  | succ n => simp [iterateReentry, hnone]

/-- Derive terminal viability and word-nongenerability from a newly
constructed candidate, reusing PR #60/61 without assuming the operator. -/
theorem reentered_repair_survives {α σ ι : Type*} [DecidableEq α]
    (alive : ℕ → σ → α → Prop) (region : α → Prop)
    (old : ι → α → α) (start : α)
    (children : α → List α) (known next : List α)
    (locals : List σ) (accepts : σ → α → Bool)
    (hmatch : ∀ x, (∃ loc, loc ∈ locals ∧ accepts loc x = true) ↔
      HasLocal alive 1 x)
    (hi : OldInvariant region old) (hx : region start)
    (he : TerminalExtinction alive region 1)
    (hzero : HasLocal alive 0 start)
    (hstep : reenter children (someLocal locals accepts) known =
      some next) :
    ∃ target,
      target ∈ known.flatMap children ∧ target ∉ known ∧
      next = known ++ [target] ∧
      IntervalSurvival alive
        (sumStep old (fun _ : Unit => patch start target))
        [Sum.inr ()] start ∧
      (∀ word : List ι, run old word start ≠ patch start target start) := by
  obtain ⟨target, hchild, hnew, hviable, heq⟩ :=
    reenter_sound children (someLocal locals accepts) known next hstep
  have hterminal : HasLocal alive 1 (patch start target start) := by
    have hlocal := (someLocal_spec locals accepts target).mp hviable
    simpa [patch] using (hmatch target).mp hlocal
  refine ⟨target, hchild, hnew, heq, ?_, ?_⟩
  · exact one_step_interval alive
      (sumStep old (fun _ : Unit => patch start target))
      (Sum.inr ()) start hzero hterminal
  · exact viable_repair_not_old_generated
      alive region old 1 start hi hx he (patch start target) hterminal

/-- A concrete bounded fixed rule: one descriptor produces the next. -/
def chainChild (x : Fin 4) : List (Fin 4) :=
  if x = 0 then [1] else if x = 1 then [2]
  else if x = 2 then [3] else []

def chainAccept (_ : Fin 4) : Bool := true

def chainSeed : List (Fin 4) := [0]

theorem chain_first_round :
    reenter chainChild chainAccept chainSeed =
      some [0, 1] := by decide

theorem chain_second_round :
    reenter chainChild chainAccept [0, 1] =
      some [0, 1, 2] := by decide

theorem chain_third_round :
    reenter chainChild chainAccept [0, 1, 2] =
      some [0, 1, 2, 3] := by decide

theorem chain_saturated :
    reenter chainChild chainAccept [0, 1, 2, 3] = none := by decide

theorem chain_three_round_reentry :
    iterateReentry chainChild chainAccept 3 chainSeed =
      [0, 1, 2, 3] := by decide

theorem chain_after_saturation (n : ℕ) :
    iterateReentry chainChild chainAccept n [0, 1, 2, 3] =
      [0, 1, 2, 3] :=
  iterateReentry_stable_of_none chainChild chainAccept
    [0, 1, 2, 3] n chain_saturated

end LinearInputRecursiveReentry
