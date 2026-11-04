/-!
# Temporal local-operator extinction and historical nonpreservation

Preservation is NOT an axiom. An explicit local operation family has a
time-dependent, state-dependent Boolean domain. At each time/state the
first available local operator executes; if none is defined, the system
stutters. Exact old-to-later history preservation can then be falsified.

Main result: if an earlier successor moves some state but every local
operator is unavailable at the later time, then no injective
observation-and-transition-preserving history embedding exists.
This remains false after arbitrary replacement of the local action
functions so long as their availability domains are fixed and empty.

Sharp boundary: when the observations are unchanged and all later
operators are absent, preservation holds iff the old successor
was already stationary. A single local extinction need not break
preservation if a second local implements the same operation.
-/

section

namespace LinearInputTemporalExtinction

open LinearInputFiniteSelfSynthesis
open LinearInputHistoryNonpreservation

/-- Current local domains and operations are separate: the first
available operator (in the supplied local priority list) is applied. -/
structure LocalTimeline (S Ω Λ : Type*) where
  locals : List Λ
  available : ℕ → Λ → S → Bool
  action : Λ → S → S
  readout : ℕ → S → Ω

def stepAt {S Ω Λ : Type*}
    (X : LocalTimeline S Ω Λ) (t : ℕ) (x : S) : S :=
  match chooseTarget X.locals (fun loc => X.available t loc x) with
  | none => x
  | some loc => X.action loc x

/-- Freeze the system at one time to obtain the PR #65 history object. -/
def historyAt {S Ω Λ : Type*}
    (X : LocalTimeline S Ω Λ) (t : ℕ) :
    HistoryModel S Ω :=
  ⟨X.readout t, stepAt X t⟩

/-- All local operators have empty domains at this time. -/
def AllExtinct {S Ω Λ : Type*}
    (X : LocalTimeline S Ω Λ) (t : ℕ) : Prop :=
  ∀ x loc, loc ∈ X.locals → X.available t loc x = false

/-- If no listed operation is defined at the present state, then
the first-available finite search returns none. -/
theorem chooseTarget_none_of_all_disabled {Λ : Type*}
    (locals : List Λ) (enabled : Λ → Bool)
    (h : ∀ loc, loc ∈ locals → enabled loc = false) :
    chooseTarget locals enabled = none := by
  cases hc : chooseTarget locals enabled with
  | none => rfl
  | some loc =>
      obtain ⟨hmem, hv⟩ :=
        chooseTarget_sound locals enabled loc hc
      rw [h loc hmem] at hv
      cases hv

theorem extinct_step_identity {S Ω Λ : Type*}
    (X : LocalTimeline S Ω Λ) (t : ℕ)
    (h : AllExtinct X t) (x : S) :
    stepAt X t x = x := by
  have hnone : chooseTarget X.locals
      (fun loc => X.available t loc x) = none :=
    chooseTarget_none_of_all_disabled X.locals
      (fun loc => X.available t loc x) (h x)
  simp [stepAt, hnone]

/-- Local extinction can destroy the entire operation history even
when the observable vocabulary remains unchanged. -/
theorem extinction_forces_nonpreservation {S Ω Λ : Type*}
    (X : LocalTimeline S Ω Λ) (before after : ℕ)
    (x : S) (hm : stepAt X before x ≠ x)
    (he : AllExtinct X after) :
    ¬ Preserves (historyAt X before) (historyAt X after) := by
  exact moving_history_cannot_embed_in_stationary_history
    (historyAt X before) (historyAt X after) x hm
    (fun y => extinct_step_identity X after he y)

/-- Even replacing every possible local action does not restore the
history if all corresponding later availability domains stay empty. -/
def reassignActions {S Ω Λ : Type*}
    (X : LocalTimeline S Ω Λ) (newActions : Λ → S → S) :
    LocalTimeline S Ω Λ :=
  { X with action := newActions }

theorem extinction_survives_reassignment {S Ω Λ : Type*}
    (X : LocalTimeline S Ω Λ) (t : ℕ)
    (he : AllExtinct X t) (newActions : Λ → S → S) :
    AllExtinct (reassignActions X newActions) t := by
  exact he

theorem extinction_blocks_every_local_action_rewrite {S Ω Λ : Type*}
    (X : LocalTimeline S Ω Λ) (before after : ℕ)
    (x : S) (hm : stepAt X before x ≠ x)
    (he : AllExtinct X after)
    (newActions : Λ → S → S) :
    ¬ Preserves (historyAt X before)
        (historyAt (reassignActions X newActions) after) := by
  exact moving_history_cannot_embed_in_stationary_history
    (historyAt X before)
    (historyAt (reassignActions X newActions) after) x hm
    (fun y => extinct_step_identity (reassignActions X newActions) after
      (extinction_survives_reassignment X after he newActions) y)

/-- If old and later observers agree, terminal extinction causes loss
of faithful history exactly when some earlier state genuinely moves.
This is a necessary-and-sufficient boundary, not a universal
consequence of mere local disappearance. -/
theorem preservation_iff_old_stationary_under_extinction
    {S Ω Λ : Type*} (X : LocalTimeline S Ω Λ)
    (before after : ℕ)
    (he : AllExtinct X after)
    (hread : ∀ x, X.readout before x = X.readout after x) :
    Preserves (historyAt X before) (historyAt X after) ↔
      ∀ x, stepAt X before x = x := by
  constructor
  · rintro ⟨f, hf, _, ht⟩ x
    apply hf
    calc
      f (stepAt X before x) = stepAt X after (f x) := ht x
      _ = f x := extinct_step_identity X after he (f x)
  · intro hold
    refine ⟨fun x => x, ?_, ?_, ?_⟩
    · intro x y h
      exact h
    · intro x
      exact (hread x).symm
    · intro x
      exact (hold x).trans (extinct_step_identity X after he x).symm

/-- An initial history survives the entire closed discrete interval iff
it has a faithful embedding into every frozen-time history. -/
def PreservedOn {S Ω Λ : Type*}
    (X : LocalTimeline S Ω Λ) (start stop : ℕ) : Prop :=
  ∀ t, start ≤ t → t ≤ stop →
    Preserves (historyAt X start) (historyAt X t)

theorem interval_with_extinct_endpoint_is_not_preserved
    {S Ω Λ : Type*} (X : LocalTimeline S Ω Λ)
    (start stop terminal : ℕ)
    (hs : start ≤ terminal) (ht : terminal ≤ stop)
    (x : S) (hm : stepAt X start x ≠ x)
    (he : AllExtinct X terminal) :
    ¬ PreservedOn X start stop := by
  intro h
  exact (extinction_forces_nonpreservation X start terminal x hm he)
    (h terminal hs ht)

/-- A concrete two-state/two-local system: local 0 runs a toggle
at time 0, local 1 takes over at time 1, and all locals vanish
from time 2 onward. Observations remain unchanged throughout. -/
def flip (x : Fin 2) : Fin 2 :=
  if x = 0 then 1 else 0

def sampleAvailable (t : ℕ) (loc : Fin 2) (_x : Fin 2) : Bool :=
  if t = 0 then decide (loc = 0)
  else if t = 1 then decide (loc = 1)
  else false

def sample : LocalTimeline (Fin 2) Unit (Fin 2) :=
  ⟨[0, 1], sampleAvailable, (fun _ => flip), fun _ _ => ()⟩

theorem sample_step_zero (x : Fin 2) :
    stepAt sample 0 x = flip x := by
  rfl

theorem sample_step_one (x : Fin 2) :
    stepAt sample 1 x = flip x := by
  rfl

theorem sample_first_local_disappears :
    ∀ x : Fin 2, sample.available 1 0 x = false := by
  intro x
  rfl

theorem sample_second_local_takes_over :
    ∀ x : Fin 2, sample.available 1 1 x = true := by
  intro x
  rfl

/-- One local extinction is insufficient: a second local realizes
the same operation and fully preserves the older history. -/
theorem sample_history_preserved_after_one_local_disappears :
    Preserves (historyAt sample 0) (historyAt sample 1) := by
  refine ⟨fun x => x, ?_, ?_, ?_⟩
  · intro x y h
    exact h
  · intro x
    rfl
  · intro x
    change stepAt sample 0 x = stepAt sample 1 x
    rw [sample_step_zero, sample_step_one]

theorem sample_extinct_after_two
    (t : ℕ) (ht : 2 ≤ t) :
    AllExtinct sample t := by
  intro x loc _
  have hn0 : t ≠ 0 := by omega
  have hn1 : t ≠ 1 := by omega
  simp [sample, sampleAvailable, hn0, hn1]

theorem sample_old_history_moves :
    stepAt sample 0 (0 : Fin 2) ≠ 0 := by
  decide

theorem sample_no_preservation_after_two
    (t : ℕ) (ht : 2 ≤ t) :
    ¬ Preserves (historyAt sample 0) (historyAt sample t) := by
  exact extinction_forces_nonpreservation sample 0 t 0
    sample_old_history_moves (sample_extinct_after_two t ht)

theorem sample_no_interval_preservation
    (stop : ℕ) (hstop : 2 ≤ stop) :
    ¬ PreservedOn sample 0 stop := by
  exact interval_with_extinct_endpoint_is_not_preserved
    sample 0 stop 2 (by omega) hstop 0
    sample_old_history_moves
    (sample_extinct_after_two 2 (by omega))

/-- Even after extinction, the current observation is unchanged.
The counterexample therefore isolates loss of *operation history*. -/
theorem sample_snapshots_always_preserved (t : ℕ) :
    SnapshotPreserves (historyAt sample 0) (historyAt sample t) := by
  refine ⟨fun x => x, ?_, ?_⟩
  · intro x y h
    exact h
  · intro x
    rfl

theorem sample_no_local_action_rewrite_restores_history
    (t : ℕ) (ht : 2 ≤ t)
    (newActions : Fin 2 → Fin 2 → Fin 2) :
    ¬ Preserves (historyAt sample 0)
      (historyAt (reassignActions sample newActions) t) := by
  exact extinction_blocks_every_local_action_rewrite
    sample 0 t 0 sample_old_history_moves
    (sample_extinct_after_two t ht) newActions

/-- Re-enabling a local operator *changes the domain*. It can restore
historical preservation, and so falls outside the impossibility theorem. -/
def reactivated : LocalTimeline (Fin 2) Unit (Fin 2) :=
  { sample with available := fun t loc x =>
      if t = 2 then decide (loc = 0) else sampleAvailable t loc x }

theorem reactivated_step_two (x : Fin 2) :
    stepAt reactivated 2 x = flip x := by
  rfl

theorem reactivation_can_restore_preservation :
    Preserves (historyAt sample 0) (historyAt reactivated 2) := by
  refine ⟨fun x => x, ?_, ?_, ?_⟩
  · intro x y h
    exact h
  · intro x
    rfl
  · intro x
    change stepAt sample 0 x = stepAt reactivated 2 x
    rw [sample_step_zero, reactivated_step_two]

/-- Reopening the old operation at time 3 recovers an endpoint
representation, but the intervening loss at time 2 remains real. -/
def recoveredAfterGap : LocalTimeline (Fin 2) Unit (Fin 2) :=
  { sample with available := fun t loc x =>
      if t = 3 then decide (loc = 0) else sampleAvailable t loc x }

theorem recovered_step_zero (x : Fin 2) :
    stepAt recoveredAfterGap 0 x = flip x := by
  rfl

theorem recovered_step_three (x : Fin 2) :
    stepAt recoveredAfterGap 3 x = flip x := by
  rfl

theorem recovered_middle_extinct :
    AllExtinct recoveredAfterGap 2 := by
  intro x loc _
  rfl

theorem recovered_endpoints_preserve_history :
    Preserves (historyAt recoveredAfterGap 0)
      (historyAt recoveredAfterGap 3) := by
  refine ⟨fun x => x, ?_, ?_, ?_⟩
  · intro x y h
    exact h
  · intro x
    rfl
  · intro x
    change stepAt recoveredAfterGap 0 x =
      stepAt recoveredAfterGap 3 x
    rw [recovered_step_zero, recovered_step_three]

theorem recovered_interval_still_not_preserved :
    ¬ PreservedOn recoveredAfterGap 0 3 := by
  exact interval_with_extinct_endpoint_is_not_preserved
    recoveredAfterGap 0 3 2 (by omega) (by omega) 0
    (by decide) recovered_middle_extinct

/-- Endpoint recovery does NOT imply interval preservation. -/
theorem recovered_endpoints_but_broken_interval :
    Preserves (historyAt recoveredAfterGap 0)
      (historyAt recoveredAfterGap 3) ∧
    ¬ PreservedOn recoveredAfterGap 0 3 :=
  ⟨recovered_endpoints_preserve_history,
   recovered_interval_still_not_preserved⟩

end LinearInputTemporalExtinction
