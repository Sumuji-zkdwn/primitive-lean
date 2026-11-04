/-!
# Fifth definition: failure of historical preservation

This model treats preservation as a *property to falsify*, not as an axiom
that must hold. A historical embedding must injectively represent earlier
states and respect both observations and the successor operation.

Two independent obstructions are formalized:
(1) an old observable label is absent in every later state; no transition
rewrite, or any later-state endomorphism before reading out, can restore it;
(2) the old system has a nontrivial successor but the later system has only
fixed points. The latter can fail even when a snapshot embedding exists.

The later system in (1) has more states and more distinct observable labels:
global growth does not entail historical preservation. Adjoining a separate
copy of the old history restores representability, but this is an actual
state-space extension, NOT a repair internal to the defective later system.

No claim that all local extinction or every noncommutative finite system
forces nonpreservation is made.
-/

section

namespace LinearInputHistoryNonpreservation

/-- A deterministic history with a present observation and a next step. -/
structure HistoryModel (S Ω : Type*) where
  observe : S → Ω
  advance : S → S

/-- Preserving the entire deterministic history requires an injective
state representation commuting with observation and next-step execution. -/
def Preserves {S T Ω : Type*}
    (A : HistoryModel S Ω) (B : HistoryModel T Ω) : Prop :=
  ∃ f : S → T, Function.Injective f ∧
    (∀ x, B.observe (f x) = A.observe x) ∧
    (∀ x, f (A.advance x) = B.advance (f x))

/-- An observation-preserving snapshot embedding can exist even when
successor dynamics cannot be preserved. -/
def SnapshotPreserves {S T Ω : Type*}
    (A : HistoryModel S Ω) (B : HistoryModel T Ω) : Prop :=
  ∃ f : S → T, Function.Injective f ∧
    ∀ x, B.observe (f x) = A.observe x

theorem preserves_implies_snapshot {S T Ω : Type*}
    (A : HistoryModel S Ω) (B : HistoryModel T Ω)
    (h : Preserves A B) : SnapshotPreserves A B := by
  obtain ⟨f, hinj, hread, _⟩ := h
  exact ⟨f, hinj, hread⟩

theorem preserves_refl {S Ω : Type*} (A : HistoryModel S Ω) :
    Preserves A A := by
  refine ⟨fun x => x, ?_, ?_, ?_⟩
  · intro x y h
    exact h
  · intro x
    rfl
  · intro x
    rfl

theorem preserves_trans {S T U Ω : Type*}
    (A : HistoryModel S Ω)
    (B : HistoryModel T Ω)
    (C : HistoryModel U Ω)
    (hAB : Preserves A B) (hBC : Preserves B C) :
    Preserves A C := by
  obtain ⟨f, hf, ho, ht⟩ := hAB
  obtain ⟨g, hg, go, gt⟩ := hBC
  refine ⟨fun x => g (f x), hg.comp hf, ?_, ?_⟩
  · intro x
    calc
      C.observe (g (f x)) = B.observe (f x) := go (f x)
      _ = A.observe x := ho x
  · intro x
    calc
      g (f (A.advance x)) = g (B.advance (f x)) :=
        congrArg g (ht x)
      _ = C.advance (g (f x)) := gt (f x)

/-- An old label absent from the entire new state space is a hard
obstruction to historical preservation. -/
theorem missing_label_blocks_preservation {S T Ω : Type*}
    (A : HistoryModel S Ω) (B : HistoryModel T Ω)
    (h : ∃ x : S, ∀ y : T, B.observe y ≠ A.observe x) :
    ¬ Preserves A B := by
  rintro ⟨f, _, hread, _⟩
  obtain ⟨x, hmiss⟩ := h
  exact hmiss (f x) (hread x)

/-- Replacing just the new transition operator cannot recover an
observation label absent from all new states. -/
theorem missing_label_blocks_any_transition_rewrite {S T Ω : Type*}
    (A : HistoryModel S Ω) (B : HistoryModel T Ω)
    (h : ∃ x : S, ∀ y : T, B.observe y ≠ A.observe x)
    (newAdvance : T → T) :
    ¬ Preserves A { B with advance := newAdvance } := by
  exact missing_label_blocks_preservation A
    { B with advance := newAdvance } h

/-- Even an arbitrary later-state transformer applied before readout
cannot produce a label that the fixed later observation cannot express. -/
def PostRepairSnapshot {S T Ω : Type*}
    (A : HistoryModel S Ω) (B : HistoryModel T Ω)
    (repair : T → T) : Prop :=
  ∃ f : S → T, Function.Injective f ∧
    ∀ x, B.observe (repair (f x)) = A.observe x

theorem missing_label_blocks_all_internal_repairs {S T Ω : Type*}
    (A : HistoryModel S Ω) (B : HistoryModel T Ω)
    (h : ∃ x : S, ∀ y : T, B.observe y ≠ A.observe x)
    (repair : T → T) :
    ¬ PostRepairSnapshot A B repair := by
  rintro ⟨f, _, hread⟩
  obtain ⟨x, hmiss⟩ := h
  exact hmiss (repair (f x)) (hread x)

/-- Under an injective later observer, exact history preservation is
equivalent to snapshot injectivity plus a one-step observational equation.
The injective-observer hypothesis is essential. -/
theorem preserves_iff_one_step_observation_of_injective
    {S T Ω : Type*}
    (A : HistoryModel S Ω) (B : HistoryModel T Ω)
    (hinj : Function.Injective B.observe) :
    Preserves A B ↔
      ∃ f : S → T, Function.Injective f ∧
        (∀ x, B.observe (f x) = A.observe x) ∧
        (∀ x, B.observe (f (A.advance x)) =
          B.observe (B.advance (f x))) := by
  constructor
  · rintro ⟨f, hf, hread, hstep⟩
    refine ⟨f, hf, hread, ?_⟩
    intro x
    exact congrArg B.observe (hstep x)
  · rintro ⟨f, hf, hread, hstep⟩
    exact ⟨f, hf, hread, fun x => hinj (hstep x)⟩

/-- Independent obstruction: a nontrivial old step cannot injectively
commute with an entirely stationary successor, even if all current
observations can be embedded. -/
theorem moving_history_cannot_embed_in_stationary_history
    {S T Ω : Type*}
    (A : HistoryModel S Ω) (B : HistoryModel T Ω)
    (x : S) (hmove : A.advance x ≠ x)
    (hstationary : ∀ y, B.advance y = y) :
    ¬ Preserves A B := by
  rintro ⟨f, hinj, _, hstep⟩
  have hfx : f (A.advance x) = f x := by
    rw [hstep x, hstationary (f x)]
  exact hmove (hinj hfx)

/-- An actual extension of the later state type that adjoins a tagged
copy of the old history can restore historical representability. This
does not retroactively preserve the old history *inside* the later type. -/
def adjoinOldHistory {S T Ω : Type*}
    (A : HistoryModel S Ω) (B : HistoryModel T Ω) :
    HistoryModel (Sum S T) Ω where
  observe := fun
    | .inl x => A.observe x
    | .inr y => B.observe y
  advance := fun
    | .inl x => .inl (A.advance x)
    | .inr y => .inr (B.advance y)

theorem adjoining_old_history_restores_embedding {S T Ω : Type*}
    (A : HistoryModel S Ω) (B : HistoryModel T Ω) :
    Preserves A (adjoinOldHistory A B) := by
  refine ⟨Sum.inl, ?_, ?_, ?_⟩
  · intro x y h
    exact Sum.inl.inj h
  · intro x
    rfl
  · intro x
    rfl

/-- A global state-space expansion and increase in the number of
observable labels need not preserve an older particular label. -/
def originalReadout (x : Fin 2) : Fin 4 :=
  if x = 0 then 0 else 1

def expandedReadout (x : Fin 4) : Fin 4 :=
  if x = 0 then 1 else if x = 1 then 2 else 3

def originalHistory : HistoryModel (Fin 2) (Fin 4) :=
  ⟨originalReadout, fun x => x⟩

def expandedHistory : HistoryModel (Fin 4) (Fin 4) :=
  ⟨expandedReadout, fun x => x⟩

theorem expanded_has_more_states :
    Fintype.card (Fin 2) < Fintype.card (Fin 4) := by
  decide

theorem expanded_has_more_observable_labels :
    (Finset.univ.image originalReadout).card <
      (Finset.univ.image expandedReadout).card := by
  decide

theorem original_label_disappears :
    ∀ y : Fin 4, expandedHistory.observe y ≠
      originalHistory.observe (0 : Fin 2) := by
  intro y
  fin_cases y <;> decide

theorem expanded_but_not_preserved :
    ¬ Preserves originalHistory expandedHistory := by
  exact missing_label_blocks_preservation originalHistory expandedHistory
    ⟨0, original_label_disappears⟩

theorem expanded_history_irreparable_by_internal_action
    (repair : Fin 4 → Fin 4) :
    ¬ PostRepairSnapshot originalHistory expandedHistory repair := by
  exact missing_label_blocks_all_internal_repairs
    originalHistory expandedHistory ⟨0, original_label_disappears⟩ repair

theorem expanded_history_irreparable_by_transition_rewrite
    (newAdvance : Fin 4 → Fin 4) :
    ¬ Preserves originalHistory
      {expandedHistory with advance := newAdvance} := by
  exact missing_label_blocks_any_transition_rewrite
    originalHistory expandedHistory
    ⟨0, original_label_disappears⟩ newAdvance

/-- A separate counterexample: all snapshot labels survive, yet their
operator history does not preserve. -/
def toggle (x : Fin 2) : Fin 2 := if x = 0 then 1 else 0

def togglingHistory : HistoryModel (Fin 2) Unit :=
  ⟨fun _ => (), toggle⟩

def stationaryHistory : HistoryModel (Fin 2) Unit :=
  ⟨fun _ => (), fun x => x⟩

theorem snapshots_can_be_embedded :
    SnapshotPreserves togglingHistory stationaryHistory := by
  refine ⟨fun x => x, ?_, ?_⟩
  · intro x y h
    exact h
  · intro x
    rfl

theorem toggling_history_cannot_be_preserved :
    ¬ Preserves togglingHistory stationaryHistory := by
  exact moving_history_cannot_embed_in_stationary_history
    togglingHistory stationaryHistory 0 (by decide) (by intro y; rfl)

theorem extension_can_represent_both_histories :
    Preserves originalHistory
      (adjoinOldHistory originalHistory expandedHistory) := by
  exact adjoining_old_history_restores_embedding
    originalHistory expandedHistory

end LinearInputHistoryNonpreservation
