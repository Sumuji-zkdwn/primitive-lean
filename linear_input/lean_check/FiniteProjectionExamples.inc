namespace LinearInputProjectionExamples

open LinearInputOperatorWords LinearInputOperatorReachability
open LinearInputProjectionReachability

def idle : Unit → Bool → Bool := fun _ x => x

theorem run_idle (w : List Unit) (x : Bool) : run idle w x = x := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem idle_iff (x y : Bool) : Reachable idle x y ↔ x = y := by
  constructor
  · rintro ⟨w, hw⟩
    simpa only [run_idle] using hw
  · rintro rfl
    exact reachable_refl idle x

/-- Smallest state carrier witnessing a gain; false retains the old identity. -/
def addSetTrue : Bool → Bool → Bool := fun a x => if a then true else x

theorem two_state_gain : StrictGain idle addSetTrue id false := by
  refine ⟨true, ⟨[true], rfl⟩, ?_⟩
  intro h
  exact Bool.false_ne_true ((idle_iff false true).mp h)

theorem two_state_not_simulated : ¬ ProjectionSimulation idle addSetTrue id := by
  intro h
  exact no_gain_of_simulation idle addSetTrue id h false two_state_gain

/-- Proper carrier extension: 0 -> 1 is hidden, 1 -> 2 changes projection. -/
def project3 (y : Fin 3) : Bool := if y = 2 then true else false
def extend3 : Bool → Fin 3 → Fin 3 :=
  fun a y => if a then (if y = 0 then 1 else 2) else y

theorem three_state_gain : StrictGain idle extend3 project3 0 := by
  refine ⟨2, ⟨[true, true], rfl⟩, ?_⟩
  intro h
  have he : (false : Bool) = true := (idle_iff _ _).mp h
  exact Bool.false_ne_true he

theorem three_state_not_simulated : ¬ ProjectionSimulation idle extend3 project3 := by
  intro h
  exact no_gain_of_simulation idle extend3 project3 h 0 three_state_gain

def embed3 : Bool → Fin 3 := fun x => if x then 2 else 0
theorem three_state_section (x : Bool) : project3 (embed3 x) = x := by
  cases x <;> decide

theorem three_state_retains_old (x z : Bool) (h : Reachable idle x z) :
    ∃ y, Reachable extend3 (embed3 x) y ∧ project3 y = z := by
  apply old_reachable_lifts idle extend3 project3 embed3 three_state_section _ h
  intro _ y
  exact reachable_refl extend3 (embed3 y)

theorem three_state_cardinalities :
    Fintype.card Bool = 2 ∧ Fintype.card (Fin 3) = 3 := by decide

/-- Extra memory alone need not add a projected endpoint. -/
def memoryStep {X I : Type*} (old : I → X → X) :
    (I ⊕ Unit) → (X × Bool) → (X × Bool)
  | .inl i, (x, b) => (old i x, b)
  | .inr _, (x, b) => (x, !b)

theorem memory_simulated {X I : Type*} (old : I → X → X) :
    ProjectionSimulation old (memoryStep old) Prod.fst := by
  intro a y
  cases a with
  | inl i => exact reachable_step old i y.1
  | inr _ => exact reachable_refl old y.1

/-- A failed simulation even at a reachable source need not enlarge the
fixed-start reachable set: the new reset goes backward inside that set. -/
def setTrue : Unit → Bool → Bool := fun _ _ => true
def resetOrSet : Bool → Bool → Bool := fun a _ => a

theorem setTrue_run_true (w : List Unit) : run setTrue w true = true := by
  induction w with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem reset_not_simulated : ¬ ProjectionSimulation setTrue resetOrSet id := by
  intro h
  obtain ⟨w, hw⟩ := h false true
  change run setTrue w true = false at hw
  rw [setTrue_run_true] at hw
  exact Bool.false_ne_true hw.symm

theorem reset_has_no_gain : ¬ StrictGain setTrue resetOrSet id false := by
  rintro ⟨z, _, hn⟩
  apply hn
  cases z with
  | false => exact reachable_refl setTrue false
  | true => exact ⟨[()], rfl⟩

end LinearInputProjectionExamples
