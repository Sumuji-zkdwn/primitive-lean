/-!
Additive supplement after OperatorReachability.inc. No upstream definition
is changed. Projection simulations permit zero or more old steps and permit
the old word to depend on the current new state.
-/
namespace LinearInputProjectionReachability

open LinearInputOperatorWords LinearInputOperatorReachability

/-- Every new step has an old finite-word witness after projection.
No finiteness, surjectivity, or state-independent compiler is assumed. -/
def ProjectionSimulation {X Y I J : Type*}
    (old : I → X → X) (fresh : J → Y → Y) (π : Y → X) : Prop :=
  ∀ j y, Reachable old (π y) (π (fresh j y))

theorem projection_run {X Y I J : Type*}
    (old : I → X → X) (fresh : J → Y → Y) (π : Y → X)
    (h : ProjectionSimulation old fresh π) (w : List J) (y : Y) :
    Reachable old (π y) (π (run fresh w y)) := by
  induction w generalizing y with
  | nil => exact reachable_refl old (π y)
  | cons j w ih => exact reachable_trans old (h j y) (ih (fresh j y))

/-- Forward preservation of projected reachability. -/
theorem projection_reachable {X Y I J : Type*}
    (old : I → X → X) (fresh : J → Y → Y) (π : Y → X)
    (h : ProjectionSimulation old fresh π) {y z : Y}
    (hz : Reachable fresh y z) : Reachable old (π y) (π z) := by
  obtain ⟨w, hw⟩ := hz
  rw [← hw]
  exact projection_run old fresh π h w y

/-- Globally, local simulation and preservation for every pair are equivalent.
This equivalence does NOT replace the fixed-start criterion below. -/
theorem simulation_iff_all_reachability {X Y I J : Type*}
    (old : I → X → X) (fresh : J → Y → Y) (π : Y → X) :
    ProjectionSimulation old fresh π ↔
      ∀ y z, Reachable fresh y z → Reachable old (π y) (π z) := by
  constructor
  · intro h y z hz
    exact projection_reachable old fresh π h hz
  · intro h j y
    exact h y (fresh j y) (reachable_step fresh j y)

/-- A uniform compiler is a sufficient, stronger assumption. -/
theorem simulation_of_compiler {X Y I J : Type*}
    (old : I → X → X) (fresh : J → Y → Y) (π : Y → X)
    (code : J → List I)
    (hc : ∀ j y, run old (code j) (π y) = π (fresh j y)) :
    ProjectionSimulation old fresh π := by
  intro j y
  exact ⟨code j, hc j y⟩

/-- The generated-word case of the existing supplement, now as a simulation. -/
theorem generated_projection_simulation {X I J : Type*}
    (old : I → X → X) (code : J → List I) :
    ProjectionSimulation old (generated old code) id :=
  simulation_of_compiler old (generated old code) id code (by intros; rfl)

/-- A new projected endpoint unavailable from the same projected start. -/
def StrictGain {X Y I J : Type*}
    (old : I → X → X) (fresh : J → Y → Y) (π : Y → X) (start : Y) : Prop :=
  ∃ z, Reachable fresh start z ∧ ¬ Reachable old (π start) (π z)

theorem no_gain_of_simulation {X Y I J : Type*}
    (old : I → X → X) (fresh : J → Y → Y) (π : Y → X)
    (h : ProjectionSimulation old fresh π) (start : Y) :
    ¬ StrictGain old fresh π start := by
  rintro ⟨z, hz, hn⟩
  exact hn (projection_reachable old fresh π h hz)

private theorem first_exit {Y J : Type*} (fresh : J → Y → Y)
    (P : Y → Prop) (w : List J) (s : Y) (hs : P s)
    (hend : ¬ P (run fresh w s)) :
    ∃ y j, Reachable fresh s y ∧ P y ∧ ¬ P (fresh j y) := by
  classical
  induction w generalizing s with
  | nil => exact False.elim (hend hs)
  | cons j w ih =>
      by_cases hn : P (fresh j s)
      · obtain ⟨y, k, hy, hp, he⟩ := ih (fresh j s) hn hend
        exact ⟨y, k, reachable_after_action fresh j hy, hp, he⟩
      · exact ⟨s, j, reachable_refl fresh s, hs, hn⟩

/-- Exact fixed-start criterion: some reachable prefix crosses from inside
the old start's reachable set to outside it. Failure to simulate a step
from its own source alone is not sufficient. -/
theorem strictGain_iff_escape {X Y I J : Type*}
    (old : I → X → X) (fresh : J → Y → Y) (π : Y → X) (s : Y) :
    StrictGain old fresh π s ↔
      ∃ y j, Reachable fresh s y ∧ Reachable old (π s) (π y) ∧
        ¬ Reachable old (π s) (π (fresh j y)) := by
  constructor
  · rintro ⟨z, ⟨w, hw⟩, hn⟩
    apply first_exit fresh (fun y => Reachable old (π s) (π y)) w s
      (reachable_refl old (π s))
    simpa only [hw] using hn
  · rintro ⟨y, j, hy, _, hn⟩
    exact ⟨fresh j y, reachable_trans fresh hy (reachable_step fresh j y), hn⟩

/-- Old behavior is retained if an initial-state-compatible section lifts
each old primitive to a finite new word. Together with StrictGain this
gives strict inclusion, rather than merely incomparable reachable sets. -/
theorem old_reachable_lifts {X Y I J : Type*}
    (old : I → X → X) (fresh : J → Y → Y) (π : Y → X)
    (embed : X → Y) (section_law : ∀ x, π (embed x) = x)
    (hlift : ProjectionSimulation fresh old embed)
    {x z : X} (hz : Reachable old x z) :
    ∃ y, Reachable fresh (embed x) y ∧ π y = z := by
  exact ⟨embed z, projection_reachable fresh old embed hlift hz, section_law z⟩

/-- A projection into a one-state old system can never have StrictGain. -/
theorem no_gain_subsingleton {X Y I J : Type*} [Subsingleton X]
    (old : I → X → X) (fresh : J → Y → Y) (π : Y → X) (s : Y) :
    ¬ StrictGain old fresh π s := by
  rintro ⟨z, _, hn⟩
  apply hn
  rw [Subsingleton.elim (π z) (π s)]
  exact reachable_refl old (π s)

/-- Two distinct projected states are necessary for any gain. -/
theorem gain_has_distinct_projections {X Y I J : Type*}
    (old : I → X → X) (fresh : J → Y → Y) (π : Y → X) (s : Y)
    (h : StrictGain old fresh π s) : ∃ z, π s ≠ π z := by
  obtain ⟨z, _, hn⟩ := h
  refine ⟨z, ?_⟩
  intro he
  apply hn
  rw [← he]
  exact reachable_refl old (π s)

/-- State-cardinality minimality: gain needs at least two old states;
a strictly larger finite carrier consequently needs at least three. -/
theorem gain_cardinality_bounds {X Y I J : Type*} [Fintype X] [Fintype Y]
    (old : I → X → X) (fresh : J → Y → Y) (π : Y → X) (s : Y)
    (h : StrictGain old fresh π s) :
    2 ≤ Fintype.card X ∧
      (Fintype.card X < Fintype.card Y → 3 ≤ Fintype.card Y) := by
  classical
  obtain ⟨z, hz⟩ := gain_has_distinct_projections old fresh π s h
  have hx : 2 ≤ Fintype.card X := by
    simpa [hz] using
      (Finset.card_le_card (Finset.subset_univ ({π s, π z} : Finset X)))
  omega

end LinearInputProjectionReachability
