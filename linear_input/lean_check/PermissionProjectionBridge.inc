/-! Adapter to the exact PR #145 definitions. Available external permissions
are part of the semantics; a compiler may not silently use an unavailable gate. -/
namespace Elastica.ChairPieProjection

open LinearInputOperatorReachability LinearInputProjectionReachability

abbrev Permitted {I G : Type*} [DecidableEq G] (A : Finset G) :=
  {a : I ⊕ G // Elastica.ChairPieKillSpot.Allowed A [a]}

def permittedStep {I G X : Type*} [DecidableEq G]
    (step : (I ⊕ G) → X → X) (A : Finset G) : Permitted (I := I) A → X → X :=
  fun a => step a.val

private theorem allowed_map {I G : Type*} [DecidableEq G]
    (A : Finset G) (w : List (Permitted (I := I) A)) :
    Elastica.ChairPieKillSpot.Allowed A (w.map Subtype.val) := by
  intro a ha
  obtain ⟨b, _, hb⟩ := List.mem_map.mp ha
  subst a
  exact b.property b.val (by simp)

private theorem lift_allowed {I G : Type*} [DecidableEq G]
    (A : Finset G) (w : List (I ⊕ G)) (hw : Elastica.ChairPieKillSpot.Allowed A w) :
    ∃ v : List (Permitted (I := I) A), v.map Subtype.val = w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons a w ih =>
      have ha : Elastica.ChairPieKillSpot.Allowed A [a] := by
        intro b hb
        have he : b = a := by simpa using hb
        subst b
        exact hw a (by simp)
      obtain ⟨v, hv⟩ := ih (by
        intro b hb
        exact hw b (by simp [hb]))
      exact ⟨⟨a, ha⟩ :: v, by simp [hv]⟩

private theorem run_permitted {I G X : Type*} [DecidableEq G]
    (step : (I ⊕ G) → X → X) (A : Finset G)
    (w : List (Permitted (I := I) A)) (x : X) :
    LinearInputOperatorWords.run (permittedStep step A) w x = Elastica.ChairPieKillSpot.run step (w.map Subtype.val) x := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih => exact ih (step a.val x)

/-- Exact bridge, not a replacement definition or analogy. -/
theorem revenue_iff_reachable {I G X : Type*} [DecidableEq G]
    (step : (I ⊕ G) → X → X) (A : Finset G) (s : X) (goal : X → Prop) :
    Elastica.ChairPieKillSpot.RevenuePossible step s goal A ↔
      ∃ z, Reachable (permittedStep step A) s z ∧ goal z := by
  constructor
  · rintro ⟨w, hw, hg⟩
    obtain ⟨v, hv⟩ := lift_allowed A w hw
    refine ⟨Elastica.ChairPieKillSpot.run step w s, ⟨v, ?_⟩, hg⟩
    rw [run_permitted, hv]
  · rintro ⟨z, ⟨w, hw⟩, hg⟩
    refine ⟨w.map Subtype.val, allowed_map A w, ?_⟩
    rw [← run_permitted, hw]
    exact hg

def PermissionSimulation {I J G X Y : Type*} [DecidableEq G]
    (old : (I ⊕ G) → X → X) (fresh : (J ⊕ G) → Y → Y)
    (A B : Finset G) (π : Y → X) : Prop :=
  ProjectionSimulation (permittedStep old A) (permittedStep fresh B) π

/-- Goals are compared through the projection, with explicit old/new gates. -/
theorem revenue_of_permission_simulation {I J G X Y : Type*} [DecidableEq G]
    (old : (I ⊕ G) → X → X) (fresh : (J ⊕ G) → Y → Y)
    (A B : Finset G) (π : Y → X) (s : Y) (goal : X → Prop)
    (hsim : PermissionSimulation old fresh A B π)
    (h : Elastica.ChairPieKillSpot.RevenuePossible fresh s (fun y => goal (π y)) B) :
    Elastica.ChairPieKillSpot.RevenuePossible old (π s) goal A := by
  obtain ⟨z, hz, hg⟩ := (revenue_iff_reachable fresh B s _).mp h
  apply (revenue_iff_reachable old A (π s) goal).mpr
  exact ⟨π z, projection_reachable _ _ π hsim hz, hg⟩

/-- Apply the same gate removal before checking simulation. -/
theorem blocks_of_permission_simulation {I J G X Y : Type*} [DecidableEq G]
    (old : (I ⊕ G) → X → X) (fresh : (J ⊕ G) → Y → Y)
    (E K : Finset G) (π : Y → X) (s : Y) (goal : X → Prop)
    (hsim : PermissionSimulation old fresh (E \ K) (E \ K) π)
    (hb : Elastica.ChairPieKillSpot.Blocks (Elastica.ChairPieKillSpot.RevenuePossible old (π s) goal) E K) :
    Elastica.ChairPieKillSpot.Blocks (Elastica.ChairPieKillSpot.RevenuePossible fresh s (fun y => goal (π y))) E K := by
  intro h
  exact hb (revenue_of_permission_simulation old fresh _ _ π s goal hsim h)

end Elastica.ChairPieProjection
