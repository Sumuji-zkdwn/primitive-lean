/-!
The actual interval-realized Laakso levels form a continuous surjective tower.
Compatible threads are the existing set-level inverse limit, now instantiated
with these geometric levels. Their topology is inherited from the product.
Choice supplies threads above every point of the base interval; this chosen
right inverse is not asserted continuous. No path metric, measure, dimension,
Poincare inequality, or infinite-space dynamics is introduced.
-/

noncomputable section

namespace LinearInputLaaksoGeometricTower

open LinearInputLaaksoFiniteGraph LinearInputLaaksoRealization
open LinearInputLaaksoGeometricProjection

/-- Discrete index topologies, recursively matching the refinement products. -/
abbrev edgeTopology : (n : ℕ) → TopologicalSpace (EdgeType n)
  | 0 => ⊥
  | n + 1 => by
      letI := edgeTopology n
      exact inferInstanceAs (TopologicalSpace (RefinedEdge (EdgeType n)))

attribute [instance] edgeTopology

abbrev vertexTopology : (n : ℕ) → TopologicalSpace (VertexType n)
  | 0 => ⊥
  | n + 1 => by
      letI := vertexTopology n
      exact inferInstanceAs (TopologicalSpace (RefinedVertex (VertexType n) (EdgeType n)))

attribute [instance] vertexTopology

abbrev edgeDiscrete : (n : ℕ) → DiscreteTopology (EdgeType n)
  | 0 => discreteTopology_bot _
  | n + 1 => by
      letI := edgeDiscrete n
      exact inferInstanceAs (DiscreteTopology (RefinedEdge (EdgeType n)))

attribute [instance] edgeDiscrete

abbrev vertexDiscrete : (n : ℕ) → DiscreteTopology (VertexType n)
  | 0 => discreteTopology_bot _
  | n + 1 => by
      letI := vertexDiscrete n
      exact inferInstanceAs (DiscreteTopology (RefinedVertex (VertexType n) (EdgeType n)))

attribute [instance] vertexDiscrete

abbrev Space (n : ℕ) := Realization (level n)

theorem compact_space (n : ℕ) : CompactSpace (Space n) :=
  compact_realization (level n)

def bonding (n : ℕ) : Space (n + 1) → Space n := bond (level n)

theorem continuous_bonding (n : ℕ) : Continuous (bonding n) :=
  continuous_bond (level n)

theorem bonding_surjective (n : ℕ) : Function.Surjective (bonding n) :=
  bond_surjective (level n)

/-- One choice of preimage, without any assertion that this choice is continuous. -/
def successor (n : ℕ) (x : Space n) : Space (n + 1) :=
  Classical.choose (bonding_surjective n x)

theorem bonding_successor (n : ℕ) (x : Space n) : bonding n (successor n x) = x :=
  Classical.choose_spec (bonding_surjective n x)

def coordinates (x : Space 0) : (n : ℕ) → Space n
  | 0 => x
  | n + 1 => successor n (coordinates x n)

abbrev Tower := LinearInputInverseTowerObservation.Limit Space bonding

/-- The product-subspace topology on compatible geometric coordinates. -/
abbrev towerTopology : TopologicalSpace Tower :=
  inferInstanceAs (TopologicalSpace
    {x : (n : ℕ) → Space n // ∀ n, bonding n (x (n + 1)) = x n})

attribute [instance] towerTopology

/-- These are compatible points of the actual interval-realized graphs. -/
def threadFromBase (x : Space 0) : Tower :=
  ⟨coordinates x, fun n => bonding_successor n (coordinates x n)⟩

def project (n : ℕ) : Tower → Space n :=
  LinearInputInverseTowerObservation.project Space bonding n

theorem project_compatible (n : ℕ) (x : Tower) :
    bonding n (project (n + 1) x) = project n x := x.property n

theorem continuous_project (n : ℕ) : Continuous (project n) :=
  (continuous_apply n).comp continuous_subtype_val

theorem project_zero_thread (x : Space 0) : project 0 (threadFromBase x) = x := rfl

theorem project_zero_surjective : Function.Surjective (project 0) :=
  fun x => ⟨threadFromBase x, project_zero_thread x⟩

theorem threadFromBase_injective : Function.Injective threadFromBase := by
  intro x y h
  exact congrArg (project 0) h

def baseVertexCoordinate (v : Fin 2) : unitInterval := by
  classical
  exact if v = (0 : Fin 2) then 0 else 1

theorem base_source_coordinate (e : EdgeType 0) :
    (0 : unitInterval) = baseVertexCoordinate ((level 0).1 e) := by
  simp [baseVertexCoordinate, level, base]

theorem base_target_coordinate (e : EdgeType 0) :
    (1 : unitInterval) = baseVertexCoordinate ((level 0).2 e) := by
  simp [baseVertexCoordinate, level, base]

def baseCoordinate : Space 0 → unitInterval :=
  lift (level 0) baseVertexCoordinate (fun _ u => u)
    base_source_coordinate base_target_coordinate

def basePoint (u : unitInterval) : Space 0 := edgePoint (level 0) (0 : Fin 1) u

theorem baseCoordinate_basePoint (u : unitInterval) : baseCoordinate (basePoint u) = u := rfl

theorem continuous_baseCoordinate : Continuous baseCoordinate :=
  continuous_lift (level 0) baseVertexCoordinate (fun _ u => u)
    base_source_coordinate base_target_coordinate continuous_of_discreteTopology continuous_snd

theorem basePoint_baseCoordinate (x : Space 0) : basePoint (baseCoordinate x) = x := by
  rcases realization_cases (level 0) x with ⟨v, rfl⟩ | ⟨e, u, rfl⟩
  · change basePoint (baseVertexCoordinate v) = vertexPoint (level 0) v
    change Fin 2 at v
    fin_cases v
    · simpa [basePoint, baseVertexCoordinate, level, base] using
        edgePoint_zero (level 0) (0 : Fin 1)
    · simpa [basePoint, baseVertexCoordinate, level, base] using
        edgePoint_one (level 0) (0 : Fin 1)
  · change basePoint u = edgePoint (level 0) e u
    have he : e = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ e 0
    rw [he]
    rfl

/-- The zeroth geometric level is exactly the closed unit interval. -/
def baseHomeomorph : Space 0 ≃ₜ unitInterval where
  toFun := baseCoordinate
  invFun := basePoint
  left_inv := basePoint_baseCoordinate
  right_inv := baseCoordinate_basePoint
  continuous_toFun := continuous_baseCoordinate
  continuous_invFun := continuous_edgePoint (level 0) (0 : Fin 1)

/-- The horizontal coordinate, read through the base interval. -/
def evaluation (x : Tower) : unitInterval := baseCoordinate (project 0 x)

theorem continuous_evaluation : Continuous evaluation :=
  continuous_baseCoordinate.comp (continuous_project 0)

def intervalThread (u : unitInterval) : Tower := threadFromBase (basePoint u)

theorem evaluation_intervalThread (u : unitInterval) : evaluation (intervalThread u) = u := rfl

theorem evaluation_surjective : Function.Surjective evaluation :=
  fun u => ⟨intervalThread u, evaluation_intervalThread u⟩

theorem intervalThread_injective : Function.Injective intervalThread := by
  intro u v h
  exact congrArg evaluation h

theorem tower_nonempty : Nonempty Tower := ⟨intervalThread 0⟩

theorem interval_threads_zero_one_distinct : intervalThread 0 ≠ intervalThread 1 := by
  intro h
  have h01 : (0 : unitInterval) = 1 := congrArg evaluation h
  have hr := congrArg (fun u : unitInterval => (u : ℝ)) h01
  norm_num at hr

/-- The base coordinate pulled back through all intervening actual bond maps. -/
def heightAt : (n : ℕ) → Space n → unitInterval
  | 0 => baseCoordinate
  | n + 1 => fun x => heightAt n (bonding n x)

theorem continuous_heightAt (n : ℕ) : Continuous (heightAt n) := by
  induction n with
  | zero => exact continuous_baseCoordinate
  | succ n ih => exact ih.comp (continuous_bonding n)

theorem heightAt_project (x : Tower) (n : ℕ) : heightAt n (project n x) = evaluation x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change heightAt n (bonding n (project (n + 1) x)) = evaluation x
      rw [project_compatible, ih]

end LinearInputLaaksoGeometricTower

end
