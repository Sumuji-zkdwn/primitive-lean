/-!
The exact singleton Galois closure for the Stops relation.

For operators with at least one fixed and one nonfixed state, the relational
closure is precisely the family with the same fixed-point set. This theorem
explains both the special spike-orbit result and the non-idempotent boundary.
The other two cases (every state fixed or no state fixed) give universal closure.
-/

namespace LinearInputStrangeFixedSets

open LinearInputStrangeGalois LinearInputStrangeConjugacy

universe u

def FixedStates {α : Type u} (S : α → α) : Set α :=
  {x | S x = x}

/-- Stops observes only the fixed-point subset, never the other outputs. -/
theorem stops_equiv_of_fixed {α : Type u} (T S U : α → α)
    (hFix : FixedStates S = FixedStates U) :
    Stops T S ↔ Stops T U := by
  have hfx : ∀ x : α, S x = x ↔ U x = x := by
    intro x
    exact Set.ext_iff.mp hFix x
  constructor
  · rintro ⟨x, hx, hst⟩
    refine ⟨x, ?_, (hfx (T x)).mp hst⟩
    intro hUx
    exact hx ((hfx x).mpr hUx)
  · rintro ⟨x, hx, hst⟩
    refine ⟨x, ?_, (hfx (T x)).mpr hst⟩
    intro hSx
    exact hx ((hfx x).mp hSx)

/-- Every map with the same fixed-point set is in the singleton closure. -/
theorem same_fixed_in_closure {α : Type u} (S U : α → α)
    (hFix : FixedStates S = FixedStates U) :
    U ∈ Close (Stops (α := α)) ({S} : Set (α → α)) := by
  intro T hT
  exact (stops_equiv_of_fixed T S U hFix).mp (hT S rfl)

/--
Complete characterization of singleton closures when the fixed-point set
is nonempty and proper, without requiring finiteness or idempotence.
-/
theorem close_singleton_exact_fixed_set {α : Type u} (S : α → α)
    (hFixed : ∃ a : α, S a = a)
    (hActive : ∃ b : α, S b ≠ b) :
    Close (Stops (α := α)) ({S} : Set (α → α)) =
      {U | FixedStates U = FixedStates S} := by
  obtain ⟨a, ha⟩ := hFixed
  obtain ⟨b, hb⟩ := hActive
  apply Set.ext
  intro U
  constructor
  · intro hclosed
    have htest (T : α → α) (hStop : Stops T S) :
        T ∈ LeftPolar (Stops (α := α)) ({S} : Set (α → α)) := by
      intro V hV
      have hVS : V = S := Set.mem_singleton_iff.mp hV
      subst V
      exact hStop
    have hForward : ∀ y : α, S y = y → U y = y := by
      intro y hy
      have hconst : Stops (fun _ : α => y) S :=
        ⟨b, hb, by simpa using hy⟩
      obtain ⟨x, hx, hUy⟩ :=
        hclosed (fun _ : α => y) (htest _ hconst)
      exact hUy
    have hBackward : ∀ y : α, U y = y → S y = y := by
      intro y hy
      by_contra hSy
      have hSp : Stops (Spike y a) S := by
        refine ⟨y, hSy, ?_⟩
        simpa [Spike] using ha
      obtain ⟨x, hx, hUtx⟩ :=
        hclosed (Spike y a) (htest _ hSp)
      by_cases hxy : x = y
      · subst x
        exact hx hy
      · have htx : Spike y a x = x := by
          simp [Spike, hxy]
        exact hx (by simpa [htx] using hUtx)
    apply Set.ext
    intro y
    exact ⟨hBackward y, hForward y⟩
  · intro hFix
    exact same_fixed_in_closure S U hFix.symm

/-- When no test can stop S, its Galois closure is the whole operator space. -/
theorem close_singleton_top_of_no_stoppers {α : Type u} (S : α → α)
    (hNo : ∀ T : α → α, ¬ Stops T S) :
    Close (Stops (α := α)) ({S} : Set (α → α)) = Set.univ := by
  apply Set.ext
  intro U
  constructor
  · intro _
    exact Set.mem_univ U
  · intro _ T hT
    exact (hNo T (hT S rfl)).elim

/-- The totally fixed case has no stopping tests. -/
theorem close_singleton_top_of_all_fixed {α : Type u} (S : α → α)
    (hAll : ∀ x : α, S x = x) :
    Close (Stops (α := α)) ({S} : Set (α → α)) = Set.univ := by
  apply close_singleton_top_of_no_stoppers S
  intro T
  rintro ⟨x, hx, hTx⟩
  exact hx (hAll x)

/-- The fixed-point-free case also has no stopping tests. -/
theorem close_singleton_top_of_no_fixed {α : Type u} (S : α → α)
    (hNone : ∀ x : α, S x ≠ x) :
    Close (Stops (α := α)) ({S} : Set (α → α)) = Set.univ := by
  apply close_singleton_top_of_no_stoppers S
  intro T
  rintro ⟨x, hx, hTx⟩
  exact hNone (T x) hTx

end LinearInputStrangeFixedSets
