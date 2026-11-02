/-!
# F0: descent of an update through idempotent forgetting

This supplement extends LinearInputF0.Idempotent and LinearInputF0.Fixed.
It distinguishes:
* a deterministic update U on the original state space;
* the observable state K x;
* the induced update on fixed representatives.

No global invertibility, optimal packing, or representation of all cellular
automata is assumed.
-/

noncomputable section

namespace LinearInputF0Descent

open LinearInputF0

/-- An update has identical observable outputs on each fiber of K. -/
def RespectsFibers {α : Type*} (K U : α → α) : Prop :=
  ∀ x y, K x = K y → K (U x) = K (U y)

/-- The update after forgetting agrees with forgetting after the update. -/
def Descends {α : Type*} (K U : α → α) : Prop :=
  ∀ x, K (U (K x)) = K (U x)

/-- Fiber invariance is exactly the descent condition for an idempotent K. -/
theorem descends_iff_respects {α : Type*} {K U : α → α}
    (hK : Idempotent K) : Descends K U ↔ RespectsFibers K U := by
  constructor
  · intro h x y hxy
    calc
      K (U x) = K (U (K x)) := (h x).symm
      _ = K (U (K y)) := congrArg (fun z => K (U z)) hxy
      _ = K (U y) := h y
  · intro h x
    exact h (K x) x (hK x)

/-- The candidate update on the fixed representatives exists for any U;
it represents the original dynamics only when the descent equation holds. -/
def induced {α : Type*} (K U : α → α) (hK : Idempotent K) :
    Fixed K → Fixed K :=
  fun a => ⟨K (U a.val), hK _⟩

/-- The observable dynamics commutes with the representative projection
precisely when U descends. -/
theorem induced_naturality {α : Type*} {K U : α → α}
    (hK : Idempotent K) (h : Descends K U) (x : α) :
    (induced K U hK ⟨K x, hK x⟩).val = K (U x) := by
  exact h x

/-- The induced observable update is unique, once naturality is required. -/
theorem induced_unique {α : Type*} {K U : α → α}
    (hK : Idempotent K) (g : Fixed K → Fixed K)
    (hg : ∀ x, (g ⟨K x, hK x⟩).val = K (U x)) :
    g = induced K U hK := by
  funext a
  have ha : (⟨K a.val, hK a.val⟩ : Fixed K) = a :=
    Subtype.ext a.property
  have hga := hg a.val
  rw [ha] at hga
  apply Subtype.ext
  exact hga

theorem identity_descends {α : Type*} {K : α → α}
    (hK : Idempotent K) : Descends K (fun x => x) := by
  exact hK

/-- Fiber-respecting updates are closed under composition. -/
theorem respects_comp {α : Type*} {K U V : α → α}
    (hU : RespectsFibers K U) (hV : RespectsFibers K V) :
    RespectsFibers K (fun x => V (U x)) := by
  intro x y hxy
  exact hV (U x) (U y) (hU x y hxy)

theorem descends_comp {α : Type*} {K U V : α → α}
    (hK : Idempotent K) (hU : Descends K U)
    (hV : Descends K V) :
    Descends K (fun x => V (U x)) := by
  apply (descends_iff_respects hK).2
  exact respects_comp ((descends_iff_respects hK).1 hU)
    ((descends_iff_respects hK).1 hV)

/-- The update on representatives is functorial for descending updates. -/
theorem induced_comp {α : Type*} {K U V : α → α}
    (hK : Idempotent K) (hV : Descends K V) (a : Fixed K) :
    induced K (fun x => V (U x)) hK a =
      induced K V hK (induced K U hK a) := by
  apply Subtype.ext
  change K (V (U a.val)) = K (V (K (U a.val)))
  exact (hV (U a.val)).symm

/-- A symmetry M commutes with an update U. -/
def Equivariant {α : Type*} (M U : α → α) : Prop :=
  ∀ x, U (M x) = M (U x)

/-- An equivariant update cannot break a symmetry already present. -/
theorem equivariant_preserves_fixed {α : Type*} {M U : α → α}
    (h : Equivariant M U) {x : α} (hx : M x = x) :
    M (U x) = U x := by
  calc
    M (U x) = U (M x) := (h x).symm
    _ = U x := congrArg U hx

/-- A three-state update exposes a distinction forgotten by exampleK. -/
def exampleUpdate (x : Fin 3) : Fin 3 := if x = 1 then 2 else x

theorem example_breaks_fiber_respect :
    ¬ RespectsFibers LinearInputF0.exampleK exampleUpdate := by
  intro h
  have heq : LinearInputF0.exampleK (0 : Fin 3) =
      LinearInputF0.exampleK (1 : Fin 3) := by decide
  have hxy := h 0 1 heq
  have hne : LinearInputF0.exampleK (exampleUpdate (0 : Fin 3)) ≠
      LinearInputF0.exampleK (exampleUpdate (1 : Fin 3)) := by decide
  exact hne hxy

theorem example_does_not_descend :
    ¬ Descends LinearInputF0.exampleK exampleUpdate := by
  intro h
  exact example_breaks_fiber_respect
    ((descends_iff_respects LinearInputF0.exampleK_idempotent).1 h)

end LinearInputF0Descent
