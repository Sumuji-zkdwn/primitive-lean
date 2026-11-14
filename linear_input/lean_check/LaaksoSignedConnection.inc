/-!
The signed two-sheet lift of the actual six-edge first Laakso graph.
Reachability is the reflexive transitive closure of undirected incidence.
Only labelled middle edge 3 is flipped; no metric or limit claim is made.
-/

namespace LinearInputLaaksoSigned

open LinearInputLaaksoFiniteGraph

abbrev Twist := Fin 6 → Bool

def untwisted : Twist := fun _ => false

def flipped : Twist := fun e => decide (e = 3)

def sign (τ : Twist) (e : Fin 6) : ℝ := if τ e then -1 else 1

theorem sign_untwisted (e : Fin 6) : sign untwisted e = 1 := rfl

theorem sign_flipped_three : sign flipped 3 = -1 := rfl

theorem sign_flipped_of_ne (e : Fin 6) (h : e ≠ 3) : sign flipped e = 1 := by
  simp [sign, flipped, h]

theorem flipped_only_middle (e : Fin 6) : flipped e ≠ untwisted e ↔ e = 3 := by
  simp [flipped, untwisted]

abbrev LiftVertex := Fin 6 × Bool
abbrev LiftEdge := Fin 6 × Bool

def liftSource : LiftEdge → LiftVertex := fun e => (firstSource e.1, e.2)

def liftTarget (τ : Twist) : LiftEdge → LiftVertex :=
  fun e => (firstTarget e.1, xor e.2 (τ e.1))

def liftGraph (τ : Twist) : Graph LiftVertex LiftEdge := ⟨liftSource, liftTarget τ⟩

theorem lift_vertex_card : Fintype.card LiftVertex = 12 := by decide

theorem lift_edge_card : Fintype.card LiftEdge = 12 := by decide

/-- Both orientations of every labelled lifted edge are allowed. -/
abbrev Adj (τ : Twist) (x y : LiftVertex) : Prop :=
  ∃ e : LiftEdge,
    (liftSource e = x ∧ liftTarget τ e = y) ∨
    (liftSource e = y ∧ liftTarget τ e = x)

def Reach (τ : Twist) : LiftVertex → LiftVertex → Prop :=
  Relation.ReflTransGen (Adj τ)

theorem adj_symm (τ : Twist) {x y : LiftVertex} (h : Adj τ x y) : Adj τ y x := by
  obtain ⟨e, h⟩ := h
  exact ⟨e, h.symm⟩

theorem reach_symm (τ : Twist) {x y : LiftVertex} (h : Reach τ x y) :
    Reach τ y x := by
  let : Std.Symm (Adj τ) := ⟨fun _ _ => adj_symm τ⟩
  change Relation.ReflTransGen (Adj τ) y x
  exact symm h

/-- A finite, checkable witness format used only to construct genuine paths. -/
abbrev TwoStep (τ : Twist) (x y : LiftVertex) : Prop :=
  x = y ∨ Adj τ x y ∨ ∃ z : LiftVertex, Adj τ x z ∧ Adj τ z y

theorem twoStep_reach (τ : Twist) {x y : LiftVertex} (h : TwoStep τ x y) :
    Reach τ x y := by
  rcases h with h | h | ⟨z, hxz, hzy⟩
  · subst y
    exact .refl
  · exact .single h
  · exact (Relation.ReflTransGen.single hxz).trans (.single hzy)

theorem untwisted_to_root (v : Fin 6) (b : Bool) :
    Reach untwisted (v, b) (4, b) := by
  apply twoStep_reach
  revert v b
  decide

theorem flipped_to_root (v : Fin 6) (b : Bool) :
    Reach flipped (v, b) (4, b) := by
  apply twoStep_reach
  revert v b
  decide

theorem untwisted_adj_layer {x y : LiftVertex} (h : Adj untwisted x y) :
    x.2 = y.2 := by
  obtain ⟨e, h | h⟩ := h
  · rcases h with ⟨rfl, rfl⟩
    simp [liftSource, liftTarget, untwisted]
  · rcases h with ⟨rfl, rfl⟩
    simp [liftSource, liftTarget, untwisted]

theorem untwisted_reach_layer {x y : LiftVertex} (h : Reach untwisted x y) :
    x.2 = y.2 := by
  induction h with
  | refl => rfl
  | tail hxy hyz ih => exact ih.trans (untwisted_adj_layer hyz)

theorem untwisted_reach_iff (x y : LiftVertex) :
    Reach untwisted x y ↔ x.2 = y.2 := by
  constructor
  · exact untwisted_reach_layer
  · rcases x with ⟨v, b⟩
    rcases y with ⟨w, c⟩
    intro h
    change b = c at h
    subst c
    exact (untwisted_to_root v b).trans (reach_symm untwisted (untwisted_to_root w b))

/-- The two distinct middle edges form a path switching sheets. -/
theorem flipped_root_switch (b c : Bool) : Reach flipped (4, b) (4, c) := by
  cases b <;> cases c <;> apply twoStep_reach flipped <;> decide

theorem flipped_fully_connected (x y : LiftVertex) : Reach flipped x y := by
  exact (flipped_to_root x.1 x.2).trans
    ((flipped_root_switch x.2 y.2).trans (reach_symm flipped (flipped_to_root y.1 y.2)))

theorem untwisted_sheets_separate : ¬ Reach untwisted (4, false) (4, true) := by
  rw [untwisted_reach_iff]
  decide

noncomputable abbrev reachableFintype (τ : Twist) (x : LiftVertex) :
    Fintype {y : LiftVertex // Reach τ x y} := Fintype.ofFinite _

attribute [instance] reachableFintype

theorem untwisted_reachable_card (x : LiftVertex) :
    Fintype.card {y : LiftVertex // Reach untwisted x y} = 6 := by
  let e : {y : LiftVertex // Reach untwisted x y} ≃ Fin 6 :=
    { toFun := fun y => y.val.1
      invFun := fun v => ⟨(v, x.2), (untwisted_reach_iff x (v, x.2)).mpr rfl⟩
      left_inv := by
        rintro ⟨⟨v, b⟩, h⟩
        apply Subtype.ext
        exact Prod.ext rfl ((untwisted_reach_iff x (v, b)).mp h)
      right_inv := fun _ => rfl }
  calc
    Fintype.card {y : LiftVertex // Reach untwisted x y} = Fintype.card (Fin 6) :=
      Fintype.card_congr e
    _ = 6 := by decide

theorem flipped_reachable_card (x : LiftVertex) :
    Fintype.card {y : LiftVertex // Reach flipped x y} = 12 := by
  let e : {y : LiftVertex // Reach flipped x y} ≃ LiftVertex :=
    { toFun := Subtype.val
      invFun := fun y => ⟨y, flipped_fully_connected x y⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans lift_vertex_card

def middleParity (τ : Twist) : Bool := xor (τ 2) (τ 3)

theorem untwisted_middle_parity : middleParity untwisted = false := rfl

theorem flipped_middle_parity : middleParity flipped = true := rfl

abbrev Spin := Fin 6 → Bool

/-- A global binary classification consistent with every signed base edge. -/
def Compatible (τ : Twist) (s : Spin) : Prop :=
  ∀ e : Fin 6, s (firstTarget e) = xor (s (firstSource e)) (τ e)

theorem compatible_middle_parity {τ : Twist} {s : Spin} (h : Compatible τ s) :
    middleParity τ = false := by
  have h₂ := h 2
  have h₃ := h 3
  change s 5 = xor (s 4) (τ 2) at h₂
  change s 5 = xor (s 4) (τ 3) at h₃
  cases h4 : s 4 <;> cases h5 : s 5 <;>
    cases h2 : τ 2 <;> cases h3 : τ 3 <;>
    simp_all [middleParity]

theorem untwisted_has_spin : ∃ s : Spin, Compatible untwisted s := by
  exact ⟨fun _ => false, fun _ => rfl⟩

theorem flipped_no_spin : ¬ ∃ s : Spin, Compatible flipped s := by
  rintro ⟨s, hs⟩
  have h := compatible_middle_parity hs
  rw [flipped_middle_parity] at h
  contradiction

end LinearInputLaaksoSigned
