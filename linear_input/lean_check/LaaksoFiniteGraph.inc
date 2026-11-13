/-!
Finite Laakso-style graph refinement. Edges are labelled: the two middle
edges of the first refinement are different even though their endpoints agree.
No metric realization, inverse-limit space, dimension or PI claim is made here.
-/

namespace LinearInputLaaksoFiniteGraph

abbrev Graph (V E : Type) := (E → V) × (E → V)

abbrev RefinedVertex (V E : Type) := (V × Bool) ⊕ (E × Fin 2)
abbrev RefinedEdge (E : Type) := E × Bool × Fin 3
abbrev RawVertex (V E : Type) := (V ⊕ (E × Fin 2)) × Bool

def refineSource {V E : Type} (G : Graph V E) : RefinedEdge E → RefinedVertex V E
  | (e, b, k) =>
      if k = 0 then .inl (G.1 e, b)
      else if k = 1 then .inr (e, 0) else .inr (e, 1)

def refineTarget {V E : Type} (G : Graph V E) : RefinedEdge E → RefinedVertex V E
  | (e, b, k) =>
      if k = 0 then .inr (e, 0)
      else if k = 1 then .inr (e, 1) else .inl (G.2 e, b)

def refine {V E : Type} (G : Graph V E) :
    Graph (RefinedVertex V E) (RefinedEdge E) :=
  ⟨refineSource G, refineTarget G⟩

/-- Keep the sheet on old vertices; glue the two copies of each new vertex. -/
def rawProjection {V E : Type} : RawVertex V E → RefinedVertex V E
  | (.inl v, b) => .inl (v, b)
  | (.inr w, _) => .inr w

def RawRelated {V E : Type} : RawVertex V E → RawVertex V E → Prop
  | (.inl v, b), (.inl w, c) => v = w ∧ b = c
  | (.inr v, _), (.inr w, _) => v = w
  | _, _ => False

theorem rawProjection_eq_iff {V E : Type} (x y : RawVertex V E) :
    rawProjection x = rawProjection y ↔ RawRelated x y := by
  rcases x with ⟨x, b⟩
  rcases y with ⟨y, c⟩
  cases x <;> cases y <;> simp [rawProjection, RawRelated, Prod.mk.injEq]

theorem rawProjection_surjective {V E : Type} :
    Function.Surjective (@rawProjection V E) := by
  intro x
  rcases x with ⟨v, b⟩ | w
  · exact ⟨(.inl v, b), rfl⟩
  · exact ⟨(.inr w, false), rfl⟩

def rawSetoid (V E : Type) : Setoid (RawVertex V E) where
  r := RawRelated
  iseqv := by
    constructor
    · intro x
      exact (rawProjection_eq_iff x x).mp rfl
    · intro x y h
      exact (rawProjection_eq_iff y x).mp ((rawProjection_eq_iff x y).mpr h).symm
    · intro x y z hxy hyz
      exact (rawProjection_eq_iff x z).mp
        (((rawProjection_eq_iff x y).mpr hxy).trans
          ((rawProjection_eq_iff y z).mpr hyz))

def quotientProjection {V E : Type} :
    Quotient (rawSetoid V E) → RefinedVertex V E :=
  Quotient.lift rawProjection (fun x y h => (rawProjection_eq_iff x y).mpr h)

theorem quotientProjection_bijective {V E : Type} :
    Function.Bijective (@quotientProjection V E) := by
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b h
    exact Quotient.sound ((rawProjection_eq_iff a b).mp h)
  · intro y
    obtain ⟨x, hx⟩ := rawProjection_surjective y
    exact ⟨Quotient.mk (rawSetoid V E) x, hx⟩

noncomputable def rawQuotientEquiv (V E : Type) :
    Quotient (rawSetoid V E) ≃ RefinedVertex V E :=
  Equiv.ofBijective quotientProjection quotientProjection_bijective

theorem old_vertices_keep_sheet {V E : Type} (v : V) :
    rawProjection (E := E) (.inl v, false) ≠ rawProjection (.inl v, true) := by
  simp [rawProjection]

theorem new_vertices_glue_sheets {V E : Type} (w : E × Fin 2) :
    rawProjection (V := V) (.inr w, false) = rawProjection (.inr w, true) := rfl

def base : Graph (Fin 2) (Fin 1) := ⟨fun _ => 0, fun _ => 1⟩

def EdgeType : ℕ → Type
  | 0 => Fin 1
  | n + 1 => RefinedEdge (EdgeType n)

def VertexType : ℕ → Type
  | 0 => Fin 2
  | n + 1 => RefinedVertex (VertexType n) (EdgeType n)

abbrev edgeFintype (n : ℕ) : Fintype (EdgeType n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 1))
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (Fintype (RefinedEdge (EdgeType n)))

attribute [instance] edgeFintype

abbrev vertexFintype (n : ℕ) : Fintype (VertexType n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 2))
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (Fintype (RefinedVertex (VertexType n) (EdgeType n)))

attribute [instance] vertexFintype

def level : (n : ℕ) → Graph (VertexType n) (EdgeType n)
  | 0 => base
  | n + 1 => refine (level n)

theorem edge_card_succ (n : ℕ) :
    Fintype.card (EdgeType (n + 1)) = 6 * Fintype.card (EdgeType n) := by
  rw [Fintype.card_eq_nat_card]
  change Nat.card (EdgeType n × Bool × Fin 3) = _
  rw [Nat.card_prod, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_bool, Fintype.card_fin]
  omega

theorem vertex_card_succ (n : ℕ) :
    Fintype.card (VertexType (n + 1)) =
      2 * Fintype.card (VertexType n) + 2 * Fintype.card (EdgeType n) := by
  rw [Fintype.card_eq_nat_card]
  change Nat.card ((VertexType n × Bool) ⊕ (EdgeType n × Fin 2)) = _
  rw [Nat.card_sum, Nat.card_prod, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_bool, Fintype.card_fin]
  omega

theorem edge_card (n : ℕ) : Fintype.card (EdgeType n) = 6 ^ n := by
  induction n with
  | zero => simp [EdgeType]
  | succ n ih => rw [edge_card_succ, ih, pow_succ]; omega

/-- An integral form of the vertex count, including level zero. -/
theorem twice_vertex_card (n : ℕ) :
    2 * Fintype.card (VertexType n) = 6 ^ n + 3 * 2 ^ n := by
  induction n with
  | zero =>
      rw [Fintype.card_eq_nat_card]
      change 2 * Nat.card (Fin 2) = _
      norm_num
  | succ n ih =>
      rw [vertex_card_succ, edge_card, pow_succ, pow_succ]
      omega

theorem first_vertex_card : Fintype.card (VertexType 1) = 6 := by
  have h := twice_vertex_card 1
  norm_num at h
  omega

theorem first_edge_card : Fintype.card (EdgeType 1) = 6 := by
  simpa using edge_card 1

/-- Public first-level numbering: L0,L1,R0,R1,W1,W2. -/
def firstSource : Fin 6 → Fin 6 := ![0, 1, 4, 4, 5, 5]
def firstTarget : Fin 6 → Fin 6 := ![4, 4, 5, 5, 2, 3]
def firstGraph : Graph (Fin 6) (Fin 6) := ⟨firstSource, firstTarget⟩

def firstVertexEncode : RefinedVertex (Fin 2) (Fin 1) → Fin 6
  | .inl (v, b) => if v = 0 then (if b then 1 else 0) else (if b then 3 else 2)
  | .inr (_, k) => if k = 0 then 4 else 5

def firstVertexDecode : Fin 6 → RefinedVertex (Fin 2) (Fin 1) :=
  ![.inl (0, false), .inl (0, true), .inl (1, false),
    .inl (1, true), .inr (0, 0), .inr (0, 1)]

def firstVertexEquiv : RefinedVertex (Fin 2) (Fin 1) ≃ Fin 6 where
  toFun := firstVertexEncode
  invFun := firstVertexDecode
  left_inv := by
    intro x
    rcases x with ⟨v, b⟩ | ⟨e, k⟩
    · fin_cases v <;> cases b <;> rfl
    · fin_cases e; fin_cases k <;> rfl
  right_inv := by intro v; fin_cases v <;> rfl

def firstEdgeEncode : RefinedEdge (Fin 1) → Fin 6
  | (_, b, k) =>
      if k = 0 then (if b then 1 else 0)
      else if k = 1 then (if b then 3 else 2) else (if b then 5 else 4)

def firstEdgeDecode : Fin 6 → RefinedEdge (Fin 1) :=
  ![(0, false, 0), (0, true, 0), (0, false, 1),
    (0, true, 1), (0, false, 2), (0, true, 2)]

def firstEdgeEquiv : RefinedEdge (Fin 1) ≃ Fin 6 where
  toFun := firstEdgeEncode
  invFun := firstEdgeDecode
  left_inv := by
    rintro ⟨e, b, k⟩
    fin_cases e; cases b <;> fin_cases k <;> rfl
  right_inv := by intro e; fin_cases e <;> rfl

theorem first_source_compatible (e : RefinedEdge (Fin 1)) :
    firstVertexEquiv ((refine base).1 e) = firstSource (firstEdgeEquiv e) := by
  rcases e with ⟨e, b, k⟩
  fin_cases e; cases b <;> fin_cases k <;> rfl

theorem first_target_compatible (e : RefinedEdge (Fin 1)) :
    firstVertexEquiv ((refine base).2 e) = firstTarget (firstEdgeEquiv e) := by
  rcases e with ⟨e, b, k⟩
  fin_cases e; cases b <;> fin_cases k <;> rfl

theorem first_parallel_middle_edges :
    (2 : Fin 6) ≠ 3 ∧ firstSource 2 = firstSource 3 ∧ firstTarget 2 = firstTarget 3 := by
  decide

end LinearInputLaaksoFiniteGraph
