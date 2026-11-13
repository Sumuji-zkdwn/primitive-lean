/-!
Geometric realization of a labelled graph by closed real intervals.
Only interval endpoints are identified. The topology is the quotient topology
of the raw disjoint union, not the disjoint-union topology of normal forms.
This module makes no path-metric, dimension, or Poincare assertion.
-/

namespace LinearInputLaaksoRealization

open LinearInputLaaksoFiniteGraph

abbrev Raw (V E : Type) := V ⊕ (E × unitInterval)

noncomputable def normal {V E : Type} (G : Graph V E) : Raw V E → V ⊕ (E × ℝ) := by
  classical
  exact fun x => match x with
    | .inl v => .inl v
    | .inr (e, u) =>
        if (u : ℝ) = 0 then .inl (G.1 e)
        else if (u : ℝ) = 1 then .inl (G.2 e)
        else .inr (e, (u : ℝ))

noncomputable def endpointSetoid {V E : Type} (G : Graph V E) : Setoid (Raw V E) :=
  Setoid.ker (normal G)

abbrev Realization {V E : Type} (G : Graph V E) := Quotient (endpointSetoid G)

noncomputable def vertexPoint {V E : Type} (G : Graph V E) (v : V) : Realization G :=
  Quotient.mk (endpointSetoid G) (.inl v)

noncomputable def edgePoint {V E : Type} (G : Graph V E) (e : E) (u : unitInterval) :
    Realization G := Quotient.mk (endpointSetoid G) (.inr (e, u))

theorem realization_cases {V E : Type} (G : Graph V E) (x : Realization G) :
    (∃ v, x = vertexPoint G v) ∨ (∃ e u, x = edgePoint G e u) := by
  refine Quotient.inductionOn x ?_
  intro a
  rcases a with v | ⟨e, u⟩
  · exact Or.inl ⟨v, rfl⟩
  · exact Or.inr ⟨e, u, rfl⟩

theorem edgePoint_zero {V E : Type} (G : Graph V E) (e : E) :
    edgePoint G e 0 = vertexPoint G (G.1 e) := by
  apply Quotient.sound
  change normal G (.inr (e, 0)) = normal G (.inl (G.1 e))
  simp [normal]

theorem edgePoint_one {V E : Type} (G : Graph V E) (e : E) :
    edgePoint G e 1 = vertexPoint G (G.2 e) := by
  apply Quotient.sound
  change normal G (.inr (e, 1)) = normal G (.inl (G.2 e))
  simp [normal]

theorem vertexPoint_injective {V E : Type} (G : Graph V E) :
    Function.Injective (vertexPoint G) := by
  intro v w h
  have hn : normal G (.inl v) = normal G (.inl w) := Quotient.exact h
  simpa [normal] using hn

theorem edgePoint_interior_eq_iff {V E : Type} (G : Graph V E)
    (e f : E) (u v : unitInterval)
    (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
    (hv0 : 0 < (v : ℝ)) (hv1 : (v : ℝ) < 1) :
    edgePoint G e u = edgePoint G f v ↔ e = f ∧ u = v := by
  constructor
  · intro h
    have hn : normal G (.inr (e, u)) = normal G (.inr (f, v)) := Quotient.exact h
    have hp : e = f ∧ (u : ℝ) = (v : ℝ) := by
      simpa [normal, ne_of_gt hu0, ne_of_lt hu1, ne_of_gt hv0, ne_of_lt hv1] using hn
    exact ⟨hp.1, Subtype.ext hp.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem edgePoint_interior_ne_vertex {V E : Type} (G : Graph V E)
    (e : E) (u : unitInterval) (v : V)
    (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1) :
    edgePoint G e u ≠ vertexPoint G v := by
  intro h
  have hn : normal G (.inr (e, u)) = normal G (.inl v) := Quotient.exact h
  simp [normal, ne_of_gt hu0, ne_of_lt hu1] at hn

def rawLift {V E Y : Type} (fV : V → Y) (fE : E → unitInterval → Y) : Raw V E → Y :=
  Sum.elim fV (fun p => fE p.1 p.2)

/-- An extension used only to factor through endpoint-normal forms. -/
noncomputable def normalValue {V E Y : Type}
    (fV : V → Y) (fE : E → unitInterval → Y) : V ⊕ (E × ℝ) → Y :=
  Sum.elim fV (fun p => fE p.1 (Set.projIcc 0 1 zero_le_one p.2))

theorem normalValue_normal {V E Y : Type} (G : Graph V E)
    (fV : V → Y) (fE : E → unitInterval → Y)
    (h0 : ∀ e, fE e 0 = fV (G.1 e)) (h1 : ∀ e, fE e 1 = fV (G.2 e))
    (x : Raw V E) : normalValue fV fE (normal G x) = rawLift fV fE x := by
  rcases x with v | ⟨e, u⟩
  · rfl
  · by_cases hu0 : (u : ℝ) = 0
    · have hu : u = 0 := Subtype.ext hu0
      subst u
      simpa [normal, normalValue, rawLift] using (h0 e).symm
    · by_cases hu1 : (u : ℝ) = 1
      · have hu : u = 1 := Subtype.ext hu1
        subst u
        simpa [normal, normalValue, rawLift] using (h1 e).symm
      · simp [normal, hu0, hu1, normalValue, rawLift, Set.projIcc_of_mem zero_le_one u.property]

theorem rawLift_respects {V E Y : Type} (G : Graph V E)
    (fV : V → Y) (fE : E → unitInterval → Y)
    (h0 : ∀ e, fE e 0 = fV (G.1 e)) (h1 : ∀ e, fE e 1 = fV (G.2 e))
    (x y : Raw V E) (h : endpointSetoid G x y) : rawLift fV fE x = rawLift fV fE y := by
  change normal G x = normal G y at h
  rw [← normalValue_normal G fV fE h0 h1 x, ← normalValue_normal G fV fE h0 h1 y]
  exact congrArg (normalValue fV fE) h

noncomputable def lift {V E Y : Type} (G : Graph V E)
    (fV : V → Y) (fE : E → unitInterval → Y)
    (h0 : ∀ e, fE e 0 = fV (G.1 e)) (h1 : ∀ e, fE e 1 = fV (G.2 e)) :
    Realization G → Y :=
  Quotient.lift (rawLift fV fE) (rawLift_respects G fV fE h0 h1)

theorem lift_vertex {V E Y : Type} (G : Graph V E)
    (fV : V → Y) (fE : E → unitInterval → Y)
    (h0 : ∀ e, fE e 0 = fV (G.1 e)) (h1 : ∀ e, fE e 1 = fV (G.2 e)) (v : V) :
    lift G fV fE h0 h1 (vertexPoint G v) = fV v := rfl

theorem lift_edge {V E Y : Type} (G : Graph V E)
    (fV : V → Y) (fE : E → unitInterval → Y)
    (h0 : ∀ e, fE e 0 = fV (G.1 e)) (h1 : ∀ e, fE e 1 = fV (G.2 e))
    (e : E) (u : unitInterval) : lift G fV fE h0 h1 (edgePoint G e u) = fE e u := rfl

theorem lift_unique {V E Y : Type} (G : Graph V E)
    (fV : V → Y) (fE : E → unitInterval → Y)
    (h0 : ∀ e, fE e 0 = fV (G.1 e)) (h1 : ∀ e, fE e 1 = fV (G.2 e))
    (f : Realization G → Y) (hv : ∀ v, f (vertexPoint G v) = fV v)
    (he : ∀ e u, f (edgePoint G e u) = fE e u) : f = lift G fV fE h0 h1 := by
  funext x
  refine Quotient.inductionOn x ?_
  intro a
  rcases a with v | ⟨e, u⟩
  · exact hv v
  · exact he e u

theorem continuous_vertexPoint {V E : Type} [TopologicalSpace V] [TopologicalSpace E]
    (G : Graph V E) : Continuous (vertexPoint G) :=
  continuous_quotient_mk'.comp continuous_inl

theorem continuous_edgePoint {V E : Type} [TopologicalSpace V] [TopologicalSpace E]
    (G : Graph V E) (e : E) : Continuous (edgePoint G e) :=
  continuous_quotient_mk'.comp (continuous_inr.comp (continuous_const.prodMk continuous_id))

theorem continuous_edgePoints {V E : Type} [TopologicalSpace V] [TopologicalSpace E]
    (G : Graph V E) : Continuous (fun p : E × unitInterval => edgePoint G p.1 p.2) :=
  continuous_quotient_mk'.comp continuous_inr

theorem continuous_lift {V E Y : Type}
    [TopologicalSpace V] [TopologicalSpace E] [TopologicalSpace Y]
    (G : Graph V E) (fV : V → Y) (fE : E → unitInterval → Y)
    (h0 : ∀ e, fE e 0 = fV (G.1 e)) (h1 : ∀ e, fE e 1 = fV (G.2 e))
    (hv : Continuous fV) (he : Continuous (fun p : E × unitInterval => fE p.1 p.2)) :
    Continuous (lift G fV fE h0 h1) := by
  have hr : Continuous (rawLift fV fE) := continuous_sum_dom.mpr ⟨hv, he⟩
  exact hr.quotient_lift (rawLift_respects G fV fE h0 h1)

theorem compact_realization {V E : Type} [TopologicalSpace V] [TopologicalSpace E]
    [Finite V] [Finite E] (G : Graph V E) : CompactSpace (Realization G) := by
  infer_instance

end LinearInputLaaksoRealization
