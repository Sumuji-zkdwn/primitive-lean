/-!
Continuous bonding maps for the endpoint-glued geometric realizations.
The map divides each parent edge parameter into thirds and forgets the sheet.
The parameter identities below are not assertions about a graph metric.
-/

namespace LinearInputLaaksoGeometricProjection

open LinearInputLaaksoFiniteGraph LinearInputLaaksoRealization

noncomputable def thirdParam (k : Fin 3) (u : unitInterval) : unitInterval :=
  ⟨((k.val : ℝ) + (u : ℝ)) / 3, by
    constructor
    · exact div_nonneg (add_nonneg (Nat.cast_nonneg k.val) u.property.1) (by norm_num)
    · have hk : (k.val : ℝ) ≤ 2 := by exact_mod_cast (show k.val ≤ 2 by omega)
      have hu := u.property.2
      linarith⟩

noncomputable def newParam (k : Fin 2) : unitInterval :=
  ⟨((k.val : ℝ) + 1) / 3, by
    constructor
    · positivity
    · have hk : (k.val : ℝ) ≤ 1 := by exact_mod_cast (show k.val ≤ 1 by omega)
      linarith⟩

theorem thirdParam_zero_zero : thirdParam 0 0 = 0 := by
  apply Subtype.ext
  norm_num [thirdParam]

theorem thirdParam_one_zero : thirdParam 1 0 = newParam 0 := by
  apply Subtype.ext
  norm_num [thirdParam, newParam]

theorem thirdParam_two_zero : thirdParam 2 0 = newParam 1 := by
  apply Subtype.ext
  norm_num [thirdParam, newParam]

theorem thirdParam_zero_one : thirdParam 0 1 = newParam 0 := by
  apply Subtype.ext
  norm_num [thirdParam, newParam]

theorem thirdParam_one_one : thirdParam 1 1 = newParam 1 := by
  apply Subtype.ext
  norm_num [thirdParam, newParam]

theorem thirdParam_two_one : thirdParam 2 1 = 1 := by
  apply Subtype.ext
  norm_num [thirdParam]

theorem continuous_thirdParam (k : Fin 3) : Continuous (thirdParam k) := by
  apply Continuous.subtype_mk
  exact (continuous_const.add continuous_subtype_val).div_const 3

theorem thirdParam_cover (u : unitInterval) :
    ∃ (k : Fin 3) (t : unitInterval), thirdParam k t = u := by
  by_cases h0 : (u : ℝ) ≤ 1 / 3
  · let t : unitInterval := ⟨3 * (u : ℝ), by
      constructor <;> nlinarith [u.property.1, u.property.2]⟩
    refine ⟨0, t, ?_⟩
    apply Subtype.ext
    simp only [thirdParam, t]
    norm_num
  · by_cases h1 : (u : ℝ) ≤ 2 / 3
    · let t : unitInterval := ⟨3 * (u : ℝ) - 1, by
        constructor <;> nlinarith [u.property.1, u.property.2]⟩
      refine ⟨1, t, ?_⟩
      apply Subtype.ext
      simp only [thirdParam, t]
      norm_num
    · let t : unitInterval := ⟨3 * (u : ℝ) - 2, by
        constructor <;> nlinarith [u.property.1, u.property.2]⟩
      refine ⟨2, t, ?_⟩
      apply Subtype.ext
      simp only [thirdParam, t]
      norm_num

noncomputable def vertexImage {V E : Type} (G : Graph V E) :
    RefinedVertex V E → Realization G
  | .inl (v, _) => vertexPoint G v
  | .inr (e, k) => edgePoint G e (newParam k)

noncomputable def edgeImage {V E : Type} (G : Graph V E)
    (a : RefinedEdge E) (u : unitInterval) : Realization G :=
  edgePoint G a.1 (thirdParam a.2.2 u)

theorem edgeImage_zero {V E : Type} (G : Graph V E) (a : RefinedEdge E) :
    edgeImage G a 0 = vertexImage G ((refine G).1 a) := by
  rcases a with ⟨e, b, k⟩
  fin_cases k <;>
    simp [edgeImage, vertexImage, refine, refineSource, thirdParam_zero_zero,
      thirdParam_one_zero, thirdParam_two_zero, edgePoint_zero]

theorem edgeImage_one {V E : Type} (G : Graph V E) (a : RefinedEdge E) :
    edgeImage G a 1 = vertexImage G ((refine G).2 a) := by
  rcases a with ⟨e, b, k⟩
  fin_cases k <;>
    simp [edgeImage, vertexImage, refine, refineTarget, thirdParam_zero_one,
      thirdParam_one_one, thirdParam_two_one, edgePoint_one]

noncomputable def bond {V E : Type} (G : Graph V E) :
    Realization (refine G) → Realization G :=
  lift (refine G) (vertexImage G) (edgeImage G) (edgeImage_zero G) (edgeImage_one G)

theorem bond_vertexPoint_old {V E : Type} (G : Graph V E) (v : V) (b : Bool) :
    bond G (vertexPoint (refine G) (.inl (v, b))) = vertexPoint G v := by
  simp [bond, lift_vertex, vertexImage]

theorem bond_vertexPoint_new {V E : Type} (G : Graph V E) (e : E) (k : Fin 2) :
    bond G (vertexPoint (refine G) (.inr (e, k))) = edgePoint G e (newParam k) := by
  simp [bond, lift_vertex, vertexImage]

theorem bond_edgePoint {V E : Type} (G : Graph V E) (e : E)
    (b : Bool) (k : Fin 3) (u : unitInterval) :
    bond G (edgePoint (refine G) (e, b, k) u) = edgePoint G e (thirdParam k u) := by
  simp [bond, lift_edge, edgeImage]

theorem continuous_bond {V E : Type} [TopologicalSpace V] [DiscreteTopology V]
    [TopologicalSpace E] [DiscreteTopology E] (G : Graph V E) :
    Continuous (bond G) := by
  apply continuous_lift
  · exact continuous_of_discreteTopology
  · apply continuous_prod_of_discrete_left.mpr
    intro a
    exact (continuous_edgePoint G a.1).comp (continuous_thirdParam a.2.2)

theorem bond_surjective {V E : Type} (G : Graph V E) :
    Function.Surjective (bond G) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro a
  rcases a with v | ⟨e, u⟩
  · exact ⟨vertexPoint (refine G) (.inl (v, false)), bond_vertexPoint_old G v false⟩
  · obtain ⟨k, t, h⟩ := thirdParam_cover u
    refine ⟨edgePoint (refine G) (e, false, k) t, ?_⟩
    rw [bond_edgePoint, h]
    rfl

/-- The sheet is forgotten on interior edge parameters as well as at vertices. -/
theorem bond_forgets_sheet {V E : Type} (G : Graph V E) (e : E)
    (b c : Bool) (k : Fin 3) (u : unitInterval) :
    bond G (edgePoint (refine G) (e, b, k) u) =
      bond G (edgePoint (refine G) (e, c, k) u) := by
  rw [bond_edgePoint, bond_edgePoint]

/-- Two distinct interior points on the two sheets have the same image. -/
theorem bond_not_injective {V E : Type} (G : Graph V E) (e : E) :
    ¬Function.Injective (bond G) := by
  let u : unitInterval := ⟨1 / 2, by norm_num⟩
  have hu0 : 0 < (u : ℝ) := by norm_num [u]
  have hu1 : (u : ℝ) < 1 := by norm_num [u]
  intro h
  have he := (edgePoint_interior_eq_iff (refine G) (e, false, 1) (e, true, 1)
    u u hu0 hu1 hu0 hu1).mp (h (bond_forgets_sheet G e false true 1 u))
  have hb : false = true := congrArg (fun a : RefinedEdge E => a.2.1) he.1
  cases hb

/-- Affine edge coordinates shrink by one third; no metric is asserted. -/
theorem thirdParam_difference (k : Fin 3) (u v : unitInterval) :
    (thirdParam k u : ℝ) - (thirdParam k v : ℝ) = ((u : ℝ) - (v : ℝ)) / 3 := by
  simp only [thirdParam]
  ring

end LinearInputLaaksoGeometricProjection
