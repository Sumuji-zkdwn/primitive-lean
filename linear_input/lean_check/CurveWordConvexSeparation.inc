/-!
Continuous linear observations determine the convex hull of a finite endpoint
set. The reverse implication uses actual strict Hahn--Banach separation from
the compact convex hull, rather than assuming observability as an axiom.
-/

noncomputable section

namespace LinearInputCurveWordConvexSeparation

open Set LinearInputCurveWordConvexObservation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_convexHull_iff_support (S : Finset E) (hS : S.Nonempty) (x : E) :
    x ∈ convexHull ℝ (S : Set E) ↔
      ∀ L : E →L[ℝ] ℝ, L x ≤ finiteSupport S hS L.toLinearMap := by
  constructor
  · intro hx L
    exact support_bounds_hull S hS L.toLinearMap hx
  · intro hx
    by_contra hnot
    obtain ⟨L, u, hu, hxL⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (S : Set E)) (S.finite_toSet.isClosed_convexHull ℝ) hnot
    obtain ⟨y, hy, he⟩ := support_attained S hS L.toLinearMap
    have hyL := hu y (subset_convexHull ℝ (S : Set E) hy)
    have hxy := hx L
    change L y = finiteSupport S hS L.toLinearMap at he
    linarith

theorem convexHull_eq_iff_support_eq (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) :
    convexHull ℝ (S : Set E) = convexHull ℝ (T : Set E) ↔
      ∀ L : E →L[ℝ] ℝ, finiteSupport S hS L.toLinearMap = finiteSupport T hT L.toLinearMap := by
  constructor
  · intro h L
    exact finiteSupport_eq_of_convexHull_eq S T hS hT h L.toLinearMap
  · intro h
    ext x
    simp only [mem_convexHull_iff_support S hS, mem_convexHull_iff_support T hT]
    constructor <;> intro hx L
    · rw [← h L]
      exact hx L
    · rw [h L]
      exact hx L

/-- Equal-cost observations for every continuous linear input lose precisely
the interior presentation of the convex hull of the finite endpoint set. -/
theorem convexHull_eq_iff_equal_cost_observations
    (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) (F : ℝ) :
    convexHull ℝ (S : Set E) = convexHull ℝ (T : Set E) ↔
      ∀ L : E →L[ℝ] ℝ,
        S.inf' hS (fun x => F - L x) = T.inf' hT (fun x => F - L x) := by
  rw [convexHull_eq_iff_support_eq S T hS hT]
  constructor <;> intro h L
  · exact equal_cost_observation_forgets_hull_interior S T hS hT
      ((convexHull_eq_iff_support_eq S T hS hT).mpr h) F L.toLinearMap
  · have he := h L
    change S.inf' hS (fun x => F - L.toLinearMap x) =
      T.inf' hT (fun x => F - L.toLinearMap x) at he
    rw [equal_cost_minimum_eq_support, equal_cost_minimum_eq_support] at he
    linarith

end LinearInputCurveWordConvexSeparation
