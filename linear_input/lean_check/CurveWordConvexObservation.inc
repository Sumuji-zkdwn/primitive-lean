/-!
Finite equal-cost observations depend only on the convex hull of endpoints.
The support is attained at an original endpoint; the assertions are about
actual convex hulls and finite minima, not a postulated duality principle.
-/

noncomputable section
namespace LinearInputCurveWordConvexObservation

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def finiteSupport (S : Finset E) (hS : S.Nonempty) (L : E →ₗ[ℝ] ℝ) : ℝ := S.sup' hS L

theorem support_bounds_hull (S : Finset E) (hS : S.Nonempty) (L : E →ₗ[ℝ] ℝ)
    {x : E} (hx : x ∈ convexHull ℝ (S : Set E)) : L x ≤ finiteSupport S hS L := by
  exact (L.convexOn convex_univ).le_sup_of_mem_convexHull (subset_univ _) hx

theorem support_attained (S : Finset E) (hS : S.Nonempty) (L : E →ₗ[ℝ] ℝ) :
    ∃ x ∈ S, L x = finiteSupport S hS L := by
  obtain ⟨x, hx, he⟩ := Finset.exists_mem_eq_sup' hS L
  exact ⟨x, hx, he.symm⟩

theorem finiteSupport_eq_of_convexHull_eq (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty)
    (hull : convexHull ℝ (S : Set E) = convexHull ℝ (T : Set E)) (L : E →ₗ[ℝ] ℝ) :
    finiteSupport S hS L = finiteSupport T hT L := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    apply support_bounds_hull T hT L
    rw [← hull]
    exact subset_convexHull ℝ (S : Set E) hx
  · apply Finset.sup'_le
    intro x hx
    apply support_bounds_hull S hS L
    rw [hull]
    exact subset_convexHull ℝ (T : Set E) hx

theorem equal_cost_minimum_eq_support (S : Finset E) (hS : S.Nonempty)
    (F : ℝ) (L : E →ₗ[ℝ] ℝ) :
    S.inf' hS (fun x => F - L x) = F - finiteSupport S hS L := by
  obtain ⟨x, hx, he⟩ := support_attained S hS L
  apply le_antisymm
  · rw [← he]
    exact Finset.inf'_le _ hx
  · apply Finset.le_inf'
    intro y hy
    exact sub_le_sub_left (Finset.le_sup' L hy) F

/-- The same attained minimum is valid over the entire convex hull. -/
theorem equal_cost_hull_minimum (S : Finset E) (hS : S.Nonempty) (F : ℝ) (L : E →ₗ[ℝ] ℝ) :
    ∃ x ∈ S, F - L x = F - finiteSupport S hS L ∧
      ∀ y ∈ convexHull ℝ (S : Set E), F - L x ≤ F - L y := by
  obtain ⟨x, hx, he⟩ := support_attained S hS L
  refine ⟨x, hx, by rw [he], ?_⟩
  intro y hy
  rw [he]
  exact sub_le_sub_left (support_bounds_hull S hS L hy) F

theorem equal_cost_observation_forgets_hull_interior
    (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty)
    (hull : convexHull ℝ (S : Set E) = convexHull ℝ (T : Set E))
    (F : ℝ) (L : E →ₗ[ℝ] ℝ) :
    S.inf' hS (fun x => F - L x) = T.inf' hT (fun x => F - L x) := by
  rw [equal_cost_minimum_eq_support, equal_cost_minimum_eq_support,
    finiteSupport_eq_of_convexHull_eq S T hS hT hull L]

end LinearInputCurveWordConvexObservation
