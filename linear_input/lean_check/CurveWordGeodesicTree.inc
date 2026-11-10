/-!
The metric bridge from actual geodesics with zero-thin triangles to the
standard four-point condition. Unique geodesics alone are not sufficient;
the explicit triangle-cover hypothesis is retained for the geometric caller.
-/

noncomputable section

namespace LinearInputCurveWordGeodesicTree

open LinearInputCurveWordSignatureTree

variable {E : Type*} [MetricSpace E]

structure GeodesicSystem (E : Type*) [MetricSpace E] where
  path : ∀ x y : E, Set.Icc (0 : ℝ) (dist x y) → E
  isometry : ∀ x y, Isometry (path x y)
  source : ∀ x y, path x y ⟨0, le_rfl, dist_nonneg⟩ = x
  target : ∀ x y, path x y ⟨dist x y, dist_nonneg, le_rfl⟩ = y

def segment (G : GeodesicSystem E) (x y : E) : Set E := Set.range (G.path x y)

def ThinTriangles (G : GeodesicSystem E) : Prop :=
  ∀ x y z : E, segment G x y ⊆ segment G x z ∪ segment G z y

theorem path_dist_source (G : GeodesicSystem E) (x y : E)
    (t : Set.Icc (0 : ℝ) (dist x y)) : dist x (G.path x y t) = t.val := by
  conv_lhs => arg 1; rw [← G.source x y]
  rw [(G.isometry x y).dist_eq]
  simp only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg t.property.1]

theorem path_dist_target (G : GeodesicSystem E) (x y : E)
    (t : Set.Icc (0 : ℝ) (dist x y)) : dist (G.path x y t) y = dist x y - t.val := by
  conv_lhs => arg 2; rw [← G.target x y]
  rw [(G.isometry x y).dist_eq]
  simp only [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr t.property.2), neg_sub]

theorem dist_add_of_mem_segment (G : GeodesicSystem E) {x y p : E}
    (hp : p ∈ segment G x y) : dist x p + dist p y = dist x y := by
  obtain ⟨t, rfl⟩ := hp
  rw [path_dist_source, path_dist_target]
  ring

theorem rootProduct_nonnegative (o x y : E) : 0 ≤ rootProduct o x y := by
  have ht := dist_triangle x o y
  rw [dist_comm x o] at ht
  unfold rootProduct
  linarith

theorem rootProduct_le_right (o x y : E) : rootProduct o x y ≤ dist o y := by
  have ht := dist_triangle o y x
  rw [dist_comm y x] at ht
  unfold rootProduct
  linarith

/-- Before the Gromov-product threshold, a point of the root-to-y geodesic
must also lie on the root-to-x geodesic. Membership on the opposite side of
the thin triangle would contradict the metric triangle inequality. -/
theorem initial_point_mem (G : GeodesicSystem E) (hthin : ThinTriangles G)
    (o x y : E) (r : Set.Icc (0 : ℝ) (dist o y))
    (hr : r.val < rootProduct o x y) : G.path o y r ∈ segment G o x := by
  have hp : G.path o y r ∈ segment G o y := ⟨r, rfl⟩
  rcases hthin o y x hp with hx | hxy
  · exact hx
  · have hside := dist_add_of_mem_segment G hxy
    have hroot := dist_add_of_mem_segment G hp
    have htriangle := dist_triangle o (G.path o y r) x
    rw [path_dist_source] at hroot htriangle
    rw [dist_comm (G.path o y r) x] at htriangle
    unfold rootProduct at hr
    linarith

theorem thin_rootProduct_min (G : GeodesicSystem E) (hthin : ThinTriangles G)
    (o x y z : E) : min (rootProduct o x y) (rootProduct o y z) ≤ rootProduct o x z := by
  by_contra hnot
  have hlt : rootProduct o x z < min (rootProduct o x y) (rootProduct o y z) := lt_of_not_ge hnot
  let r : ℝ := (rootProduct o x z + min (rootProduct o x y) (rootProduct o y z)) / 2
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [rootProduct_nonnegative o x z]
  have hrlo : rootProduct o x z < r := by dsimp [r]; linarith
  have hrhi : r < min (rootProduct o x y) (rootProduct o y z) := by dsimp [r]; linarith
  have hry : r ≤ dist o y := (hrhi.le.trans (min_le_left _ _)).trans (rootProduct_le_right o x y)
  let t : Set.Icc (0 : ℝ) (dist o y) := ⟨r, hr0, hry⟩
  have hx := initial_point_mem G hthin o x y t (hrhi.trans_le (min_le_left _ _))
  have hz := initial_point_mem G hthin o z y t (by
    rw [rootProduct_symm o z y]
    exact hrhi.trans_le (min_le_right _ _))
  have hdx := dist_add_of_mem_segment G hx
  have hdz := dist_add_of_mem_segment G hz
  rw [path_dist_source] at hdx hdz
  have ht := dist_triangle x (G.path o y t) z
  rw [dist_comm x (G.path o y t)] at ht
  unfold rootProduct at hrlo
  change r + dist (G.path o y t) x = dist o x at hdx
  change r + dist (G.path o y t) z = dist o z at hdz
  linarith

theorem fourPoint_of_rootProduct_min
    (h : ∀ o x y z : E, min (rootProduct o x y) (rootProduct o y z) ≤ rootProduct o x z) :
    @FourPoint E _ := by
  intro a b c d
  have hh := h a b c d
  unfold rootProduct at hh
  by_cases hc : dist a b + dist c d ≤ dist a d + dist b c
  · rw [min_eq_left (by linarith)] at hh
    rw [max_eq_right hc]
    linarith
  · rw [min_eq_right (by linarith)] at hh
    rw [max_eq_left (le_of_not_ge hc)]
    linarith

theorem fourPoint_of_thin_geodesics (G : GeodesicSystem E) (hthin : ThinTriangles G) :
    @FourPoint E _ := fourPoint_of_rootProduct_min (thin_rootProduct_min G hthin)

end LinearInputCurveWordGeodesicTree
