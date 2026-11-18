/-!+A metric geometry ingredient for a future signature-tree construction.
The standard four-point condition implies that every continuous loop has an
explicit root-distance tree height. No four-point metric on a signature range
and no general Hambly--Lyons conclusion is assumed or claimed here.
-/

noncomputable section
open Set
open LinearInputCurveWordTreeLike

namespace LinearInputCurveWordSignatureTree

open scoped NNReal

/-- The usual metric four-point condition for zero hyperbolicity. -/
def FourPoint {E : Type*} [PseudoMetricSpace E] : Prop :=
  ∀ a b c d : E, dist a c + dist b d ≤
    max (dist a b + dist c d) (dist a d + dist b c)

def rootProduct {E : Type*} [PseudoMetricSpace E] (o x y : E) : ℝ :=
  (dist o x + dist o y - dist x y) / 2

theorem rootProduct_self {E : Type*} [PseudoMetricSpace E] (o x : E) :
    rootProduct o x x = dist o x := by simp [rootProduct]

theorem rootProduct_symm {E : Type*} [PseudoMetricSpace E] (o x y : E) :
    rootProduct o x y = rootProduct o y x := by
  simp only [rootProduct, dist_comm x y]
  ring

theorem rootProduct_lower {E : Type*} [PseudoMetricSpace E] (o x y : E) :
    dist o x - dist x y ≤ rootProduct o x y := by
  have h := dist_triangle o y x
  rw [dist_comm y x] at h
  unfold rootProduct
  linarith

theorem rootProduct_min {E : Type*} [PseudoMetricSpace E] (h : @FourPoint E _)
    (o x y z : E) :
    min (rootProduct o x y) (rootProduct o y z) ≤ rootProduct o x z := by
  have hh := h o x y z
  unfold rootProduct
  by_cases hc : dist o x + dist y z ≤ dist o z + dist x y
  · rw [max_eq_right hc] at hh
    exact le_trans (min_le_left _ _) (by linarith)
  · rw [max_eq_left (le_of_not_ge hc)] at hh
    exact le_trans (min_le_right _ _) (by linarith)

/-- Above any root-height threshold, membership in one branch is locally
constant. The proof uses the four-point condition and actual metric balls. -/
theorem branch_locallyConstant {E : Type*} [PseudoMetricSpace E]
    (h : @FourPoint E _) (o x : E) (c : ℝ) :
    IsLocallyConstant (fun z : {z : E // c < dist o z} =>
      decide (c < rootProduct o x z)) := by
  classical
  apply (IsLocallyConstant.iff_exists_open _).2
  intro y
  let ε := dist o (y : E) - c
  have hε : 0 < ε := sub_pos.mpr y.property
  refine ⟨Metric.ball y ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
  intro z hz
  have hdist : dist (y : E) (z : E) < ε := by
    simpa only [Metric.mem_ball, dist_comm] using! hz
  have hp : c < rootProduct o (y : E) (z : E) := by
    have hb := rootProduct_lower o (y : E) (z : E)
    dsimp [ε] at hdist
    linarith
  have he : (c < rootProduct o x (z : E)) ↔ (c < rootProduct o x (y : E)) := by
    constructor
    · intro hz'
      have ht := rootProduct_min h o x (z : E) (y : E)
      rw [rootProduct_symm o (z : E) (y : E)] at ht
      exact lt_of_lt_of_le (lt_min hz' hp) ht
    · intro hy'
      exact lt_of_lt_of_le (lt_min hy' hp) (rootProduct_min h o x (y : E) (z : E))
  simp only [decide_eq_decide]
  exact he

/-- Every continuous path in a four-point metric space passes at or below
the common-branch height of its endpoints. -/
theorem path_meets_branch_height {E : Type*} [PseudoMetricSpace E]
    (h : @FourPoint E _) (o : E) {γ : ℝ → E} {s t : ℝ}
    (hst : s ≤ t) (hγ : ContinuousOn γ (Icc s t)) :
    ∃ r ∈ Icc s t, dist o (γ r) ≤ rootProduct o (γ s) (γ t) := by
  classical
  let c := rootProduct o (γ s) (γ t)
  by_contra hn
  have habove : ∀ r ∈ Icc s t, c < dist o (γ r) := by
    intro r hr
    exact lt_of_not_ge (fun hle => hn ⟨r, hr, hle⟩)
  let τ : Icc s t → {z : E // c < dist o z} := fun r => ⟨γ r, habove r r.property⟩
  have hτ : Continuous τ := hγ.domRestrict.subtype_mk _
  have hbranch := (branch_locallyConstant h o (γ s) c).comp_continuous hτ
  let : PreconnectedSpace (Icc s t) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have he := hbranch.apply_eq_of_preconnectedSpace ⟨s, ⟨le_rfl, hst⟩⟩ ⟨t, ⟨hst, le_rfl⟩⟩
  have hs : c < dist o (γ s) := habove s ⟨le_rfl, hst⟩
  change decide (c < rootProduct o (γ s) (γ s)) = decide (c < rootProduct o (γ s) (γ t)) at he
  rw [rootProduct_self] at he
  simp only [hs, decide_true, c, lt_self_iff_false, decide_false] at he
  contradiction

/-- The root-distance height is derived from the metric four-point condition
and continuity, rather than assumed as an independent path inequality. -/
theorem loop_hasTreeHeight {E : Type*} [PseudoMetricSpace E]
    (h : @FourPoint E _) {γ : ℝ → E} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) :
    HasTreeHeight γ a b (fun t => dist (γ a) (γ t)) := by
  refine ⟨continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγ), by simp, by simp [hclosed],
    (fun _ _ => dist_nonneg), ?_⟩
  intro s hs t ht
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  obtain ⟨r, hr, hb⟩ := path_meets_branch_height h (γ a) ht.1 (hγ.mono hsub)
  refine ⟨r, hr, ?_⟩
  unfold rootProduct at hb
  linarith

theorem loop_treeLike {E : Type*} [PseudoMetricSpace E]
    (h : @FourPoint E _) {γ : ℝ → E} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) : TreeLike γ a b :=
  ⟨hγ, _, loop_hasTreeHeight h hγ hclosed⟩

theorem lipschitz_factor_loop_treeLike {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (h : @FourPoint E _) {τ : ℝ → E} {a b : ℝ}
    (hτ : ContinuousOn τ (Icc a b)) (hclosed : τ a = τ b)
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    TreeLike (f ∘ τ) a b :=
  (loop_treeLike h hτ hclosed).lipschitz_map hf

end LinearInputCurveWordSignatureTree
