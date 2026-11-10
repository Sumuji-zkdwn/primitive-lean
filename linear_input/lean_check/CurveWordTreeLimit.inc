/-!
Limit transport from genuine finite chronological samplings to the canonical
signature of a continuous BV path. The final height theorem instantiates the
sampling premise with the independently constructed height-level samples.
-/

noncomputable section

namespace LinearInputCurveWordTreeLimit

open Real Set MeasureTheory Filter
open scoped Topology
open LinearInputCurveWordBoundedVariation LinearInputCurveWordBVCanonical
open LinearInputCurveWordSignatureUniform LinearInputCurveWordPolygonal LinearInputCurveWordFormalSeries

def extendedCoordinates {ι : Type*} (γ : ℝ → ι → ℝ) (a b : ℝ) (i : ι) (t : ℝ) : ℝ :=
  γ (clamp a b t) i

theorem extendedCoordinates_boundedVariation {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b) (hγ : BoundedVariationOn γ (Icc a b)) (i : ι) :
    BoundedVariationOn (extendedCoordinates γ a b i) univ :=
  constantExtension_boundedVariation hab (coordinate_boundedVariation hγ i)

theorem extendedCoordinates_continuous {ι : Type*}
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn γ (Icc a b)) (i : ι) :
    Continuous (extendedCoordinates γ a b i) :=
  constantExtension_continuous hab (coordinate_continuousOn hc i)

theorem extendedCoordinates_eq {ι : Type*} (γ : ℝ → ι → ℝ) {a b t : ℝ}
    (ht : t ∈ Icc a b) (i : ι) : extendedCoordinates γ a b i t = γ t i := by
  rw [extendedCoordinates, clamp_eq ht]

/-- The compact-interval path API equals the global Jordan-pair API of its
constant endpoint extension; all changes outside the interval are explicit. -/
theorem pathSignature_eq_extension {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b)) :
    pathSignature γ hab hγ hc = bvSignature (extendedCoordinates γ a b)
      (extendedCoordinates_boundedVariation γ hab hγ) (extendedCoordinates_continuous γ hab hc) a b := by
  rw [← curveSignature_eq_bvSignature _ _ _ hab]
  funext w
  apply curveSignature_congr hab
  intro i t ht
  exact (extendedCoordinates_eq γ ht i).symm

/-- This transport lemma has an explicit sampling premise. The final theorem
below obtains that premise from the actual height-level construction. -/
theorem pathSignature_eq_unit_of_fine_samples {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hsample : ∀ δ > 0, ∃ (N : ℕ) (T : Fin (N + 1) → ℝ),
      StrictMono T ∧ T 0 = a ∧ T (Fin.last N) = b ∧
      (∀ i : Fin N, T i.succ - T i.castSucc ≤ δ) ∧
      interpolateProduct (fun j => γ (T j)) = unitSeries) :
    pathSignature γ hab hγ hc = unitSeries := by
  have hex : ∀ n : ℕ, ∃ (N : ℕ) (T : Fin (N + 1) → ℝ),
      StrictMono T ∧ T 0 = a ∧ T (Fin.last N) = b ∧
      (∀ i : Fin N, T i.succ - T i.castSucc ≤ (1 : ℝ) / (n + 1)) ∧
      interpolateProduct (fun j => γ (T j)) = unitSeries :=
    fun n => hsample _ (by positivity)
  choose N T hT ha hb hgap hprod using hex
  have hmesh : ∀ δ > 0, ∀ᶠ k in atTop, ∀ i : Fin (N k), T k i.succ - T k i.castSucc < δ := by
    intro δ hδ
    have hz : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hz.eventually (gt_mem_nhds hδ)] with k hk
    intro i
    exact (hgap k i).trans_lt hk
  let F := extendedCoordinates γ a b
  have hF := extendedCoordinates_boundedVariation γ hab hγ
  have hFc := extendedCoordinates_continuous γ hab hc
  have hlim := interpolateProduct_tendsto_of_mesh N T hT F hF hFc a b hab ha hb hmesh
  have he (k : ℕ) : interpolateProduct (fun j i => F i (T k j)) = unitSeries := by
    have hx : (fun j i => F i (T k j)) = (fun j => γ (T k j)) := by
      funext j i
      apply extendedCoordinates_eq
      rw [← ha k, ← hb k]
      exact ⟨(hT k).monotone (Fin.zero_le j), (hT k).monotone (Fin.le_last j)⟩
    rw [hx]
    exact hprod k
  simp only [he] at hlim
  rw [pathSignature_eq_extension γ hab hγ hc]
  exact tendsto_nhds_unique hlim tendsto_const_nhds

open LinearInputCurveWordTreeLike LinearInputCurveWordHeightMetric LinearInputCurveWordTreeSampleProduct

/-- The tree-like-to-trivial-signature direction for arbitrary finite-dimensional
continuous BV paths on a compact interval. The height predicate is independent
of signatures. Finite sampling existence and exact cancellation are applied,
not assumed, and the degenerate interval is included by `a ≤ b`. -/
theorem pathSignature_eq_unit_of_tree_height {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hc : ContinuousOn γ (Icc a b))
    (hh : HasTreeHeight γ a b h) : pathSignature γ hab hγ hc = unitSeries :=
  pathSignature_eq_unit_of_fine_samples γ hab hγ hc
    (fun _ hδ => exists_unit_signature_sampling hab hh hδ)

/-- A continuous height witness already forces continuity of the path. -/
theorem pathSignature_eq_unit_of_height {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hh : HasTreeHeight γ a b h) :
    pathSignature γ hab hγ (height_implies_curve_continuous hh) = unitSeries :=
  pathSignature_eq_unit_of_tree_height γ hab hγ _ hh

theorem treeLike_pathSignature_eq_unit {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hγ : BoundedVariationOn γ (Icc a b)) (htree : TreeLike γ a b) :
    pathSignature γ hab hγ htree.1 = unitSeries := by
  obtain ⟨h, hh⟩ := htree.2
  exact pathSignature_eq_unit_of_tree_height γ hab hγ htree.1 hh

end LinearInputCurveWordTreeLimit
