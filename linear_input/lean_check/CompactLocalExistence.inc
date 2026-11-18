import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Compactness.Compact

/-!
Compactness supplies a common actual local existence time for a C¹ vector
field.  No integral curve is assumed, and an empty compact set is permitted.
-/

noncomputable section
namespace LinearInputCompactLocalExistence

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

open Set Metric

/-- Uniform local existence at every point of a compact set, obtained by a
finite subcover of the actual nearby-initial-data Picard-Lindelöf neighborhoods. -/
theorem exists_uniform_local_time {F : V → V} {K : Set V}
    (hF : ContDiff ℝ 1 F) (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∃ z : ℝ → V,
      z 0 = x ∧ ∀ t ∈ Ioo (-ε) ε, HasDerivAt z (F (z t)) t := by
  classical
  have hlocal (x : V) :=
    (hF.contDiffAt (x := x)).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  choose r hr d hd hz using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x => ball x (r x))
    (fun _ => isOpen_ball) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, mem_ball_self (hr x)⟩)
  have hsmall : ∀ a : Finset V, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ a, ε ≤ d x := by
    intro a
    induction a using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert x a hxa ih =>
      obtain ⟨ε, hε, he⟩ := ih
      refine ⟨min (d x) ε, lt_min (hd x) hε, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with hxy | hya
      · subst y
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (he y hya)
  obtain ⟨ε, hε, he⟩ := hsmall s
  refine ⟨ε, hε, ?_⟩
  intro x hx
  obtain ⟨y, hys, hxy⟩ := mem_iUnion₂.mp (hs hx)
  obtain ⟨z, hz0, hzd⟩ := hz y x (ball_subset_closedBall hxy)
  refine ⟨z, hz0, ?_⟩
  intro t ht
  apply hzd t
  have hed := he y hys
  constructor <;> linarith [ht.1, ht.2]

end LinearInputCompactLocalExistence
