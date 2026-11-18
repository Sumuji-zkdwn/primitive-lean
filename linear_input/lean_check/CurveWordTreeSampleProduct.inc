/-!
The actual straight-segment signature products of the constructed height
samples are the unit series.  This connects finite height sampling and its
metric quotient to the polygonal integral signature, in every degree.
-/

noncomputable section

namespace LinearInputCurveWordTreeSampleProduct

open Set
open LinearInputCurveWordFormalSeries LinearInputCurveWordFriedrichs
open LinearInputCurveWordTreeLike LinearInputCurveWordHeightMetric
open LinearInputCurveWordTreeSignature LinearInputCurveWordTreeSampling
open LinearInputCurveWordPolygonal

theorem segmentProduct_eq_sequenceWeight {ι V : Type*}
    (f : V → ι → ℝ) (x : ℕ → V) (n : ℕ) :
    segmentProduct (fun j => f (x j)) n =
      sequenceWeight (M := TensorSeries ι) (fun u v => segmentSignature (f u) (f v)) x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [segmentProduct, sequenceWeight, ih]
    rfl

theorem interpolateProduct_graph_eq_one {ι V : Type*} {G : SimpleGraph V}
    (hG : G.IsAcyclic) (f : V → ι → ℝ) {N : ℕ} (x : Fin (N + 1) → V)
    (hedge : ∀i : Fin N, x i.castSucc = x i.succ ∨ G.Adj (x i.castSucc) (x i.succ))
    (hclosed : x (Fin.last N) = x 0) :
    interpolateProduct (fun j => f (x j)) = unitSeries := by
  let z : ℕ → V := fun j => x ⟨min j N, Nat.lt_succ_of_le (min_le_right j N)⟩
  have hz : ∀j < N, z j = z (j + 1) ∨ G.Adj (z j) (z (j + 1)) := by
    intro j hj
    simpa only [z, min_eq_left hj.le, min_eq_left (Nat.succ_le_of_lt hj)] using! hedge ⟨j, hj⟩
  have hc : z N = z 0 := by simpa only [z, min_self, zero_min] using! hclosed
  change segmentProduct (fun j => f (z j)) N = (1 : TensorSeries ι)
  rw [segmentProduct_eq_sequenceWeight]
  exact acyclic_closed_segment_sequence hG f z N hz hc

theorem interpolateProduct_of_height_steps {ι : Type*} [Fintype ι]
    {γ : ℝ → (ι → ℝ)} {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hh : HasTreeHeight γ a b h) {L : Finset ℝ} {N : ℕ}
    (t : Fin (N + 1) → ℝ) (ht : StrictMono t) (ha : t 0 = a)
    (hb : t (Fin.last N) = b)
    (hstep : ∀i : Fin N, HeightStep h L (t i.castSucc) (t i.succ)) :
    interpolateProduct (fun j => γ (t j)) = unitSeries := by
  have hmem (j : Fin (N + 1)) : t j ∈ Icc a b := by
    rw [← ha, ← hb]
    exact ⟨ht.monotone (Fin.zero_le j), ht.monotone (Fin.le_last j)⟩
  let x : Fin (N + 1) → HeightQuotient h a b hh.1 :=
    fun j => quotientTime hh.1 ⟨t j, hmem j⟩
  let o : HeightQuotient h a b hh.1 := quotientTime hh.1 ⟨a, left_mem_Icc.mpr hab⟩
  have hedge : ∀i : Fin N, x i.castSucc = x i.succ ∨
      (levelGraph o L).Adj (x i.castSucc) (x i.succ) := by
    intro i
    exact heightStep_quotient_edge hab hh.1 hh.2.1 hh.2.2.2.1
      ⟨t i.castSucc, hmem _⟩ ⟨t i.succ, hmem _⟩
      (ht.monotone (show i.castSucc ≤ i.succ from Nat.le_succ i.val)) (hstep i)
  have hx0 : x 0 = quotientTime hh.1 ⟨a, left_mem_Icc.mpr hab⟩ :=
    congrArg (quotientTime hh.1) (Subtype.ext ha)
  have hxN : x (Fin.last N) = quotientTime hh.1 ⟨b, right_mem_Icc.mpr hab⟩ :=
    congrArg (quotientTime hh.1) (Subtype.ext hb)
  have hclosed : x (Fin.last N) = x 0 := hxN.trans
    ((quotientTime_endpoints hab hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1).symm.trans hx0.symm)
  have he := interpolateProduct_graph_eq_one
    (levelGraph_acyclic (heightQuotient_fourPoint hh.1) o L) (factorCurve hh) x hedge hclosed
  exact he

/-- Every height-coded path admits arbitrarily fine time-ordered samples
whose actual straight-segment signature product is exactly the unit series.
No signature cancellation is assumed in the construction. -/
theorem exists_unit_signature_sampling {ι : Type*} [Fintype ι]
    {γ : ℝ → (ι → ℝ)} {h : ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b)
    (hh : HasTreeHeight γ a b h) (hδ : 0 < δ) :
    ∃(N : ℕ) (t : Fin (N + 1) → ℝ),
      StrictMono t ∧ t 0 = a ∧ t (Fin.last N) = b ∧
      (∀i : Fin N, t i.succ - t i.castSucc ≤ δ) ∧
      interpolateProduct (fun j => γ (t j)) = unitSeries := by
  obtain ⟨L, N, t, ht, ha, hb, he⟩ := exists_height_sampling hab hh.1 hδ
  exact ⟨N, t, ht, ha, hb, fun i => (he i).2,
    interpolateProduct_of_height_steps hab hh t ht ha hb (fun i => (he i).1)⟩

end LinearInputCurveWordTreeSampleProduct
