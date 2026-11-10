/-!
Finite ordered sampling and gluing. These purely order-theoretic lemmas join
local height-controlled samples without changing their consecutive-step law.
-/

noncomputable section

namespace LinearInputCurveWordSamplingOrder

def Consecutive (S : Finset ℝ) (x y : ℝ) : Prop :=
  x ∈ S ∧ y ∈ S ∧ x < y ∧ ∀ z ∈ S, x < z → y ≤ z

def GoodSampling (R : ℝ → ℝ → Prop) (a b : ℝ) (S : Finset ℝ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ (∀ x ∈ S, x ∈ Set.Icc a b) ∧
    ∀ x y, Consecutive S x y → R x y

theorem consecutive_subset {S T : Finset ℝ} (hST : S ⊆ T) {x y : ℝ}
    (hxy : Consecutive T x y) (hx : x ∈ S) (hy : y ∈ S) : Consecutive S x y :=
  ⟨hx, hy, hxy.2.2.1, fun z hz => hxy.2.2.2 z (hST hz)⟩

theorem goodSampling_singleton (R : ℝ → ℝ → Prop) (a : ℝ) :
    GoodSampling R a a {a} := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact ⟨le_rfl, le_rfl⟩
  · intro x y hxy
    have hx : x = a := Finset.mem_singleton.mp hxy.1
    have hy : y = a := Finset.mem_singleton.mp hxy.2.1
    exact False.elim ((ne_of_lt hxy.2.2.1) (hx.trans hy.symm))

theorem goodSampling_union {R : ℝ → ℝ → Prop} {a b c : ℝ} {S T : Finset ℝ}
    (hS : GoodSampling R a b S) (hT : GoodSampling R b c T) :
    GoodSampling R a c (S ∪ T) := by
  have hab : a ≤ b := (hS.2.2.1 b hS.2.1).1
  have hbc : b ≤ c := (hT.2.2.1 b hT.1).2
  have left_mem {x : ℝ} (hx : x ∈ S ∪ T) (hxb : x ≤ b) : x ∈ S := by
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hx
    · have he : x = b := le_antisymm hxb (hT.2.2.1 x hx).1
      exact he ▸ hS.2.1
  have right_mem {x : ℝ} (hx : x ∈ S ∪ T) (hbx : b ≤ x) : x ∈ T := by
    rcases Finset.mem_union.mp hx with hx | hx
    · have he : x = b := le_antisymm (hS.2.2.1 x hx).2 hbx
      exact he ▸ hT.1
    · exact hx
  refine ⟨Finset.mem_union_left T hS.1, Finset.mem_union_right S hT.2.1, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ⟨(hS.2.2.1 x hx).1, (hS.2.2.1 x hx).2.trans hbc⟩
    · exact ⟨hab.trans (hT.2.2.1 x hx).1, (hT.2.2.1 x hx).2⟩
  · intro x y hxy
    by_cases hyb : y ≤ b
    · exact hS.2.2.2 x y (consecutive_subset Finset.subset_union_left hxy
        (left_mem hxy.1 (hxy.2.2.1.le.trans hyb)) (left_mem hxy.2.1 hyb))
    · have hbx : b ≤ x := by
        by_contra hnot
        exact hyb (hxy.2.2.2 b (Finset.mem_union_left T hS.2.1) (lt_of_not_ge hnot))
      exact hT.2.2.2 x y (consecutive_subset Finset.subset_union_right hxy
        (right_mem hxy.1 hbx) (right_mem hxy.2.1 (hbx.trans hxy.2.2.1.le)))

theorem goodSampling_with_mesh {R : ℝ → ℝ → Prop} {a b δ : ℝ} {S : Finset ℝ}
    (hS : GoodSampling R a b S) (hwidth : b - a ≤ δ) :
    GoodSampling (fun x y => R x y ∧ y - x ≤ δ) a b S := by
  refine ⟨hS.1, hS.2.1, hS.2.2.1, ?_⟩
  intro x y hxy
  refine ⟨hS.2.2.2 x y hxy, ?_⟩
  have hx := hS.2.2.1 x hxy.1
  have hy := hS.2.2.1 y hxy.2.1
  linarith [hx.1, hy.2]

def chainSamples (t : ℕ → ℝ) (S : ℕ → Finset ℝ) (N : ℕ) : Finset ℝ :=
  insert (t 0) ((Finset.range N).biUnion S)

theorem chainSamples_zero (t : ℕ → ℝ) (S : ℕ → Finset ℝ) :
    chainSamples t S 0 = {t 0} := by simp [chainSamples]

theorem chainSamples_succ (t : ℕ → ℝ) (S : ℕ → Finset ℝ) (N : ℕ) :
    chainSamples t S (N + 1) = chainSamples t S N ∪ S N := by
  simp [chainSamples, Finset.range_add_one, Finset.union_comm]

theorem goodSampling_chain {R : ℝ → ℝ → Prop} (t : ℕ → ℝ) (S : ℕ → Finset ℝ) (N : ℕ)
    (hS : ∀ i < N, GoodSampling R (t i) (t (i + 1)) (S i)) :
    GoodSampling R (t 0) (t N) (chainSamples t S N) := by
  induction N with
  | zero => simpa only [chainSamples_zero] using goodSampling_singleton R (t 0)
  | succ N ih =>
    rw [chainSamples_succ]
    exact goodSampling_union (ih (fun i hi => hS i (by omega))) (hS N (by omega))

theorem chainSamples_contains_grid {R : ℝ → ℝ → Prop} (t : ℕ → ℝ) (S : ℕ → Finset ℝ)
    (N : ℕ) (hS : ∀ i < N, GoodSampling R (t i) (t (i + 1)) (S i))
    {j : ℕ} (hj : j ≤ N) : t j ∈ chainSamples t S N := by
  cases j with
  | zero => exact Finset.mem_insert_self _ _
  | succ j =>
    apply Finset.mem_insert_of_mem
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega), (hS j (by omega)).2.1⟩

theorem ordered_consecutive (S : Finset ℝ) {N : ℕ} (hc : S.card = N + 1) (i : Fin N) :
    Consecutive S (S.orderEmbOfFin hc i.castSucc) (S.orderEmbOfFin hc i.succ) := by
  refine ⟨S.orderEmbOfFin_mem hc _, S.orderEmbOfFin_mem hc _,
    (S.orderEmbOfFin hc).strictMono (by exact_mod_cast Nat.lt_succ_self i.val), ?_⟩
  intro z hz hxz
  have hz' : z ∈ Set.range (S.orderEmbOfFin hc) := by
    rw [Finset.range_orderEmbOfFin]
    exact hz
  obtain ⟨j, rfl⟩ := hz'
  apply (S.orderEmbOfFin hc).monotone
  have hj : i.castSucc < j := (S.orderEmbOfFin hc).lt_iff_lt.mp hxz
  exact hj

/-- Increasing finite times with the exact sampled set, both endpoints, and
the original consecutive-step relation. Degenerate intervals use N = 0. -/
theorem goodSampling_enumeration {R : ℝ → ℝ → Prop} {a b : ℝ} {S : Finset ℝ}
    (hS : GoodSampling R a b S) :
    ∃ (N : ℕ) (t : Fin (N + 1) → ℝ), StrictMono t ∧ t 0 = a ∧ t (Fin.last N) = b ∧
      Set.range t = (S : Set ℝ) ∧ ∀ i : Fin N, R (t i.castSucc) (t i.succ) := by
  let N := S.card - 1
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨a, hS.1⟩
  have hc : S.card = N + 1 := by dsimp [N]; omega
  let t := S.orderEmbOfFin hc
  have hr : Set.range t = (S : Set ℝ) := S.range_orderEmbOfFin hc
  have ha : t 0 = a := by
    have ha' : a ∈ Set.range t := by rw [hr]; exact hS.1
    obtain ⟨i, hi⟩ := ha'
    exact le_antisymm (hi ▸ t.monotone (Fin.zero_le i)) (hS.2.2.1 _ (S.orderEmbOfFin_mem hc _)).1
  have hb : t (Fin.last N) = b := by
    have hb' : b ∈ Set.range t := by rw [hr]; exact hS.2.1
    obtain ⟨i, hi⟩ := hb'
    exact le_antisymm (hS.2.2.1 _ (S.orderEmbOfFin_mem hc _)).2
      (hi ▸ t.monotone (Fin.le_last i))
  exact ⟨N, t, t.strictMono, ha, hb, hr,
    fun i => hS.2.2.2 _ _ (ordered_consecutive S hc i)⟩

end LinearInputCurveWordSamplingOrder
