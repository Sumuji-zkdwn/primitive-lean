import Mathlib.Tactic

/-!
# 非負重みの隣接行列：冪零 ⇔ 有向閉路なし

`docs/research/2026-11-17-square-zero-network.md` の論理的境界1で「DAG iff `A^n = 0` は
単位・非負辺重みの有向グラフについての関係で、Lean での普遍命題（任意の有限 `n`・グラフ）は
未形式化」とされていた命題を、任意の有限頂点集合と、和・積で打ち消しが起こらない係数
（`ℕ`、`ℝ≥0` など：標準順序の加法、零因子なし）について証明する。

頂点集合 `n`（有限）、行列 `A : Matrix n n R` について、辺 `i → j` を `A i j ≠ 0` で定める。

* `(A ^ k) i j ≠ 0` ⇔ 長さ `k` の有向歩道 `i → … → j` がある（`pow_apply_ne_zero_iff`）。
* `A ^ |n| = 0` ⇔ 有向閉路がない ⇔ `A` は冪零（`pow_card_eq_zero_iff_acyclic`、
  `isNilpotent_iff_acyclic`）。
* 一方向「非巡回 ⇒ `A ^ |n| = 0`」は**任意の半環**（`ℤ`、`ℝ` を含む）で成り立つ
  （`pow_card_eq_zero_of_acyclic`、`isNilpotent_of_acyclic`）。

係数に打ち消しがあると同値は崩れる：整数行列 `!![1, 1; -1, -1]` は自己ループを持つが
`A ^ 2 = 0`（`signed_counterexample`）。
-/

namespace AcyclicNilpotent

open Matrix

variable {n : Type*}

/-! ## 辺・歩道・閉路 -/

/-- 辺 `i → j`：重みが零でない。 -/
def Edge {R : Type*} [Zero R] (A : Matrix n n R) (i j : n) : Prop := A i j ≠ 0

/-- 長さ `k` の有向歩道。 -/
def Walk {R : Type*} [Zero R] (A : Matrix n n R) : ℕ → n → n → Prop
  | 0, i, j => i = j
  | k + 1, i, j => ∃ l, Edge A i l ∧ Walk A k l j

/-- 有向閉路（長さ1以上で同じ頂点に戻る歩道）がある。 -/
def HasCycle {R : Type*} [Zero R] (A : Matrix n n R) : Prop :=
  ∃ i, Relation.TransGen (Edge A) i i

section Walks

variable {R : Type*} [Zero R] (A : Matrix n n R)

theorem walk_add {a b : ℕ} {i j k : n} (h₁ : Walk A a i j) (h₂ : Walk A b j k) :
    Walk A (a + b) i k := by
  induction a generalizing i with
  | zero => simp only [Walk] at h₁; subst h₁; simpa using h₂
  | succ a ih =>
    obtain ⟨l, hil, hl⟩ := h₁
    rw [Nat.add_right_comm]
    exact ⟨l, hil, ih hl⟩

theorem walk_succ_right {k : ℕ} {i j l : n} (h : Walk A k i j) (hjl : Edge A j l) :
    Walk A (k + 1) i l :=
  walk_add A h ⟨l, hjl, rfl⟩

/-- 推移閉包は長さ1以上の歩道。 -/
theorem transGen_iff_walk {i j : n} :
    Relation.TransGen (Edge A) i j ↔ ∃ k, Walk A (k + 1) i j := by
  constructor
  · intro h
    induction h with
    | single h => exact ⟨0, _, h, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, walk_succ_right A hk hbc⟩
  · rintro ⟨k, hk⟩
    induction k generalizing i with
    | zero =>
      obtain ⟨l, hil, rfl⟩ := hk
      exact Relation.TransGen.single hil
    | succ k ih =>
      obtain ⟨l, hil, hl⟩ := hk
      exact Relation.TransGen.head hil (ih hl)

theorem walk_mul {k : ℕ} {i : n} (h : Walk A k i i) (m : ℕ) : Walk A (m * k) i i := by
  induction m with
  | zero => simp [Walk]
  | succ m ih =>
    rw [Nat.succ_mul]
    exact walk_add A ih h

/-- 歩道を頂点の列として書く。 -/
theorem walk_iff_seq {k : ℕ} {i j : n} :
    Walk A k i j ↔ ∃ w : ℕ → n, w 0 = i ∧ w k = j ∧ ∀ t < k, Edge A (w t) (w (t + 1)) := by
  induction k generalizing i with
  | zero =>
    constructor
    · intro h
      exact ⟨fun _ => i, rfl, h, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
    · rintro ⟨w, h0, hk, -⟩
      exact h0 ▸ hk
  | succ k ih =>
    constructor
    · rintro ⟨l, hil, hl⟩
      obtain ⟨w, h0, hk, hw⟩ := (ih (i := l)).mp hl
      refine ⟨fun t => if t = 0 then i else w (t - 1), by simp, by simpa using hk, ?_⟩
      intro t ht
      rcases t with _ | t
      · simpa [h0] using hil
      · simpa using hw t (by omega)
    · rintro ⟨w, h0, hk, hw⟩
      refine ⟨w 1, h0 ▸ hw 0 (by omega), (ih (i := w 1)).mpr ⟨fun t => w (t + 1), rfl, ?_, ?_⟩⟩
      · simpa [Nat.add_comm] using hk
      · intro t ht
        exact hw (t + 1) (by omega)

/-- 列の区間は推移閉包の辺をつなぐ。 -/
theorem seq_transGen {k : ℕ} {w : ℕ → n} (hw : ∀ t < k, Edge A (w t) (w (t + 1)))
    {s t : ℕ} (hst : s < t) (htk : t ≤ k) : Relation.TransGen (Edge A) (w s) (w t) := by
  induction t with
  | zero => exact absurd hst (Nat.not_lt_zero s)
  | succ t ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hst with h | rfl
    · exact Relation.TransGen.tail (ih h (by omega)) (hw t (by omega))
    · exact Relation.TransGen.single (hw s (by omega))

/-- 頂点数以上の長さの歩道は閉路を含む（鳩の巣原理）。 -/
theorem hasCycle_of_walk [Fintype n] {k : ℕ} (hk : Fintype.card n ≤ k) {i j : n} (h : Walk A k i j) :
    HasCycle A := by
  obtain ⟨w, -, -, hw⟩ := (walk_iff_seq A).mp h
  obtain ⟨s, t, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun t : Fin (k + 1) => w t) (by simp; omega)
  have hs := s.isLt
  have ht := t.isLt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · have h := seq_transGen A hw hlt (by omega)
    rw [← heq] at h
    exact ⟨w s, h⟩
  · have h := seq_transGen A hw hlt (by omega)
    rw [heq] at h
    exact ⟨w t, h⟩

/-- 辺に沿って真に増える順位関数があれば閉路はない（位相順序）。 -/
theorem not_hasCycle_of_rank (f : n → ℕ) (hf : ∀ a b, Edge A a b → f a < f b) :
    ¬ HasCycle A := by
  rintro ⟨i, hi⟩
  have key : ∀ a b, Relation.TransGen (Edge A) a b → f a < f b := by
    intro a b h
    induction h with
    | single h => exact hf _ _ h
    | tail _ h ih => exact ih.trans (hf _ _ h)
  exact lt_irrefl _ (key i i hi)

end Walks

/-! ## 任意の半環：非巡回 ⇒ 冪零 -/

section AnySemiring

variable [Fintype n] [DecidableEq n] {S : Type*} [Semiring S]

/-- 任意の半環で、冪の成分が零でなければその長さの歩道がある（逆は打ち消しがあると偽）。 -/
theorem walk_of_pow_apply_ne_zero (A : Matrix n n S) (k : ℕ) (i j : n) :
    (A ^ k) i j ≠ 0 → Walk A k i j := by
  induction k generalizing i with
  | zero =>
    intro h
    by_contra hij
    exact h (by simp [Matrix.one_apply_ne hij])
  | succ k ih =>
    intro h
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact ⟨l, left_ne_zero_of_mul hl, ih l (right_ne_zero_of_mul hl)⟩

/-- **任意の半環**（`ℤ`、`ℝ` を含む）：非零辺のグラフが非巡回なら `A ^ |n| = 0`。 -/
theorem pow_card_eq_zero_of_acyclic {A : Matrix n n S} (hc : ¬ HasCycle A) :
    A ^ Fintype.card n = 0 := by
  ext i j
  by_contra hne
  exact hc (hasCycle_of_walk A le_rfl (walk_of_pow_apply_ne_zero A _ i j hne))

theorem isNilpotent_of_acyclic {A : Matrix n n S} (hc : ¬ HasCycle A) : IsNilpotent A :=
  ⟨_, pow_card_eq_zero_of_acyclic hc⟩

end AnySemiring

/-! ## 打ち消しのない係数：冪と歩道の同値 -/

variable [Fintype n] [DecidableEq n]
  {R : Type*} [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [NoZeroDivisors R]
  [Nontrivial R]

/-- 打ち消しのない係数では、冪の成分が零でないことと歩道の存在は同値。 -/
theorem pow_apply_ne_zero_iff (A : Matrix n n R) (k : ℕ) (i j : n) :
    (A ^ k) i j ≠ 0 ↔ Walk A k i j := by
  induction k generalizing i with
  | zero =>
    simp only [pow_zero, Walk]
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h, h]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, Ne, Finset.sum_eq_zero_iff]
    simp only [Finset.mem_univ, true_implies, not_forall, Walk, Edge]
    constructor
    · rintro ⟨l, hl⟩
      exact ⟨l, left_ne_zero_of_mul hl, (ih l).mp (right_ne_zero_of_mul hl)⟩
    · rintro ⟨l, hil, hl⟩
      exact ⟨l, mul_ne_zero hil ((ih l).mpr hl)⟩

theorem pow_eq_zero_iff_no_walk (A : Matrix n n R) (k : ℕ) :
    A ^ k = 0 ↔ ∀ i j, ¬ Walk A k i j := by
  constructor
  · intro h i j hw
    exact (pow_apply_ne_zero_iff A k i j).mpr hw (by rw [h]; rfl)
  · intro h
    ext i j
    by_contra hne
    exact h i j ((pow_apply_ne_zero_iff A k i j).mp hne)

/-- 閉路があればどの冪も零でない。 -/
theorem pow_ne_zero_of_hasCycle {A : Matrix n n R} (hc : HasCycle A) (N : ℕ) : A ^ N ≠ 0 := by
  obtain ⟨i, hi⟩ := hc
  obtain ⟨k, hk⟩ := (transGen_iff_walk A).mp hi
  intro hN
  have hM : A ^ (N * (k + 1)) = 0 := by
    rw [pow_mul, hN, zero_pow (by omega)]
  exact (pow_eq_zero_iff_no_walk A _).mp hM i i (walk_mul A hk N)

/-- **主定理1**：`A ^ |n| = 0` ⇔ 有向閉路がない。 -/
theorem pow_card_eq_zero_iff_acyclic (A : Matrix n n R) :
    A ^ Fintype.card n = 0 ↔ ¬ HasCycle A :=
  ⟨fun h hc => pow_ne_zero_of_hasCycle hc _ h, pow_card_eq_zero_of_acyclic⟩

/-- **主定理2**：冪零 ⇔ 有向閉路がない。 -/
theorem isNilpotent_iff_acyclic (A : Matrix n n R) : IsNilpotent A ↔ ¬ HasCycle A :=
  ⟨fun ⟨N, hN⟩ hc => pow_ne_zero_of_hasCycle hc N hN,
    fun hc => ⟨_, pow_card_eq_zero_of_acyclic hc⟩⟩

/-- 冪零なら、頂点数の冪ですでに零。 -/
theorem isNilpotent_iff_pow_card (A : Matrix n n R) :
    IsNilpotent A ↔ A ^ Fintype.card n = 0 := by
  rw [isNilpotent_iff_acyclic, pow_card_eq_zero_iff_acyclic]

/-- 閉路があれば、冪の成分は周期的に零でない（同じ頂点への歩道が何度でも戻る）。 -/
theorem pow_diag_ne_zero_of_cycle {A : Matrix n n R} {i : n} {k : ℕ} (hk : Walk A (k + 1) i i)
    (m : ℕ) : (A ^ (m * (k + 1))) i i ≠ 0 :=
  (pow_apply_ne_zero_iff A _ i i).mpr (walk_mul A hk m)

/-! ## 例 -/

/-- 自然数係数の例：三頂点の推移的トーナメント（`0 → 1 → 2`, `0 → 2`）は冪零。 -/
theorem tournament_nilpotent :
    IsNilpotent (!![0, 1, 1; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℕ) :=
  ⟨3, by decide⟩

/-- 二頂点の往復（`0 → 1 → 0`）は閉路なので、どの冪も零でない。 -/
theorem two_cycle_not_nilpotent :
    ¬ IsNilpotent (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) := by
  rw [isNilpotent_iff_acyclic, not_not]
  refine ⟨0, Relation.TransGen.tail (b := 1) (Relation.TransGen.single ?_) ?_⟩ <;>
    · unfold Edge
      decide

/-- 閉路は増幅を意味しない：重み1の二頂点往復では `A ^ 2 = 1`（どの冪も置換行列）。 -/
theorem unit_two_cycle_sq_eq_one :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) ^ 2 = 1 := by
  decide

/-- 整数係数でも、非巡回な例は冪零（`isNilpotent_of_acyclic` の適用例）。 -/
theorem signed_acyclic_nilpotent :
    IsNilpotent (!![0, -3; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) := by
  apply isNilpotent_of_acyclic
  apply not_hasCycle_of_rank _ (fun a : Fin 2 => (a : ℕ))
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [Edge] at h ⊢

/-- **打ち消しがあると同値は崩れる**：整数行列 `!![1, 1; -1, -1]` は自己ループ（閉路）を
持つが `A ^ 2 = 0`。 -/
theorem signed_counterexample :
    let A : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; -1, -1]
    A ^ 2 = 0 ∧ HasCycle A := by
  refine ⟨by decide, 0, Relation.TransGen.single ?_⟩
  unfold Edge
  decide

end AcyclicNilpotent

#print axioms AcyclicNilpotent.pow_apply_ne_zero_iff
#print axioms AcyclicNilpotent.pow_card_eq_zero_iff_acyclic
#print axioms AcyclicNilpotent.isNilpotent_iff_acyclic
#print axioms AcyclicNilpotent.signed_counterexample
