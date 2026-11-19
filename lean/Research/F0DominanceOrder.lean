import Research.F0ImbalanceMonotonicity

/-!
# F0：二塊移動の到達可能性と優越順序、`Φ_d` の優越順序に沿った厳密増加

`F0ImbalanceMonotonicity` は二塊移動 `(a,b) ↦ (a+1,b-1)`（`a ≥ b ≥ 2`）で `Φ_d` が厳密に
増加することを示した。ここでは、どの型からどの型へ二塊移動の列で到達できるかを完全に
特徴づける。

塊サイズ型 `p`（正整数の多重集合）と閾値 `t` について、超過量

`E_p(t) = ∑_{m ∈ p} (m - t)⁺`（自然数の切り捨て減算）

を考える。総和の等しいベクトルについて「すべての `t` で `E_y(t) ≤ E_x(t)`」は、
古典的な majorization（優越）の同値な言い換えとして知られている。この順序を `Dominates x y`
と書く（総和・塊数が等しく、`x` も正）。

* **到達可能性の特徴づけ**（`reachable_iff_dominates`）：正整数の型 `y` から `x` へ二塊移動の
  列（0回を含む）で到達できる ⇔ `Dominates x y`。これは Muirhead の整数移動補題の
  多重集合版である。
* **系**（`phi_lt_of_dominates`）：`d ≥ 1`、`Dominates x y`、`x ≠ y` なら `Φ_d(y) < Φ_d(x)`。

したがって `Φ_d` は、塊数を固定した正整数の型の上で優越順序について狭義単調である。
優越順序で比較できない型どうしの大小は主張しない。sorted ベクトルの部分和による
古典的定義と `excess` による定義の同値性は、この Lean ファイルでは証明していない。
-/

namespace F0DominanceOrder

open Multiset F0ImbalanceMonotonicity

/-! ## 超過量 -/

/-- 超過量 `E_p(t) = ∑_{m ∈ p} (m - t)`（自然数の切り捨て減算）。 -/
def excess (p : Multiset ℕ) (t : ℕ) : ℕ := (p.map (· - t)).sum

/-- 閾値 `t` を超える塊の個数。 -/
def above (p : Multiset ℕ) (t : ℕ) : ℕ := (p.filter (t < ·)).card

/-- 優越順序：正整数の型 `x` は `y` と総和・塊数が等しく、すべての閾値で超過量が大きい。 -/
def Dominates (x y : Multiset ℕ) : Prop :=
  x.card = y.card ∧ x.sum = y.sum ∧ (∀ m ∈ x, 0 < m) ∧ ∀ t, excess y t ≤ excess x t

@[simp] theorem excess_zero_multiset (t : ℕ) : excess 0 t = 0 := by simp [excess]

@[simp] theorem excess_cons (a : ℕ) (p : Multiset ℕ) (t : ℕ) :
    excess (a ::ₘ p) t = (a - t) + excess p t := by simp [excess]

@[simp] theorem above_zero_multiset (t : ℕ) : above 0 t = 0 := by simp [above]

theorem above_cons (a : ℕ) (p : Multiset ℕ) (t : ℕ) :
    above (a ::ₘ p) t = (if t < a then 1 else 0) + above p t := by
  unfold above
  by_cases h : t < a
  · simp [Multiset.filter_cons_of_pos _ h, h, add_comm]
  · simp [Multiset.filter_cons_of_neg _ h, h]

theorem excess_at_zero (p : Multiset ℕ) : excess p 0 = p.sum := by simp [excess]

theorem excess_at_one (p : Multiset ℕ) (hp : ∀ m ∈ p, 0 < m) :
    excess p 1 + p.card = p.sum := by
  induction p using Multiset.induction_on with
  | empty => simp
  | cons a p ih =>
    have ha := hp a (by simp)
    have := ih fun m hm => hp m (by simp [hm])
    simp only [excess_cons, Multiset.card_cons, Multiset.sum_cons]
    omega

/-- 超過量の差分は閾値を超える塊の個数。 -/
theorem excess_eq_succ_add_above (p : Multiset ℕ) (t : ℕ) :
    excess p t = excess p (t + 1) + above p t := by
  induction p using Multiset.induction_on with
  | empty => simp
  | cons a p ih =>
    rw [excess_cons, excess_cons, above_cons, ih]
    split_ifs <;> omega

theorem excess_eq_zero_of_le (p : Multiset ℕ) (t : ℕ) (h : ∀ m ∈ p, m ≤ t) :
    excess p t = 0 := by
  induction p using Multiset.induction_on with
  | empty => simp
  | cons a p ih =>
    have ha := h a (by simp)
    rw [excess_cons, ih fun m hm => h m (by simp [hm])]
    omega

/-- 区間 `(L, U)` にある塊の個数と `above` の関係。 -/
theorem above_split (p : Multiset ℕ) {L U : ℕ} (hLU : L < U) :
    above p L = (p.filter fun m => L < m ∧ m < U).card + above p (U - 1) := by
  induction p using Multiset.induction_on with
  | empty => simp
  | cons a p ih =>
    rw [above_cons, above_cons, ih]
    by_cases h : L < a ∧ a < U
    · rw [Multiset.filter_cons_of_pos (p := fun m => L < m ∧ m < U) _ h]
      simp only [Multiset.card_cons]
      split_ifs <;> omega
    · rw [Multiset.filter_cons_of_neg (p := fun m => L < m ∧ m < U) _ h]
      split_ifs <;> omega

/-! ## 超過量は型を決める -/

theorem count_eq_above_sub (p : Multiset ℕ) (v : ℕ) :
    count (v + 1) p + above p (v + 1) = above p v := by
  induction p using Multiset.induction_on with
  | empty => simp
  | cons a p ih =>
    rw [above_cons, above_cons, Multiset.count_cons, ← ih]
    split_ifs <;> omega

theorem eq_of_excess_eq {x y : Multiset ℕ} (hx : ∀ m ∈ x, 0 < m) (hy : ∀ m ∈ y, 0 < m)
    (h : ∀ t, excess x t = excess y t) : x = y := by
  have habove : ∀ t, above x t = above y t := by
    intro t
    have h1 := excess_eq_succ_add_above x t
    have h2 := excess_eq_succ_add_above y t
    have := h t
    have := h (t + 1)
    omega
  ext v
  rcases v with _ | v
  · rw [Multiset.count_eq_zero.mpr fun h0 => (hx 0 h0).false,
      Multiset.count_eq_zero.mpr fun h0 => (hy 0 h0).false]
  · have h1 := count_eq_above_sub x v
    have h2 := count_eq_above_sub y v
    rw [habove, habove] at h1
    omega

/-! ## 二塊移動は超過量を増やす（到達可能 ⇒ 優越） -/

theorem excess_transfer (a b : ℕ) (rest : Multiset ℕ) (hba : b ≤ a) (t : ℕ) :
    excess ((a + 1) ::ₘ (b - 1) ::ₘ rest) t =
      excess (a ::ₘ b ::ₘ rest) t + (if b ≤ t ∧ t ≤ a then 1 else 0) := by
  simp only [excess_cons]
  split_ifs <;> omega

theorem excess_le_of_transfer {p q : Multiset ℕ} (h : Transfer p q) (t : ℕ) :
    excess p t ≤ excess q t := by
  obtain ⟨a, b, rest, hba, -, rfl, rfl⟩ := h
  rw [excess_transfer a b rest hba]
  omega

theorem dominates_of_reachable {x y : Multiset ℕ} (hy : ∀ m ∈ y, 0 < m)
    (h : Relation.ReflTransGen Transfer y x) : Dominates x y := by
  induction h with
  | refl => exact ⟨rfl, rfl, hy, fun _ => le_rfl⟩
  | tail _ hbc ih =>
    obtain ⟨hc, hs, hp, he⟩ := ih
    exact ⟨(transfer_card hbc).symm.trans hc, (transfer_sum hbc).symm.trans hs,
      transfer_pos hbc hp, fun t => (he t).trans (excess_le_of_transfer hbc t)⟩

/-! ## 優越 ⇒ 到達可能（Muirhead の整数移動補題） -/

/-- 優越している相手に向かって、優越を保ったまま一回移動できる。 -/
theorem exists_transfer_toward {x y : Multiset ℕ} (hy : ∀ m ∈ y, 0 < m)
    (hd : Dominates x y) (hne : x ≠ y) :
    ∃ a b rest, b ≤ a ∧ 2 ≤ b ∧ y = a ::ₘ b ::ₘ rest ∧
      ∀ t, excess ((a + 1) ::ₘ (b - 1) ::ₘ rest) t ≤ excess x t := by
  classical
  obtain ⟨hcard, hsum, hx, hle⟩ := hd
  -- 超過量が真に小さい閾値がある
  obtain ⟨t₀, ht₀⟩ : ∃ t, excess y t < excess x t := by
    by_contra hall
    simp only [not_exists, not_lt] at hall
    exact hne (eq_of_excess_eq hx hy fun t => le_antisymm (hall t) (hle t))
  have hzero0 : excess y 0 = excess x 0 := by rw [excess_at_zero, excess_at_zero, hsum]
  have hzero1 : excess y 1 = excess x 1 := by
    have := excess_at_one x hx
    have := excess_at_one y hy
    omega
  have ht₀2 : 2 ≤ t₀ := by
    by_contra hlt
    rcases (by omega : t₀ = 0 ∨ t₀ = 1) with rfl | rfl <;> omega
  -- 右端：t₀ より大きい最初の一致点
  have hexU : ∃ s, t₀ < s ∧ excess y s = excess x s := by
    refine ⟨x.sum + t₀ + 1, by omega, ?_⟩
    rw [excess_eq_zero_of_le x _ fun m hm => by
          have := Multiset.le_sum_of_mem hm; omega,
        excess_eq_zero_of_le y _ fun m hm => by
          have := Multiset.le_sum_of_mem hm; omega]
  obtain ⟨U, hUeq⟩ : ∃ U, Nat.find hexU = U := ⟨_, rfl⟩
  have hUspec : t₀ < U ∧ excess y U = excess x U := hUeq ▸ Nat.find_spec hexU
  have hUmin : ∀ s, t₀ < s → s < U → excess y s < excess x s := by
    intro s hs hsU
    have := Nat.find_min hexU (hUeq ▸ hsU)
    simp only [not_and] at this
    exact lt_of_le_of_ne (hle s) (this hs)
  -- 左端：t₀ より小さい最後の一致点
  obtain ⟨L, hLeq⟩ : ∃ L, Nat.findGreatest (fun s => excess y s = excess x s) (t₀ - 1) = L :=
    ⟨_, rfl⟩
  have hLspec : excess y L = excess x L := by
    rw [← hLeq]
    exact Nat.findGreatest_spec (P := fun s => excess y s = excess x s) (m := 1) (by omega) hzero1
  have hL1 : 1 ≤ L := by
    rw [← hLeq]
    exact Nat.le_findGreatest (P := fun s => excess y s = excess x s) (by omega) hzero1
  have hLt : L < t₀ := by
    have := Nat.findGreatest_le (P := fun s => excess y s = excess x s) (t₀ - 1)
    omega
  have hLmax : ∀ s, L < s → s < t₀ → excess y s < excess x s := by
    intro s hLs hst
    exact lt_of_le_of_ne (hle s)
      (Nat.findGreatest_is_greatest (P := fun s => excess y s = excess x s) (hLeq ▸ hLs)
        (by omega))
  have hpos : ∀ s, L < s → s < U → excess y s < excess x s := by
    intro s hLs hsU
    rcases lt_trichotomy s t₀ with h | rfl | h
    · exact hLmax s hLs h
    · exact ht₀
    · exact hUmin s h hsU
  -- 区間 (L, U) に y の塊が2個以上ある
  have hLU : L < U := lt_trans hLt hUspec.1
  have hwin : 2 ≤ (y.filter fun m => L < m ∧ m < U).card := by
    have sx := above_split x hLU
    have sy := above_split y hLU
    have ex1 := excess_eq_succ_add_above x L
    have ey1 := excess_eq_succ_add_above y L
    have ex2 := excess_eq_succ_add_above x (U - 1)
    have ey2 := excess_eq_succ_add_above y (U - 1)
    have hU1 : U - 1 + 1 = U := by omega
    rw [hU1] at ex2 ey2
    have d1 := hpos (L + 1) (by omega) (by omega)
    have d2 := hpos (U - 1) (by omega) (by omega)
    have := hUspec.2
    omega
  -- 二つ取り出す
  obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega :
    0 < (y.filter fun m => L < m ∧ m < U).card)
  obtain ⟨s₁, hs₁⟩ := Multiset.exists_cons_of_mem hu
  have hs₁c : 0 < s₁.card := by
    have := congrArg Multiset.card hs₁
    simp only [Multiset.card_cons] at this
    omega
  obtain ⟨v, hv⟩ := Multiset.card_pos_iff_exists_mem.mp hs₁c
  obtain ⟨s₂, hs₂⟩ := Multiset.exists_cons_of_mem hv
  have hu' := (Multiset.mem_filter.mp hu).2
  have hv' : L < v ∧ v < U := by
    have : v ∈ y.filter fun m => L < m ∧ m < U := by
      rw [hs₁]; exact Multiset.mem_cons_of_mem hv
    exact (Multiset.mem_filter.mp this).2
  have hy_eq : y = u ::ₘ v ::ₘ (s₂ + y.filter fun m => ¬ (L < m ∧ m < U)) := by
    conv_lhs => rw [← Multiset.filter_add_not (fun m => L < m ∧ m < U) y]
    rw [hs₁, hs₂]
    simp
  -- 大きい方を a、小さい方を b とする
  have key : ∀ a b rest, b ≤ a → L < b → a < U → y = a ::ₘ b ::ₘ rest →
      ∃ a b rest, b ≤ a ∧ 2 ≤ b ∧ y = a ::ₘ b ::ₘ rest ∧
        ∀ t, excess ((a + 1) ::ₘ (b - 1) ::ₘ rest) t ≤ excess x t := by
    intro a b rest hba hLb haU hyab
    refine ⟨a, b, rest, hba, by omega, hyab, fun t => ?_⟩
    rw [excess_transfer a b rest hba, ← hyab]
    split_ifs with ht
    · have := hpos t (by omega) (by omega)
      omega
    · simpa using hle t
  rcases le_total v u with hvu | huv
  · exact key u v _ hvu hv'.1 hu'.2 hy_eq
  · exact key v u _ huv hu'.1 hv'.2 (hy_eq.trans (Multiset.cons_swap _ _ _))

/-- 到達可能性の測度：超過量の差の総和。 -/
def gap (x y : Multiset ℕ) : ℕ := ∑ t ∈ Finset.range (x.sum + 1), (excess x t - excess y t)

/-- **Muirhead の整数移動補題（多重集合版）**：優越 ⇒ 二塊移動の列で到達可能。 -/
theorem reachable_of_dominates {x : Multiset ℕ} :
    ∀ {y : Multiset ℕ}, (∀ m ∈ y, 0 < m) → Dominates x y →
      Relation.ReflTransGen Transfer y x := by
  intro y
  induction hμ : gap x y using Nat.strong_induction_on generalizing y with
  | _ μ ih =>
    intro hy hd
    by_cases hxy : x = y
    · rw [hxy]
    obtain ⟨a, b, rest, hba, hb, rfl, hstep⟩ := exists_transfer_toward hy hd hxy
    have htr : Transfer (a ::ₘ b ::ₘ rest) ((a + 1) ::ₘ (b - 1) ::ₘ rest) :=
      ⟨a, b, rest, hba, hb, rfl, rfl⟩
    have hd' : Dominates x ((a + 1) ::ₘ (b - 1) ::ₘ rest) :=
      ⟨hd.1.trans (transfer_card htr), hd.2.1.trans (transfer_sum htr), hd.2.2.1, hstep⟩
    have hlt : gap x ((a + 1) ::ₘ (b - 1) ::ₘ rest) < μ := by
      rw [← hμ]
      apply Finset.sum_lt_sum
      · intro t _
        have := excess_le_of_transfer htr t
        omega
      · refine ⟨b, Finset.mem_range.mpr ?_, ?_⟩
        · have : b ≤ (a ::ₘ b ::ₘ rest).sum := by simp; omega
          have := hd.2.1
          omega
        · have h1 := excess_transfer a b rest hba b
          simp only [le_refl, hba, and_self, ↓reduceIte] at h1
          have h2 := hstep b
          omega
    exact Relation.ReflTransGen.head htr (ih _ hlt rfl (transfer_pos htr hy) hd')

/-- **到達可能性の特徴づけ**：正整数の型 `y` から `x` へ二塊移動の列で到達できる ⇔ `x` が `y` に優越。 -/
theorem reachable_iff_dominates {x y : Multiset ℕ} (hy : ∀ m ∈ y, 0 < m) :
    Relation.ReflTransGen Transfer y x ↔ Dominates x y :=
  ⟨dominates_of_reachable hy, reachable_of_dominates hy⟩

/-- **系**：`Φ_d` は優越順序について狭義単調（`d ≥ 1`）。 -/
theorem phi_lt_of_dominates {d : ℕ} (hd : 1 ≤ d) {x y : Multiset ℕ} (hy : ∀ m ∈ y, 0 < m)
    (hdom : Dominates x y) (hne : x ≠ y) : phi d y < phi d x := by
  have h := reachable_of_dominates hy hdom
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hyc, hcx⟩
  · exact absurd rfl hne
  · exact phi_lt_of_transGen hd (Relation.TransGen.head' hyc hcx)

theorem phi_le_of_dominates (d : ℕ) {x y : Multiset ℕ} (hy : ∀ m ∈ y, 0 < m)
    (hdom : Dominates x y) : phi d y ≤ phi d x := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  by_cases hne : x = y
  · rw [hne]
  · exact (phi_lt_of_dominates hd hy hdom hne).le

/-! ## 例 -/

/-- `(4,2,1)` は `(3,3,1)` に優越する（実際に移動一回で到達する）。 -/
theorem example_dominates : Dominates {4, 2, 1} {3, 3, 1} := by
  refine ⟨by decide, by decide, by decide, fun t => ?_⟩
  rcases Nat.lt_or_ge t 5 with ht | ht
  · interval_cases t <;> decide
  · rw [excess_eq_zero_of_le _ _ (by intro m hm; simp at hm; omega),
      excess_eq_zero_of_le _ _ (by intro m hm; simp at hm; omega)]

/-- 優越順序で比較できない型の例：同じ総量・塊数の `(5,2,2,1,1)` と `(4,4,1,1,1)` は、
どちらの向きにも優越しない（閾値2と4で超過量の大小が逆転する）。 -/
theorem example_incomparable :
    ¬ Dominates ({5, 2, 2, 1, 1} : Multiset ℕ) {4, 4, 1, 1, 1} ∧
      ¬ Dominates ({4, 4, 1, 1, 1} : Multiset ℕ) {5, 2, 2, 1, 1} := by
  constructor
  · rintro ⟨-, -, -, h⟩
    exact absurd (h 2) (by decide)
  · rintro ⟨-, -, -, h⟩
    exact absurd (h 4) (by decide)

end F0DominanceOrder

#print axioms F0DominanceOrder.reachable_iff_dominates
#print axioms F0DominanceOrder.phi_lt_of_dominates
