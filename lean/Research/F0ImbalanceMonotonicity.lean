import Mathlib.Tactic

/-!
# F0 偏在単調性：二塊移動による `Φ_d` の厳密増加

F0 の会話資料（`sources/f0_math_chat_2026-10-29/03_conjecture_and_cautions.md`）で
未証明予想として保持されていた命題を一般に証明する。塊サイズ型を
`F0MergeChains.inc` と同じく `Multiset ℕ` で表し、

`Φ_d(m_1,…,m_r) = ∏_i (∑_j m_j^(m_i-1))^d`

とおく。総量 `N` と塊数 `r` を保つ二塊移動 `(a,b) ↦ (a+1,b-1)`（`a ≥ b > 1`）について、
`d ≥ 1` なら `Φ_d` は厳密に増加する（`phi_lt_of_transfer`）。

証明の骨格は次の二つの初等不等式である。

* 交換不等式：`c < a` かつ `n ≥ 2` なら `a^n + (c+1)^n < (a+1)^n + c^n`。
  これにより、移動後の各べき和は移動前以上で、指数 `a` では真に大きい。
* べき和の対数凸性：`P(e+1) P(e+k) ≤ P(e) P(e+k+1)`（`P(n) = ∑ m^n`）。
  これにより、移動した二塊の因子の積は指数の組 `(a-1, b-1)` から `(a, b-2)` へ移って減らない。

系として、総量 `N` と塊数 `r` を固定した正整数の型の中で、最も偏った型
`(N-r+1, 1, …, 1)` が `Φ_d` の一意な最大点であることを示す（`phi_lt_hook`）。

塊数が変わる合流については単調性が成り立たないことを、会話資料の数値例で確認する
（`merge_can_increase`, `merge_chain_endpoints_decrease`）。

この定理は二塊移動という基本操作についての主張であり、majorization 順序で比較
できない型どうしの大小や、成分を正の実数へ広げた主張は含まない。
-/

namespace F0ImbalanceMonotonicity

open Multiset

/-! ## 定義 -/

/-- 多重集合 `p` の `e` 乗べき和 `∑_{m ∈ p} m^e`。 -/
def powerSum (p : Multiset ℕ) (e : ℕ) : ℕ := (p.map (· ^ e)).sum

/-- `Φ_1`：`∏_i ∑_j m_j^(m_i-1)`。 -/
def base (p : Multiset ℕ) : ℕ := (p.map fun m => powerSum p (m - 1)).prod

/-- 会話中の量 `Φ_d(m_1,…,m_r) = ∏_i (∑_j m_j^(m_i-1))^d`。 -/
def phi (d : ℕ) (p : Multiset ℕ) : ℕ := (p.map fun m => powerSum p (m - 1) ^ d).prod

/-- 偏在化の基本移動 `(a,b) ↦ (a+1,b-1)`（`a ≥ b > 1`）。他の塊 `rest` は変えない。 -/
def Transfer (p q : Multiset ℕ) : Prop :=
  ∃ a b : ℕ, ∃ rest : Multiset ℕ,
    b ≤ a ∧ 2 ≤ b ∧ p = a ::ₘ b ::ₘ rest ∧ q = (a + 1) ::ₘ (b - 1) ::ₘ rest

/-- 総量 `N`・塊数 `r` の最も偏った型 `(N-r+1, 1^(r-1))`。 -/
def hook (N r : ℕ) : Multiset ℕ := (N - r + 1) ::ₘ replicate (r - 1) 1

/-! ## べき和の基本性質 -/

@[simp] theorem powerSum_zero_multiset (e : ℕ) : powerSum 0 e = 0 := by
  simp [powerSum]

@[simp] theorem powerSum_cons (a : ℕ) (p : Multiset ℕ) (e : ℕ) :
    powerSum (a ::ₘ p) e = a ^ e + powerSum p e := by
  simp [powerSum]

theorem phi_eq_base_pow (d : ℕ) (p : Multiset ℕ) : phi d p = base p ^ d := by
  simp only [phi, base]
  exact Multiset.prod_map_pow

/-- 指数 `0` では `Φ_0 = 1` なので、厳密増加には `d ≥ 1` が必要。 -/
@[simp] theorem phi_zero (p : Multiset ℕ) : phi 0 p = 1 := by
  simp [phi]

theorem phi_one (p : Multiset ℕ) : phi 1 p = base p := by
  simp [phi_eq_base_pow]

/-- 添字付きの形：塊を有限型 `ι` で添字付け、塊サイズを `m : ι → ℕ` とすると
`Φ_d = ∏_i (∑_j m_j^(m_i-1))^d`。右辺は `F0Retractions.inc` の `compatible_split_count`
（`ι = Fixed K`, `m a = Nat.card (Fiber K a)`, `d = Fintype.card I`）の右辺と同じ形である。 -/
theorem phi_map_univ {ι : Type*} [Fintype ι] (m : ι → ℕ) (d : ℕ) :
    phi d (Finset.univ.val.map m) = ∏ i, (∑ j, m j ^ (m i - 1)) ^ d := by
  simp only [phi, powerSum, Multiset.map_map, Function.comp_def]
  rfl

theorem pow_le_powerSum {a : ℕ} {p : Multiset ℕ} (ha : a ∈ p) (e : ℕ) :
    a ^ e ≤ powerSum p e := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  simp

theorem powerSum_pos {a : ℕ} {p : Multiset ℕ} (ha : a ∈ p) (ha0 : 0 < a) (e : ℕ) :
    0 < powerSum p e :=
  lt_of_lt_of_le (Nat.pow_pos ha0) (pow_le_powerSum ha e)

/-! ## 交換不等式 -/

/-- `x^n` の前進差分の単調性：`c ≤ a` なら `a^n + (c+1)^n ≤ (a+1)^n + c^n`。 -/
theorem pow_exchange_le (a c : ℕ) (h : c ≤ a) (n : ℕ) :
    a ^ n + (c + 1) ^ n ≤ (a + 1) ^ n + c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : a ^ n ≤ (a + 1) ^ n := Nat.pow_le_pow_left (by omega) n
    have hC : (c + 1) ^ n ≤ (a + 1) ^ n := Nat.pow_le_pow_left (by omega) n
    rw [pow_succ, pow_succ, pow_succ, pow_succ]
    nlinarith [Nat.mul_le_mul_left c ih, Nat.mul_le_mul h hA]

/-- 狭義版：`c < a` かつ `n ≥ 2` なら `a^n + (c+1)^n < (a+1)^n + c^n`。 -/
theorem pow_exchange_lt (a c : ℕ) (h : c < a) {n : ℕ} (hn : 2 ≤ n) :
    a ^ n + (c + 1) ^ n < (a + 1) ^ n + c ^ n := by
  induction n, hn using Nat.le_induction with
  | base => nlinarith
  | succ n hn ih =>
    have hA : a ^ n ≤ (a + 1) ^ n := Nat.pow_le_pow_left (by omega) n
    have hC : (c + 1) ^ n < (a + 1) ^ n := Nat.pow_lt_pow_left (by omega) (by omega)
    rw [pow_succ, pow_succ, pow_succ, pow_succ]
    nlinarith [Nat.mul_le_mul_left c ih.le, Nat.mul_le_mul h.le hA]

/-! ## べき和の対数凸性 -/

/-- 二点の並べ替え不等式：`x^(e+1) y^(e+k) + x^(e+k) y^(e+1) ≤ x^e y^(e+k+1) + x^(e+k+1) y^e`。 -/
theorem pair_cross_le (x y e k : ℕ) :
    x ^ (e + 1) * y ^ (e + k) + x ^ (e + k) * y ^ (e + 1) ≤
      x ^ e * y ^ (e + k + 1) + x ^ (e + k + 1) * y ^ e := by
  have key : x * y ^ k + y * x ^ k ≤ x * x ^ k + y * y ^ k := by
    rcases le_total x y with hxy | hxy
    · exact mul_add_mul_le_mul_add_mul hxy (Nat.pow_le_pow_left hxy k)
    · have := mul_add_mul_le_mul_add_mul hxy (Nat.pow_le_pow_left hxy k)
      linarith
  have e1 : x ^ (e + 1) * y ^ (e + k) + x ^ (e + k) * y ^ (e + 1) =
      x ^ e * y ^ e * (x * y ^ k + y * x ^ k) := by ring
  have e2 : x ^ e * y ^ (e + k + 1) + x ^ (e + k + 1) * y ^ e =
      x ^ e * y ^ e * (x * x ^ k + y * y ^ k) := by ring
  rw [e1, e2]
  exact Nat.mul_le_mul_left _ key

/-- 一点と多重集合の交差項。 -/
theorem cross_le (x : ℕ) (Y : Multiset ℕ) (e k : ℕ) :
    x ^ (e + 1) * powerSum Y (e + k) + x ^ (e + k) * powerSum Y (e + 1) ≤
      x ^ e * powerSum Y (e + k + 1) + x ^ (e + k + 1) * powerSum Y e := by
  induction Y using Multiset.induction_on with
  | empty => simp
  | cons y Y ih =>
    simp only [powerSum_cons, mul_add]
    have := pair_cross_le x y e k
    linarith

/-- べき和の対数凸性：`P(e+1) P(e+k) ≤ P(e) P(e+k+1)`。 -/
theorem powerSum_mul_le (X : Multiset ℕ) (e k : ℕ) :
    powerSum X (e + 1) * powerSum X (e + k) ≤ powerSum X e * powerSum X (e + k + 1) := by
  induction X using Multiset.induction_on with
  | empty => simp
  | cons x X ih =>
    simp only [powerSum_cons]
    have hx : x ^ (e + 1) * x ^ (e + k) = x ^ e * x ^ (e + k + 1) := by ring
    have hc := cross_le x X e k
    nlinarith [hx, hc, ih]

/-! ## 主定理：二塊移動で `Φ_d` は厳密に増加する -/

theorem transfer_sum {p q : Multiset ℕ} (h : Transfer p q) : p.sum = q.sum := by
  obtain ⟨a, b, rest, _, hb, rfl, rfl⟩ := h
  simp only [Multiset.sum_cons]
  omega

theorem transfer_card {p q : Multiset ℕ} (h : Transfer p q) : p.card = q.card := by
  obtain ⟨a, b, rest, _, _, rfl, rfl⟩ := h
  simp

theorem transfer_pos {p q : Multiset ℕ} (h : Transfer p q) (hp : ∀ m ∈ p, 0 < m) :
    ∀ m ∈ q, 0 < m := by
  obtain ⟨a, b, rest, _, hb, rfl, hq⟩ := h
  subst hq
  intro m hm
  simp only [Multiset.mem_cons] at hm
  rcases hm with rfl | rfl | hm
  · omega
  · omega
  · exact hp m (by simp [hm])

/-- 移動後のべき和は、すべての指数で移動前以上。 -/
theorem powerSum_le_of_transfer (a b : ℕ) (rest : Multiset ℕ) (hba : b ≤ a) (hb : 1 ≤ b)
    (n : ℕ) :
    powerSum (a ::ₘ b ::ₘ rest) n ≤ powerSum ((a + 1) ::ₘ (b - 1) ::ₘ rest) n := by
  have := pow_exchange_le a (b - 1) (by omega) n
  rw [Nat.sub_add_cancel hb] at this
  simp only [powerSum_cons]
  omega

/-- 指数 `a` では真に大きい。 -/
theorem powerSum_lt_of_transfer (a b : ℕ) (rest : Multiset ℕ) (hba : b ≤ a) (hb : 2 ≤ b) :
    powerSum (a ::ₘ b ::ₘ rest) a < powerSum ((a + 1) ::ₘ (b - 1) ::ₘ rest) a := by
  have := pow_exchange_lt a (b - 1) (by omega) (show 2 ≤ a by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ b)] at this
  simp only [powerSum_cons]
  omega

/-- 単調な因子の積の比較。 -/
theorem prod_map_le_prod_map_nat (s : Multiset ℕ) (f g : ℕ → ℕ) (h : ∀ m, f m ≤ g m) :
    (s.map f).prod ≤ (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons m s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact Nat.mul_le_mul (h m) ih

theorem prod_map_pos_nat (s : Multiset ℕ) (g : ℕ → ℕ) (h : ∀ m, 0 < g m) :
    0 < (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons m s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact Nat.mul_pos (h m) ih

/-- `Φ_1` の厳密増加。 -/
theorem base_lt_of_transfer {p q : Multiset ℕ} (h : Transfer p q) : base p < base q := by
  obtain ⟨a, b, rest, hba, hb, rfl, rfl⟩ := h
  set X := a ::ₘ b ::ₘ rest with hX
  set Y := (a + 1) ::ₘ (b - 1) ::ₘ rest with hY
  -- 二塊の因子と残りの因子に分ける
  have hbaseX : base X =
      powerSum X (a - 1) * (powerSum X (b - 1) * (rest.map fun m => powerSum X (m - 1)).prod) := by
    simp [base, hX]
  have hbaseY : base Y =
      powerSum Y a * (powerSum Y (b - 2) * (rest.map fun m => powerSum Y (m - 1)).prod) := by
    simp only [base, hY, Multiset.map_cons, Multiset.prod_cons, Nat.add_sub_cancel]
    rfl
  -- 各べき和の比較
  have hle : ∀ n, powerSum X n ≤ powerSum Y n :=
    powerSum_le_of_transfer a b rest hba (by omega)
  have hlt : powerSum X a < powerSum Y a := powerSum_lt_of_transfer a b rest hba hb
  have hYpos : ∀ n, 0 < powerSum Y n :=
    fun n => powerSum_pos (a := a + 1) (by simp [hY]) (by omega) n
  -- 対数凸性：指数 (a-1, b-1) から (a, b-2) へ
  have hconv : powerSum X (b - 1) * powerSum X (a - 1) ≤ powerSum X (b - 2) * powerSum X a := by
    have := powerSum_mul_le X (b - 2) (a + 1 - b)
    have e1 : b - 2 + 1 = b - 1 := by omega
    have e2 : b - 2 + (a + 1 - b) = a - 1 := by omega
    have e3 : b - 2 + (a + 1 - b) + 1 = a := by omega
    rwa [e3, e2, e1] at this
  -- 残りの因子
  have hrest : (rest.map fun m => powerSum X (m - 1)).prod ≤
      (rest.map fun m => powerSum Y (m - 1)).prod :=
    prod_map_le_prod_map_nat rest _ _ (fun m => hle (m - 1))
  have hrestpos : 0 < (rest.map fun m => powerSum Y (m - 1)).prod :=
    prod_map_pos_nat rest _ (fun m => hYpos (m - 1))
  -- 二塊の因子の積は真に増える
  have hpair : powerSum X (a - 1) * powerSum X (b - 1) < powerSum Y a * powerSum Y (b - 2) := by
    calc powerSum X (a - 1) * powerSum X (b - 1)
        = powerSum X (b - 1) * powerSum X (a - 1) := Nat.mul_comm _ _
      _ ≤ powerSum X (b - 2) * powerSum X a := hconv
      _ = powerSum X a * powerSum X (b - 2) := Nat.mul_comm _ _
      _ < powerSum Y a * powerSum Y (b - 2) :=
          Nat.mul_lt_mul_of_lt_of_le hlt (hle (b - 2)) (hYpos (b - 2))
  rw [hbaseX, hbaseY, ← Nat.mul_assoc, ← Nat.mul_assoc]
  calc powerSum X (a - 1) * powerSum X (b - 1) * (rest.map fun m => powerSum X (m - 1)).prod
      ≤ powerSum X (a - 1) * powerSum X (b - 1) * (rest.map fun m => powerSum Y (m - 1)).prod :=
        Nat.mul_le_mul_left _ hrest
    _ < powerSum Y a * powerSum Y (b - 2) * (rest.map fun m => powerSum Y (m - 1)).prod :=
        Nat.mul_lt_mul_of_pos_right hpair hrestpos

/-- **主定理（偏在単調性）**：`d ≥ 1` なら、二塊移動 `(a,b) ↦ (a+1,b-1)`（`a ≥ b > 1`）で
`Φ_d` は厳密に増加する。他の塊には条件を課さない。 -/
theorem phi_lt_of_transfer {d : ℕ} (hd : 1 ≤ d) {p q : Multiset ℕ} (h : Transfer p q) :
    phi d p < phi d q := by
  rw [phi_eq_base_pow, phi_eq_base_pow]
  exact Nat.pow_lt_pow_left (base_lt_of_transfer h) (by omega)

/-- 成分ごとの形で述べた主定理。 -/
theorem phi_lt_cons {d : ℕ} (hd : 1 ≤ d) {a b : ℕ} (hba : b ≤ a) (hb : 2 ≤ b)
    (rest : Multiset ℕ) :
    phi d (a ::ₘ b ::ₘ rest) < phi d ((a + 1) ::ₘ (b - 1) ::ₘ rest) :=
  phi_lt_of_transfer hd ⟨a, b, rest, hba, hb, rfl, rfl⟩

/-- 二塊移動を何回か（1回以上）繰り返しても `Φ_d` は厳密に増加する。 -/
theorem phi_lt_of_transGen {d : ℕ} (hd : 1 ≤ d) {p q : Multiset ℕ}
    (h : Relation.TransGen Transfer p q) : phi d p < phi d q := by
  induction h with
  | single h => exact phi_lt_of_transfer hd h
  | tail _ h ih => exact ih.trans (phi_lt_of_transfer hd h)

/-! ## 系：固定した総量・塊数での一意な最大点 -/

theorem hook_card {r : ℕ} (hr : 1 ≤ r) (N : ℕ) : (hook N r).card = r := by
  simp [hook]
  omega

theorem hook_sum {N r : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N) : (hook N r).sum = N := by
  simp [hook]
  omega

theorem hook_pos (N r : ℕ) : ∀ m ∈ hook N r, 0 < m := by
  intro m hm
  simp only [hook, Multiset.mem_cons] at hm
  rcases hm with rfl | hm
  · omega
  · rw [Multiset.eq_of_mem_replicate hm]; omega

/-- 平方和は総和の平方以下。 -/
theorem powerSum_two_le_sq_sum (p : Multiset ℕ) : powerSum p 2 ≤ p.sum ^ 2 := by
  induction p using Multiset.induction_on with
  | empty => simp
  | cons a p ih =>
    simp only [powerSum_cons, Multiset.sum_cons]
    nlinarith [Nat.zero_le (a * p.sum)]

/-- 二塊移動で平方和は真に増える（停止性の測度）。 -/
theorem powerSum_two_lt_of_transfer {p q : Multiset ℕ} (h : Transfer p q) :
    powerSum p 2 < powerSum q 2 := by
  obtain ⟨a, b, rest, hba, hb, rfl, rfl⟩ := h
  have := pow_exchange_lt a (b - 1) (by omega) (le_refl 2)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ b)] at this
  simp only [powerSum_cons]
  omega

/-- 正整数の型が最も偏った型でなければ、二塊移動を適用できる。 -/
theorem exists_transfer_of_ne_hook {p : Multiset ℕ} (hpos : ∀ m ∈ p, 0 < m)
    (hr : 1 ≤ p.card) (hne : p ≠ hook p.sum p.card) :
    ∃ q, Transfer p q := by
  classical
  set big := p.filter (2 ≤ ·) with hbig
  set small := p.filter (fun m => ¬ 2 ≤ m) with hsmall
  have hsplit : big + small = p := Multiset.filter_add_not _ p
  have hsmall_rep : small = replicate small.card 1 := by
    rw [Multiset.eq_replicate]
    refine ⟨rfl, fun m hm => ?_⟩
    rw [hsmall, Multiset.mem_filter] at hm
    have := hpos m hm.1
    omega
  by_cases h2 : 2 ≤ big.card
  · -- 2以上の塊が二つある
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < big.card)
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hx
    have htc : 0 < t.card := by
      have := congrArg Multiset.card ht
      simp at this
      omega
    obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.mp htc
    obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem hy
    have hx2 : 2 ≤ x := (Multiset.mem_filter.mp hx).2
    have hy2 : 2 ≤ y := by
      have : y ∈ big := by rw [ht]; exact Multiset.mem_cons_of_mem hy
      exact (Multiset.mem_filter.mp this).2
    have hp : p = x ::ₘ y ::ₘ (u + small) := by
      rw [← hsplit, ht, hu]
      simp
    rcases le_total y x with hyx | hxy
    · exact ⟨_, x, y, u + small, hyx, hy2, hp, rfl⟩
    · exact ⟨_, y, x, u + small, hxy, hx2, by rw [hp, Multiset.cons_swap], rfl⟩
  · -- 2以上の塊は高々一つ：最も偏った型に一致してしまう
    exfalso
    apply hne
    have hpcard : p.card = big.card + small.card := by
      rw [← hsplit, Multiset.card_add]
    have hpsum : p.sum = big.sum + small.card := by
      conv_lhs => rw [← hsplit]
      rw [Multiset.sum_add, hsmall_rep]
      simp
    rcases (by omega : big.card = 0 ∨ big.card = 1) with h0 | h1
    · have hb0 : big = 0 := Multiset.card_eq_zero.mp h0
      have hp : p = replicate small.card 1 := by
        rw [← hsplit, hb0, zero_add]
        exact hsmall_rep
      obtain ⟨k, hk⟩ : ∃ k, small.card = k + 1 :=
        ⟨small.card - 1, by
          have := hr
          rw [hp, Multiset.card_replicate] at this
          omega⟩
      rw [hk] at hp
      rw [hp]
      simp [hook, Multiset.replicate_succ]
      omega
    · obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp h1
      have hx2 : 2 ≤ x := by
        have : x ∈ big := by rw [hx]; exact Multiset.mem_singleton_self x
        exact (Multiset.mem_filter.mp this).2
      have hp : p = x ::ₘ replicate small.card 1 := by
        rw [← hsplit, hx, Multiset.singleton_add, ← hsmall_rep]
      rw [hp]
      simp [hook]
      omega

/-- **系（一意な最大点）**：`d ≥ 1` で、正整数の型 `p` が最も偏った型
`(N-r+1, 1^(r-1))`（`N = ∑p`, `r = |p| ≥ 1`）と異なれば、`Φ_d(p)` はその型の値より真に小さい。 -/
theorem phi_lt_hook {d : ℕ} (hd : 1 ≤ d) :
    ∀ {p : Multiset ℕ}, (∀ m ∈ p, 0 < m) → 1 ≤ p.card → p ≠ hook p.sum p.card →
      phi d p < phi d (hook p.sum p.card) := by
  intro p
  induction hμ : p.sum ^ 2 - powerSum p 2 using Nat.strong_induction_on generalizing p with
  | _ μ ih =>
    intro hpos hr hne
    obtain ⟨q, hq⟩ := exists_transfer_of_ne_hook hpos hr hne
    have hsum := transfer_sum hq
    have hcard := transfer_card hq
    have hlt := phi_lt_of_transfer hd hq
    by_cases hqh : q = hook q.sum q.card
    · rw [hsum, hcard, ← hqh]
      exact hlt
    · have hμq : q.sum ^ 2 - powerSum q 2 < μ := by
        have h1 := powerSum_two_lt_of_transfer hq
        have h2 := powerSum_two_le_sq_sum q
        rw [← hμ, hsum]
        omega
      have := ih _ hμq rfl (transfer_pos hq hpos) (hcard ▸ hr) hqh
      rw [hsum, hcard]
      exact hlt.trans this

/-- 総量 `N`・塊数 `r` を明示した形の一意最大性。 -/
theorem phi_lt_hook_of_sum_card {d N r : ℕ} (hd : 1 ≤ d) {p : Multiset ℕ}
    (hpos : ∀ m ∈ p, 0 < m) (hsum : p.sum = N) (hcard : p.card = r) (hr : 1 ≤ r)
    (hne : p ≠ hook N r) : phi d p < phi d (hook N r) := by
  subst hsum hcard
  exact phi_lt_hook hd hpos hr hne

/-- 系の非狭義版：正整数の型の中で最も偏った型が `Φ_d` を最大にする（`d` は任意）。 -/
theorem phi_le_hook (d : ℕ) {p : Multiset ℕ} (hpos : ∀ m ∈ p, 0 < m) (hr : 1 ≤ p.card) :
    phi d p ≤ phi d (hook p.sum p.card) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  by_cases h : p = hook p.sum p.card
  · exact le_of_eq (congrArg (phi d) h)
  · exact (phi_lt_hook hd hpos hr h).le

/-! ## 会話資料の数値例と、塊数を固定する条件の必要性 -/

/-- `N = 7, d = 2` の固定 `r = 2` のチェイン（会話資料第3節）。 -/
theorem seven_two_chain :
    phi 2 {4, 3} = 5175625 ∧ phi 2 {5, 2} = 20133169 ∧ phi 2 {6, 1} = 241926916 := by
  decide

example : phi 2 {4, 3} < phi 2 {5, 2} := phi_lt_cons (by norm_num) (by norm_num) (by norm_num) {}

/-- 塊数が変わる合流では増加が起こり得る：`Φ_2(4,1,1,1) < Φ_2(5,1,1)`。 -/
theorem merge_can_increase :
    phi 2 {4, 1, 1, 1} = 18386944 ∧ phi 2 {5, 1, 1} = 31843449 ∧
      phi 2 {4, 1, 1, 1} < phi 2 {5, 1, 1} := by
  decide

/-- 一方で合流チェインの端点では減少する：`Φ_2(1^7) > Φ_2(7)`。したがって
合流チェインに沿った値は単調増加でも単調減少でもない。 -/
theorem merge_chain_endpoints_decrease :
    phi 2 (replicate 7 1) = 678223072849 ∧ phi 2 {7} = 13841287201 ∧
      phi 2 {7} < phi 2 (replicate 7 1) := by
  decide

end F0ImbalanceMonotonicity

#print axioms F0ImbalanceMonotonicity.phi_lt_of_transfer
#print axioms F0ImbalanceMonotonicity.phi_lt_of_transGen
#print axioms F0ImbalanceMonotonicity.phi_lt_hook
#print axioms F0ImbalanceMonotonicity.phi_le_hook
#print axioms F0ImbalanceMonotonicity.phi_map_univ
