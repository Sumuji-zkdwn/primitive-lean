import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# F0：塊サイズ型ごとの冪等写像の個数（型別階乗公式）

## 第1段：ファイバーの大きさを指定した写像の個数

有限型 `β → ι` の写像 `f` について、`f ∘ σ`（`σ` は `β` の置換）全体は、ファイバーの大きさが
`f` と同じ写像全体に一致し（`exists_perm_comp_eq`）、`f ∘ σ = f` となる `σ` の個数は
mathlib の `DomMulAct.stabilizer_card` により `∏_i |f⁻¹(i)|!`。したがって

  `#{g | ∀ i, |g⁻¹(i)| = |f⁻¹(i)|} · ∏_i |f⁻¹(i)|! = |β|!`（`card_sameFibers_mul`）。

## 第2段：型別階乗公式

`sources/f0_math_chat_2026-10-29` の表は、`N` 点集合上の冪等写像を塊サイズ型ごとに数えた値
（7点で型 `(4,3)` は 420 個など）を有限計算で与え、検証記録は「原資料の型別階乗公式の一般
Lean 証明」を未完としていた。冪等写像 `K₀` の型を `λ`（塊の大きさ `m_a`、値 `k` の重複度 `c_k`）
とすると

  `I(λ) · ∏_a (m_a - 1)! · ∏_k c_k! = N!`（`card_type_mul`）、

すなわち `I(λ) = N! / (∏_a (m_a - 1)! · ∏_k c_k!)`。証明は、固定点では塊の大きさ・それ以外では
0 をとる「プロファイル」を経由する：型が等しい ⇔ プロファイルのファイバー数が等しい
（`type_eq_iff_fin`）、同じファイバー数のプロファイルは置換の共役で移り合う、同じプロファイルの
冪等写像は非固定点から固定点への写像（ファイバー数 `m_a - 1`）と一対一（`profileEquiv`）。
第1段の多項係数を二回使う。7点の型 `(4,3)`・`(3,2,2)` の 420・1260 個は
`seven_points_43`・`seven_points_322` で確かめる。
-/

namespace F0TypeCount

open Equiv Finset

variable {β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

/-- ファイバーの大きさ。 -/
def fiberCard (f : β → ι) (i : ι) : ℕ := Fintype.card {b // f b = i}

omit [DecidableEq β] [Fintype ι] in
/-- 同じファイバーの大きさを持つ写像は置換で移り合う。 -/
theorem exists_perm_comp_eq {f g : β → ι} (h : ∀ i, fiberCard g i = fiberCard f i) :
    ∃ σ : Perm β, f ∘ σ = g := by
  have e : ∀ i, {b // g b = i} ≃ {b // f b = i} := fun i => Fintype.equivOfCardEq (h i)
  let σ : Perm β :=
    ((Equiv.sigmaFiberEquiv g).symm.trans (Equiv.sigmaCongrRight e)).trans
      (Equiv.sigmaFiberEquiv f)
  refine ⟨σ, funext fun b => ?_⟩
  simp only [Function.comp_apply, σ, Equiv.trans_apply, Equiv.sigmaFiberEquiv_apply,
    Equiv.sigmaCongrRight_apply]
  exact (e (g b) ⟨b, rfl⟩).2

omit [DecidableEq β] [Fintype ι] in
theorem fiberCard_comp_perm (f : β → ι) (σ : Perm β) (i : ι) :
    fiberCard (f ∘ σ) i = fiberCard f i :=
  Fintype.card_congr (σ.subtypeEquiv fun _ => Iff.rfl)

/-- **多項係数**：ファイバーの大きさが `f` と同じ写像の個数 × `∏ |f⁻¹(i)|!` = `|β|!`。 -/
theorem card_sameFibers_mul (f : β → ι) :
    Fintype.card {g : β → ι // ∀ i, fiberCard g i = fiberCard f i} *
      ∏ i, (fiberCard f i).factorial = (Fintype.card β).factorial := by
  classical
  -- Perm β ≃ Σ (g in the class), {σ | f ∘ σ = g}
  have hfib : ∀ g : {g : β → ι // ∀ i, fiberCard g i = fiberCard f i},
      Fintype.card {σ : Perm β // f ∘ σ = g.1} = Fintype.card {σ : Perm β // f ∘ σ = f} := by
    intro g
    obtain ⟨τ, hτ⟩ := exists_perm_comp_eq g.2
    -- σ ↦ σ * τ⁻¹ maps {f ∘ σ = g} onto {f ∘ σ = f}
    apply Fintype.card_congr
    refine
      { toFun := fun σ => ⟨σ.1 * τ⁻¹, ?_⟩
        invFun := fun σ => ⟨σ.1 * τ, ?_⟩
        left_inv := fun σ => by simp
        right_inv := fun σ => by simp }
    · funext b
      have h1 := congrFun σ.2 (τ⁻¹ b)
      have h2 := congrFun hτ (τ⁻¹ b)
      simp only [Function.comp_apply] at h1 h2
      simp only [Function.comp_apply, Perm.coe_mul]
      rw [h1, ← h2]
      simp
    · funext b
      have h1 := congrFun σ.2 (τ b)
      have h2 := congrFun hτ b
      simp only [Function.comp_apply] at h1 h2
      simp only [Function.comp_apply, Perm.coe_mul]
      rw [h1, h2]
  have hsplit : Fintype.card (Perm β) =
      ∑ g : {g : β → ι // ∀ i, fiberCard g i = fiberCard f i},
        Fintype.card {σ : Perm β // f ∘ σ = g.1} := by
    rw [← Fintype.card_sigma]
    apply Fintype.card_congr
    exact
      { toFun := fun σ => ⟨⟨f ∘ σ, fun i => fiberCard_comp_perm f σ i⟩, ⟨σ, rfl⟩⟩
        invFun := fun p => p.2.1
        left_inv := fun σ => rfl
        right_inv := fun p => by
          obtain ⟨⟨g, hg⟩, ⟨σ, hσ⟩⟩ := p
          simp only at hσ
          subst hσ
          rfl }
  rw [Fintype.card_perm] at hsplit
  rw [hsplit, Finset.sum_congr rfl fun g _ => hfib g, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]
  congr 1
  simp only [fiberCard]
  convert (DomMulAct.stabilizer_card f).symm

/-! ## 第2段：冪等写像のプロファイル -/

section Idempotents

variable {α : Type*} [Fintype α] [DecidableEq α]

def Idempotent (K : α → α) : Prop := ∀ x, K (K x) = K x

/-- 塊サイズ型：固定点ごとの塊の大きさの多重集合。 -/
def type (K : α → α) : Multiset ℕ :=
  (Finset.univ.filter fun a => K a = a).val.map (fiberCard K)

/-- プロファイル：固定点では塊の大きさ、それ以外では 0。 -/
def profile (K : α → α) (a : α) : ℕ := if K a = a then fiberCard K a else 0

theorem fiberCard_pos {K : α → α} {a : α} (ha : K a = a) : 0 < fiberCard K a :=
  Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩

theorem fiberCard_le (K : α → α) (a : α) : fiberCard K a ≤ Fintype.card α :=
  Fintype.card_subtype_le _

theorem profile_le (K : α → α) (a : α) : profile K a ≤ Fintype.card α := by
  unfold profile; split_ifs
  · exact fiberCard_le K a
  · exact Nat.zero_le _

theorem profile_pos_iff {K : α → α} {a : α} : 0 < profile K a ↔ K a = a := by
  unfold profile
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => fiberCard_pos h⟩
  · exact ⟨fun h' => absurd h' (lt_irrefl 0), fun h' => absurd h' h⟩

/-- 型の各成分の重複度はプロファイルのファイバーの大きさ（成分 `k ≥ 1`）。 -/
theorem count_type {K : α → α} {k : ℕ} (hk : 0 < k) :
    (type K).count k = fiberCard (profile K) k := by
  unfold type
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val, fiberCard, Fintype.card_subtype,
    Finset.filter_filter]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro a _
  unfold profile
  by_cases ha : K a = a
  · simp only [ha, true_and, ↓reduceIte]
    exact eq_comm
  · simp only [ha, false_and, ↓reduceIte, false_iff]
    omega

theorem count_type_zero (K : α → α) : (type K).count 0 = 0 := by
  unfold type
  rw [Multiset.count_eq_zero]
  intro h
  obtain ⟨a, ha, h0⟩ := Multiset.mem_map.mp h
  rw [Finset.mem_val, Finset.mem_filter] at ha
  exact (fiberCard_pos ha.2).ne' h0

/-- 固定されない点の数と型の長さの和は全体の点数。 -/
theorem fiberCard_profile_zero_add (K : α → α) :
    fiberCard (profile K) 0 + Multiset.card (type K) = Fintype.card α := by
  unfold type
  rw [Multiset.card_map, Finset.card_val, fiberCard, Fintype.card_subtype]
  have : (Finset.univ.filter fun a => profile K a = 0) =
      Finset.univ.filter fun a => ¬ K a = a := by
    apply Finset.filter_congr
    intro a _
    have := (profile_pos_iff (K := K) (a := a))
    constructor
    · intro h0 hfix; have := this.mpr hfix; omega
    · intro hn; by_contra h0; exact hn (this.mp (Nat.pos_of_ne_zero h0))
  rw [this, add_comm, Finset.card_filter_add_card_filter_not, Finset.card_univ]

/-- 型が等しい ⇔ プロファイルのファイバーの大きさがすべて等しい。 -/
theorem type_eq_iff (K K' : α → α) :
    type K = type K' ↔ ∀ v, fiberCard (profile K) v = fiberCard (profile K') v := by
  constructor
  · intro h v
    rcases v with _ | v
    · have h1 := fiberCard_profile_zero_add K
      have h2 := fiberCard_profile_zero_add K'
      rw [h] at h1
      omega
    · rw [← count_type (Nat.succ_pos v), ← count_type (Nat.succ_pos v), h]
  · intro h
    ext k
    rcases k with _ | k
    · rw [count_type_zero, count_type_zero]
    · rw [count_type (Nat.succ_pos k), count_type (Nat.succ_pos k), h]

/-! ### 置換による共役 -/

/-- `σ ∘ K ∘ σ⁻¹`。 -/
def conj (σ : Perm α) (K : α → α) : α → α := fun x => σ (K (σ.symm x))

omit [Fintype α] [DecidableEq α] in
theorem conj_idempotent {K : α → α} (hK : Idempotent K) (σ : Perm α) :
    Idempotent (conj σ K) := by
  intro x
  simp [conj, hK (σ.symm x)]

theorem fiberCard_conj (σ : Perm α) (K : α → α) (a : α) :
    fiberCard (conj σ K) a = fiberCard K (σ.symm a) :=
  Fintype.card_congr (σ.symm.subtypeEquiv fun x => by
    simp only [conj]
    exact ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩)

theorem profile_conj (σ : Perm α) (K : α → α) (a : α) :
    profile (conj σ K) a = profile K (σ.symm a) := by
  unfold profile
  have hfix : conj σ K a = a ↔ K (σ.symm a) = σ.symm a := by
    simp only [conj]
    exact (Equiv.eq_symm_apply σ).symm
  by_cases h : K (σ.symm a) = σ.symm a
  · simp only [hfix.mpr h, h, ↓reduceIte, fiberCard_conj]
  · have h' : ¬ conj σ K a = a := fun h' => h (hfix.mp h')
    simp only [h', h, ↓reduceIte]

omit [Fintype α] [DecidableEq α] in
theorem conj_conj_symm (σ : Perm α) (K : α → α) : conj σ (conj σ.symm K) = K := by
  funext x; simp [conj]

omit [Fintype α] [DecidableEq α] in
theorem conj_symm_conj (σ : Perm α) (K : α → α) : conj σ.symm (conj σ K) = K := by
  funext x; simp [conj]

/-! ### プロファイルが同じ冪等写像 ≃ 非固定点から固定点への写像 -/

variable {K₀ : α → α}

/-- 非固定点から固定点への基準写像 `g₀ z = K₀ z`。 -/
def baseMap (hK₀ : Idempotent K₀) : {x // ¬ K₀ x = x} → {a // K₀ a = a} :=
  fun z => ⟨K₀ z.1, hK₀ z.1⟩

/-- 固定点 `a` の塊は、`a` 自身と、`a` に送られる非固定点からなる。 -/
def fiberOptionEquiv (K : α → α) {a : α} (ha : K a = a) :
    {x // K x = a} ≃ Option {z : {x // ¬ K x = x} // K z.1 = a} where
  toFun x := if h : K x.1 = x.1 then none else some ⟨⟨x.1, h⟩, x.2⟩
  invFun o := match o with
    | none => ⟨a, ha⟩
    | some z => ⟨z.1.1, z.2⟩
  left_inv x := by
    by_cases h : K x.1 = x.1
    · simp only [h, ↓reduceDIte]
      apply Subtype.ext
      simp only
      rw [← h, x.2]
    · simp [h]
  right_inv o := by
    cases o with
    | none => simp [ha]
    | some z => simp [z.1.2]

theorem fiberCard_eq_succ (K : α → α) {a : α} (ha : K a = a) :
    fiberCard K a = Fintype.card {z : {x // ¬ K x = x} // K z.1 = a} + 1 := by
  rw [fiberCard, Fintype.card_congr (fiberOptionEquiv K ha), Fintype.card_option]

theorem fiberCard_baseMap (hK₀ : Idempotent K₀) (a : {a // K₀ a = a}) :
    fiberCard (baseMap hK₀) a = fiberCard K₀ a.1 - 1 := by
  rw [fiberCard_eq_succ K₀ a.2, Nat.add_sub_cancel, fiberCard]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun z => by
    simp only [baseMap]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩)

theorem fixed_iff_of_profile {K : α → α} (h : profile K = profile K₀) (x : α) :
    K x = x ↔ K₀ x = x := by
  rw [← profile_pos_iff, ← profile_pos_iff, h]

/-- 非固定点の集合が同じなら、そこから `a` に送られる点の数も同じ。 -/
theorem card_nonfixed_fiber {K : α → α} (hfix : ∀ x, K x = x ↔ K₀ x = x) (a : α) :
    Fintype.card {z : {x // ¬ K₀ x = x} // K z.1 = a} =
      Fintype.card {z : {x // ¬ K x = x} // K z.1 = a} :=
  Fintype.card_congr
    { toFun := fun z => ⟨⟨z.1.1, fun h => z.1.2 ((hfix _).mp h)⟩, z.2⟩
      invFun := fun z => ⟨⟨z.1.1, fun h => z.1.2 ((hfix _).mpr h)⟩, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- 写像 `g` から作る冪等写像：固定点はそのまま、非固定点 `z` は `g z` へ。 -/
def ofMap (g : {x // ¬ K₀ x = x} → {a // K₀ a = a}) (x : α) : α :=
  if h : K₀ x = x then x else (g ⟨x, h⟩).1

omit [Fintype α] in
theorem ofMap_fixed_iff (g : {x // ¬ K₀ x = x} → {a // K₀ a = a}) (x : α) :
    ofMap g x = x ↔ K₀ x = x := by
  unfold ofMap
  by_cases h : K₀ x = x
  · simp [h]
  · simp only [h, ↓reduceDIte, iff_false]
    intro h'
    exact h (h' ▸ (g ⟨x, h⟩).2)

omit [Fintype α] in
theorem ofMap_idempotent (g : {x // ¬ K₀ x = x} → {a // K₀ a = a}) :
    Idempotent (ofMap g) := by
  intro x
  rw [(ofMap_fixed_iff g (ofMap g x)).mpr]
  unfold ofMap
  by_cases h : K₀ x = x
  · simp [h]
  · simp only [h, ↓reduceDIte]
    exact (g ⟨x, h⟩).2

theorem profile_ofMap (hK₀ : Idempotent K₀) (g : {x // ¬ K₀ x = x} → {a // K₀ a = a})
    (hg : ∀ a, fiberCard g a = fiberCard (baseMap hK₀) a) :
    profile (ofMap g) = profile K₀ := by
  funext a
  unfold profile
  by_cases ha : K₀ a = a
  · have ha' : ofMap g a = a := (ofMap_fixed_iff g a).mpr ha
    simp only [ha, ha', ↓reduceIte]
    rw [fiberCard_eq_succ _ ha', ← card_nonfixed_fiber (ofMap_fixed_iff g) a]
    have hcount : Fintype.card {z : {x // ¬ K₀ x = x} // ofMap g z.1 = a} =
        fiberCard g ⟨a, ha⟩ := by
      rw [fiberCard]
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro z
      simp only [ofMap, z.2, ↓reduceDIte]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [hcount, hg, fiberCard_baseMap]
    have := fiberCard_pos ha
    simp only
    omega
  · have ha' : ¬ ofMap g a = a := fun h => ha ((ofMap_fixed_iff g a).mp h)
    simp only [ha, ha', ↓reduceIte]

/-- **同じプロファイルの冪等写像 ≃ ファイバー数が基準と同じ写像（非固定点 → 固定点）**。 -/
def profileEquiv (hK₀ : Idempotent K₀) :
    {K : α → α // Idempotent K ∧ profile K = profile K₀} ≃
      {g : {x // ¬ K₀ x = x} → {a // K₀ a = a} //
        ∀ a, fiberCard g a = fiberCard (baseMap hK₀) a} where
  toFun K := ⟨fun z => ⟨K.1 z.1, (fixed_iff_of_profile K.2.2 _).mp (K.2.1 z.1)⟩, fun a => by
    have hfix := fixed_iff_of_profile K.2.2
    have haK : K.1 a.1 = a.1 := (hfix a.1).mpr a.2
    have hprof := congrFun K.2.2 a.1
    simp only [profile, haK, a.2, ↓reduceIte] at hprof
    rw [fiberCard_baseMap, ← hprof, fiberCard_eq_succ _ haK, Nat.add_sub_cancel,
      ← card_nonfixed_fiber hfix, fiberCard]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun z =>
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩)⟩
  invFun g := ⟨ofMap g.1, ofMap_idempotent g.1, profile_ofMap hK₀ g.1 g.2⟩
  left_inv K := by
    apply Subtype.ext
    funext x
    simp only [ofMap]
    split_ifs with h
    · exact ((fixed_iff_of_profile K.2.2 x).mpr h).symm
    · rfl
  right_inv g := by
    apply Subtype.ext
    funext z
    apply Subtype.ext
    simp [ofMap, z.2]

/-! ### 組み立て -/

/-- プロファイル（値を `Fin (N+1)` に入れたもの）。 -/
def profileFin (K : α → α) (a : α) : Fin (Fintype.card α + 1) :=
  ⟨profile K a, Nat.lt_succ_of_le (profile_le K a)⟩

theorem fiberCard_profileFin (K : α → α) (v : Fin (Fintype.card α + 1)) :
    fiberCard (profileFin K) v = fiberCard (profile K) v.val :=
  Fintype.card_congr (Equiv.subtypeEquivRight fun a => by simp [profileFin, Fin.ext_iff])

theorem fiberCard_profile_large (K : α → α) {v : ℕ} (hv : Fintype.card α < v) :
    fiberCard (profile K) v = 0 :=
  Fintype.card_eq_zero_iff.mpr ⟨fun a => by have := profile_le K a.1; have := a.2; omega⟩

theorem type_eq_iff_fin (K K' : α → α) :
    type K = type K' ↔ ∀ v, fiberCard (profileFin K) v = fiberCard (profileFin K') v := by
  rw [type_eq_iff]
  constructor
  · intro h v
    rw [fiberCard_profileFin, fiberCard_profileFin, h]
  · intro h v
    by_cases hv : v < Fintype.card α + 1
    · have := h ⟨v, hv⟩
      rwa [fiberCard_profileFin, fiberCard_profileFin] at this
    · rw [fiberCard_profile_large K (by omega), fiberCard_profile_large K' (by omega)]

theorem profileFin_conj (σ : Perm α) (K : α → α) :
    profileFin (conj σ K) = profileFin K ∘ σ.symm := by
  funext a
  apply Fin.ext
  simp [profileFin, profile_conj]

theorem profileFin_eq_iff (K K' : α → α) : profileFin K = profileFin K' ↔ profile K = profile K' :=
  ⟨fun h => funext fun a => congrArg Fin.val (congrFun h a),
    fun h => funext fun a => Fin.ext (congrFun h a)⟩

theorem fiberCard_profile_zero (K : α → α) :
    fiberCard (profile K) 0 = Fintype.card {x // ¬ K x = x} :=
  Fintype.card_congr (Equiv.subtypeEquivRight fun a => by
    have := profile_pos_iff (K := K) (a := a)
    constructor
    · intro h0 hfix; have := this.mpr hfix; omega
    · intro hn; by_contra h0; exact hn (this.mp (Nat.pos_of_ne_zero h0)))

/-- `∏_v (プロファイルのファイバー数)! = (非固定点の数)! · ∏_k c_k!`。 -/
theorem prod_profileFin (K : α → α) :
    ∏ v : Fin (Fintype.card α + 1), (fiberCard (profileFin K) v).factorial =
      (Fintype.card {x // ¬ K x = x}).factorial *
        ∏ k ∈ Finset.range (Fintype.card α + 1), ((type K).count k).factorial := by
  rw [Fin.prod_univ_succ, Finset.prod_range_succ', count_type_zero, Nat.factorial_zero,
    mul_one]
  congr 1
  · rw [fiberCard_profileFin, Fin.val_zero, fiberCard_profile_zero]
  · rw [← Fin.prod_univ_eq_prod_range]
    apply Fintype.prod_congr
    intro i
    rw [fiberCard_profileFin, Fin.val_succ, count_type (Nat.succ_pos _)]

/-- **型別階乗公式**：`|α| = N`、冪等写像 `K₀` の型を `λ`、塊の大きさ `m_a`、型の中の値 `k` の
重複度を `c_k` とすると、型が `λ` の冪等写像の個数 `I(λ)` について
`I(λ) · ∏_a (m_a - 1)! · ∏_k c_k! = N!`。すなわち `I(λ) = N! / (∏ (m_a - 1)! ∏ c_k!)`。 -/
theorem card_type_mul (hK₀ : Idempotent K₀) :
    Nat.card {K : α → α // Idempotent K ∧ type K = type K₀} *
        (∏ a : {a // K₀ a = a}, (fiberCard K₀ a.1 - 1).factorial) *
        (∏ k ∈ Finset.range (Fintype.card α + 1), ((type K₀).count k).factorial) =
      (Fintype.card α).factorial := by
  classical
  -- 同じプロファイルの冪等写像の個数
  have hM : Nat.card {K : α → α // Idempotent K ∧ profile K = profile K₀} *
      ∏ a : {a // K₀ a = a}, (fiberCard K₀ a.1 - 1).factorial =
        (Fintype.card {x // ¬ K₀ x = x}).factorial := by
    rw [Nat.card_congr (profileEquiv hK₀), Nat.card_eq_fintype_card,
      ← card_sameFibers_mul (baseMap hK₀)]
    congr 1
    apply Finset.prod_congr rfl
    intro a _
    rw [fiberCard_baseMap]
  -- プロファイルの類の個数
  have hC := card_sameFibers_mul (profileFin K₀)
  rw [prod_profileFin] at hC
  -- 型が同じ冪等写像 ≃ Σ（プロファイルの類）×（そのプロファイルの冪等写像）
  have hdecomp : Nat.card {K : α → α // Idempotent K ∧ type K = type K₀} =
      Nat.card {s : α → Fin (Fintype.card α + 1) //
          ∀ v, fiberCard s v = fiberCard (profileFin K₀) v} *
        Nat.card {K : α → α // Idempotent K ∧ profile K = profile K₀} := by
    let e : {K : α → α // Idempotent K ∧ type K = type K₀} ≃
        Σ s : {s : α → Fin (Fintype.card α + 1) //
            ∀ v, fiberCard s v = fiberCard (profileFin K₀) v},
          {K : α → α // Idempotent K ∧ profileFin K = s.1} :=
      { toFun := fun K => ⟨⟨profileFin K.1, (type_eq_iff_fin _ _).mp K.2.2⟩, ⟨K.1, K.2.1, rfl⟩⟩
        invFun := fun p => ⟨p.2.1, p.2.2.1, (type_eq_iff_fin _ _).mpr (by
          rw [p.2.2.2]; exact p.1.2)⟩
        left_inv := fun K => rfl
        right_inv := fun p => Sigma.subtype_ext (Subtype.ext p.2.2.2) rfl }
    have hfib : ∀ s : {s : α → Fin (Fintype.card α + 1) //
        ∀ v, fiberCard s v = fiberCard (profileFin K₀) v},
        Nat.card {K : α → α // Idempotent K ∧ profileFin K = s.1} =
          Nat.card {K : α → α // Idempotent K ∧ profile K = profile K₀} := by
      intro s
      obtain ⟨σ, hσ⟩ := exists_perm_comp_eq s.2
      apply Nat.card_congr
      exact
        { toFun := fun K => ⟨conj σ K.1, conj_idempotent K.2.1 σ, by
            rw [← profileFin_eq_iff, profileFin_conj, K.2.2, ← hσ]
            funext a
            simp⟩
          invFun := fun K => ⟨conj σ.symm K.1, conj_idempotent K.2.1 σ.symm, by
            rw [profileFin_conj, (profileFin_eq_iff _ _).mpr K.2.2, ← hσ]
            funext a
            simp⟩
          left_inv := fun K => Subtype.ext (conj_symm_conj σ K.1)
          right_inv := fun K => Subtype.ext (conj_conj_symm σ K.1) }
    rw [Nat.card_congr e, Nat.card_sigma]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  have hC' : Nat.card {s : α → Fin (Fintype.card α + 1) //
      ∀ v, fiberCard s v = fiberCard (profileFin K₀) v} *
        ((Fintype.card {x // ¬ K₀ x = x}).factorial *
          ∏ k ∈ Finset.range (Fintype.card α + 1), ((type K₀).count k).factorial) =
      (Fintype.card α).factorial := by
    rw [Nat.card_eq_fintype_card]
    convert hC using 3
  rw [hdecomp]
  set A := Nat.card {s : α → Fin (Fintype.card α + 1) //
    ∀ v, fiberCard s v = fiberCard (profileFin K₀) v}
  set M := Nat.card {K : α → α // Idempotent K ∧ profile K = profile K₀}
  set B := ∏ a : {a // K₀ a = a}, (fiberCard K₀ a.1 - 1).factorial
  set C := ∏ k ∈ Finset.range (Fintype.card α + 1), ((type K₀).count k).factorial
  calc A * M * B * C = A * ((M * B) * C) := by ring
    _ = (Fintype.card α).factorial := by rw [hM]; exact hC'

/-! ### 元資料の表との照合（7点） -/

/-- 型 `(4,3)`：塊 `{0,1,2,3}`（代表 0）と `{4,5,6}`（代表 4）。 -/
def K43 (x : Fin 7) : Fin 7 := if x.val < 4 then 0 else 4

/-- 型 `(3,2,2)`：塊 `{0,1,2}`、`{3,4}`、`{5,6}`。 -/
def K322 (x : Fin 7) : Fin 7 := if x.val < 3 then 0 else if x.val < 5 then 3 else 5

theorem K43_idempotent : Idempotent K43 := by unfold Idempotent; decide

theorem K322_idempotent : Idempotent K322 := by unfold Idempotent; decide

/-- 7点で型 `(4,3)` の冪等写像は 420 個（元資料の表の値）。 -/
theorem seven_points_43 :
    Nat.card {K : Fin 7 → Fin 7 // Idempotent K ∧ type K = type K43} = 420 := by
  have h := card_type_mul K43_idempotent
  have hB : (∏ a : {a // K43 a = a}, (fiberCard K43 a.1 - 1).factorial) = 12 := by decide
  have hC : (∏ k ∈ Finset.range (Fintype.card (Fin 7) + 1),
      ((type K43).count k).factorial) = 1 := by decide
  rw [hB, hC, Fintype.card_fin] at h
  norm_num [Nat.factorial] at h
  omega

/-- 7点で型 `(3,2,2)` の冪等写像は 1260 個（元資料の表の値）。 -/
theorem seven_points_322 :
    Nat.card {K : Fin 7 → Fin 7 // Idempotent K ∧ type K = type K322} = 1260 := by
  have h := card_type_mul K322_idempotent
  have hB : (∏ a : {a // K322 a = a}, (fiberCard K322 a.1 - 1).factorial) = 2 := by decide
  have hC : (∏ k ∈ Finset.range (Fintype.card (Fin 7) + 1),
      ((type K322).count k).factorial) = 2 := by decide
  rw [hB, hC, Fintype.card_fin] at h
  norm_num [Nat.factorial] at h
  omega

theorem type_K43 : type K43 = {4, 3} := by decide

theorem type_K322 : type K322 = {3, 2, 2} := by decide

end Idempotents

end F0TypeCount

#print axioms F0TypeCount.card_sameFibers_mul
#print axioms F0TypeCount.card_type_mul
#print axioms F0TypeCount.seven_points_43
#print axioms F0TypeCount.seven_points_322
