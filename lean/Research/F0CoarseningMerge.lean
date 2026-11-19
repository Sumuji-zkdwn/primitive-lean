import Mathlib.Tactic

/-!
# F0：冪等写像の粗化は塊サイズ型の合流チェインをちょうど実現する

F0 の会話資料（`sources/f0_math_chat_2026-10-29/03_conjecture_and_cautions.md` 第6・7節）は、
二塊合流グラフを整数分割の構造として定義し、「個別の写像の合成が型の合流を実現する」
という実現定理は証明されていないとして、「元の写像の合成と、型の合流・細分化の対応条件」
を今後の課題に挙げていた。ここでその対応を与える。

有限集合 `α` 上の冪等写像 `K` の塊サイズ型を、固定点 `a` ごとの塊 `K⁻¹(a)` の大きさの
多重集合 `type K` とする。`K'` が `K` の粗化であるとは `K' ∘ K = K'`
（`K` で同じ値の点は `K'` でも同じ値）のこと（`Coarsens K K'`）。`Merge`・`Chain` は
`F0MergeChains.inc` と同じ本文で定義する。

* **粗化 ⇒ 合流チェイン**（`coarsening_chain`）：冪等な `K'` が `K` の粗化なら、
  `Chain (r - r') (type K) (type K')`（`r, r'` は固定点の個数）。
* **合流の実現**（`merge_realized`）：`type K` の任意の二塊合流は、`K` の二つの塊を一つにまとめる
  冪等な粗化 `K₁` によって実現される。
* **対応**（`chain_iff_coarsening`）：`type K` から長さ `n` の合流チェインで `q` へ行ける ⇔
  固定点が `n` 個少ない冪等な粗化 `K'` で `type K' = q` となるものがある。

塊のラベル（どの点をまとめたか）は型からは失われる。細分化（逆向き）は扱わない。
-/

namespace F0CoarseningMerge

open Finset

/-! ## 定義 -/

def Idempotent {α : Type*} (K : α → α) : Prop := ∀ x, K (K x) = K x

/-- 二塊合流（`F0MergeChains.inc` と同じ本文）。 -/
def Merge (p q : Multiset ℕ) : Prop :=
  ∃ a b : ℕ, ∃ rest : Multiset ℕ,
    0 < a ∧ 0 < b ∧ p = a ::ₘ b ::ₘ rest ∧ q = (a + b) ::ₘ rest

/-- 長さ `n` の合流チェイン（`F0MergeChains.inc` と同じ本文）。 -/
def Chain : ℕ → Multiset ℕ → Multiset ℕ → Prop
  | 0, p, q => p = q
  | n + 1, p, q => ∃ r, Merge p r ∧ Chain n r q

/-- `K'` は `K` の粗化：`K' ∘ K = K'`。 -/
def Coarsens {α : Type*} (K K' : α → α) : Prop := ∀ x, K' (K x) = K' x

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- 固定点（代表点）の集合。 -/
def fixSet (K : α → α) : Finset α := univ.filter fun a => K a = a

/-- 塊 `K⁻¹(a)`。 -/
def fiber (K : α → α) (a : α) : Finset α := univ.filter fun x => K x = a

/-- 塊サイズ型。 -/
def type (K : α → α) : Multiset ℕ := (fixSet K).val.map fun a => (fiber K a).card

omit [Fintype α] [DecidableEq α] in
theorem coarsens_refl (K : α → α) (hK : Idempotent K) : Coarsens K K := hK

omit [Fintype α] [DecidableEq α] in
theorem coarsens_trans {K K₁ K₂ : α → α} (h₁ : Coarsens K K₁) (h₂ : Coarsens K₁ K₂) :
    Coarsens K K₂ := by
  intro x
  rw [← h₂ (K x), h₁ x, h₂ x]

omit [Fintype α] [DecidableEq α] in
/-- 粗化は「`K` で同じ値なら `K'` でも同じ値」と同値。 -/
theorem coarsens_iff_ker {K K' : α → α} (hK : Idempotent K) :
    Coarsens K K' ↔ ∀ x y, K x = K y → K' x = K' y := by
  constructor
  · intro h x y hxy
    rw [← h x, ← h y, hxy]
  · intro h x
    exact h _ _ (hK x)

theorem mem_fixSet {K : α → α} {a : α} : a ∈ fixSet K ↔ K a = a := by simp [fixSet]

theorem mem_fiber {K : α → α} {a x : α} : x ∈ fiber K a ↔ K x = a := by simp [fiber]

theorem fiber_card_pos {K : α → α} {a : α} (ha : K a = a) : 0 < (fiber K a).card :=
  Finset.card_pos.mpr ⟨a, mem_fiber.mpr ha⟩

/-- 型を一つの固定点で分ける。 -/
theorem type_split {K : α → α} {a : α} (ha : a ∈ fixSet K) :
    type K = (fiber K a).card ::ₘ ((fixSet K).erase a).val.map fun b => (fiber K b).card := by
  unfold type
  conv_lhs => rw [← Finset.insert_erase ha]
  rw [Finset.insert_val_of_notMem (Finset.notMem_erase a _), Multiset.map_cons]

/-! ## 二つの塊をまとめる -/

/-- 塊 `K⁻¹(a₂)` を `a₁` の塊へまとめる。 -/
def mergeFibers (K : α → α) (a₁ a₂ : α) : α → α := fun x => if K x = a₂ then a₁ else K x

variable {K : α → α} {a₁ a₂ : α}

omit [Fintype α] in
theorem mergeFibers_idempotent (hK : Idempotent K) (h₁ : K a₁ = a₁) (hne : a₁ ≠ a₂) :
    Idempotent (mergeFibers K a₁ a₂) := by
  intro x
  unfold mergeFibers
  by_cases hx : K x = a₂
  · simp [hx, h₁, hne]
  · simp [hx, hK x]

omit [Fintype α] in
theorem mergeFibers_coarsens (hK : Idempotent K) : Coarsens K (mergeFibers K a₁ a₂) := by
  intro x
  simp [mergeFibers, hK x]

omit [Fintype α] in
/-- 粗化先 `K'` で `a₁, a₂` が同じ値なら、まとめた写像からも `K'` へ粗化する。 -/
theorem mergeFibers_coarsens_to {K' : α → α} (hKK' : Coarsens K K') (h : K' a₁ = K' a₂) :
    Coarsens (mergeFibers K a₁ a₂) K' := by
  intro x
  unfold mergeFibers
  by_cases hx : K x = a₂
  · simp only [hx, ↓reduceIte]
    rw [h, ← hx, hKK' x]
  · simp only [hx, ↓reduceIte]
    rw [hKK' x]

theorem fixSet_mergeFibers (h₁ : K a₁ = a₁) (h₂ : K a₂ = a₂) (hne : a₁ ≠ a₂) :
    fixSet (mergeFibers K a₁ a₂) = (fixSet K).erase a₂ := by
  ext a
  simp only [mem_fixSet, Finset.mem_erase, mergeFibers]
  by_cases ha : K a = a₂
  · simp only [ha, ↓reduceIte]
    constructor
    · rintro rfl
      exact absurd (h₁ ▸ ha) hne
    · rintro ⟨hne', rfl⟩
      exact absurd h₂ (by rw [ha]; exact fun h => hne' h.symm)
  · simp only [ha, ↓reduceIte]
    constructor
    · intro hfix
      exact ⟨fun h => ha (h ▸ hfix), hfix⟩
    · exact fun h => h.2

theorem fiber_mergeFibers_self (hne : a₁ ≠ a₂) :
    (fiber (mergeFibers K a₁ a₂) a₁).card = (fiber K a₁).card + (fiber K a₂).card := by
  have : fiber (mergeFibers K a₁ a₂) a₁ = fiber K a₁ ∪ fiber K a₂ := by
    ext x
    simp only [mem_fiber, Finset.mem_union, mergeFibers]
    by_cases hx : K x = a₂ <;> simp [hx, Ne.symm hne]
  rw [this, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro x h1 h2
  rw [mem_fiber] at h1 h2
  exact hne (h1.symm.trans h2)

theorem fiber_mergeFibers_other {b : α} (hb₁ : b ≠ a₁) (hb₂ : b ≠ a₂) :
    fiber (mergeFibers K a₁ a₂) b = fiber K b := by
  ext x
  simp only [mem_fiber, mergeFibers]
  by_cases hx : K x = a₂
  · simp only [hx, ↓reduceIte]
    exact ⟨fun h => absurd h.symm hb₁, fun h => absurd h.symm hb₂⟩
  · simp [hx]

/-- まとめた写像の型は、二つの塊の大きさを足し合わせた二塊合流。 -/
theorem type_mergeFibers (h₁ : K a₁ = a₁) (h₂ : K a₂ = a₂) (hne : a₁ ≠ a₂) :
    let rest := (((fixSet K).erase a₁).erase a₂).val.map fun b => (fiber K b).card
    type K = (fiber K a₁).card ::ₘ (fiber K a₂).card ::ₘ rest ∧
      type (mergeFibers K a₁ a₂) = ((fiber K a₁).card + (fiber K a₂).card) ::ₘ rest := by
  intro rest
  have ha₁ : a₁ ∈ fixSet K := mem_fixSet.mpr h₁
  have ha₂ : a₂ ∈ (fixSet K).erase a₁ := Finset.mem_erase.mpr ⟨Ne.symm hne, mem_fixSet.mpr h₂⟩
  constructor
  · rw [type_split ha₁]
    congr 1
    conv_lhs => rw [← Finset.insert_erase ha₂]
    rw [Finset.insert_val_of_notMem (Finset.notMem_erase a₂ _), Multiset.map_cons]
  · have hfix := fixSet_mergeFibers h₁ h₂ hne
    have ha₁' : a₁ ∈ fixSet (mergeFibers K a₁ a₂) := by
      rw [hfix]; exact Finset.mem_erase.mpr ⟨hne, ha₁⟩
    rw [type_split ha₁', fiber_mergeFibers_self hne, hfix, Finset.erase_right_comm]
    congr 1
    apply Multiset.map_congr rfl
    intro b hb
    have hb' := Finset.mem_val.mp hb
    simp only [Finset.mem_erase] at hb'
    rw [fiber_mergeFibers_other hb'.2.1 hb'.1]

/-! ## 合流の実現 -/

/-- **合流の実現**：`type K` の二塊合流は、二つの塊をまとめる冪等な粗化で実現される。 -/
theorem merge_realized (hK : Idempotent K) {q : Multiset ℕ} (h : Merge (type K) q) :
    ∃ K₁ : α → α, Idempotent K₁ ∧ Coarsens K K₁ ∧ type K₁ = q ∧
      (fixSet K₁).card + 1 = (fixSet K).card := by
  obtain ⟨a, b, rest, -, -, hp, rfl⟩ := h
  -- 大きさ `a` の塊の代表点 `a₁`
  have ha : a ∈ type K := by rw [hp]; simp
  obtain ⟨c₁, hc₁, hsize₁⟩ := Multiset.mem_map.mp ha
  have hc₁' : c₁ ∈ fixSet K := Finset.mem_val.mp hc₁
  have hsplit₁ := type_split hc₁'
  rw [hp, hsize₁] at hsplit₁
  have hrest₁ := (Multiset.cons_inj_right _).mp hsplit₁
  -- 大きさ `b` の塊の代表点 `a₂ ≠ a₁`
  have hb : b ∈ ((fixSet K).erase c₁).val.map fun x => (fiber K x).card := by
    rw [← hrest₁]; simp
  obtain ⟨c₂, hc₂, hsize₂⟩ := Multiset.mem_map.mp hb
  have hc₂' := Finset.mem_erase.mp (Finset.mem_val.mp hc₂)
  have hne : c₁ ≠ c₂ := Ne.symm hc₂'.1
  have h₁ : K c₁ = c₁ := mem_fixSet.mp hc₁'
  have h₂ : K c₂ = c₂ := mem_fixSet.mp hc₂'.2
  obtain ⟨hTK, hTK₁⟩ := type_mergeFibers h₁ h₂ hne
  refine ⟨mergeFibers K c₁ c₂, mergeFibers_idempotent hK h₁ hne, mergeFibers_coarsens hK, ?_, ?_⟩
  · rw [hTK₁, hsize₁, hsize₂]
    congr 1
    rw [hp, hsize₁, hsize₂] at hTK
    exact (Multiset.cons_inj_right _).mp ((Multiset.cons_inj_right _).mp hTK).symm
  · rw [fixSet_mergeFibers h₁ h₂ hne, Finset.card_erase_add_one (mem_fixSet.mpr h₂)]

/-! ## 粗化 ⇒ 合流チェイン -/

/-- 固定点の数が等しい粗化では型は変わらない。 -/
theorem type_eq_of_coarsens_card {K' : α → α} (hK : Idempotent K) (hK' : Idempotent K')
    (hKK' : Coarsens K K') (hcard : (fixSet K).card = (fixSet K').card) :
    type K = type K' := by
  -- φ : Fix K → Fix K', a ↦ K' a は全射
  have hmaps : ∀ a ∈ fixSet K, K' a ∈ fixSet K' := fun a _ => mem_fixSet.mpr (hK' a)
  have hsurj : ∀ b ∈ fixSet K', ∃ a ∈ fixSet K, K' a = b := by
    intro b hb
    exact ⟨K b, mem_fixSet.mpr (hK b), (hKK' b).trans (mem_fixSet.mp hb)⟩
  have hinj : Set.InjOn K' (fixSet K) :=
    Finset.injOn_of_surjOn_of_card_le _ hmaps (fun b hb => by
      obtain ⟨a, ha, hab⟩ := hsurj b hb
      exact ⟨a, ha, hab⟩) hcard.le
  have himage : fixSet K' = (fixSet K).image K' := by
    ext b
    simp only [Finset.mem_image]
    exact ⟨fun hb => hsurj b hb, fun ⟨a, ha, hab⟩ => hab ▸ hmaps a ha⟩
  -- 対応する塊は同じ
  have hfib : ∀ a ∈ fixSet K, fiber K' (K' a) = fiber K a := by
    intro a ha
    ext x
    simp only [mem_fiber]
    constructor
    · intro hx
      have : K' (K x) = K' a := (hKK' x).trans hx
      exact hinj (mem_fixSet.mpr (hK x)) ha this
    · intro hx
      rw [← hKK' x, hx]
  unfold type
  rw [himage, Finset.image_val_of_injOn hinj, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a ha
  simp only [Function.comp_apply]
  rw [hfib a (Finset.mem_val.mp ha)]

/-- **粗化 ⇒ 合流チェイン**：冪等な粗化 `K'` の型には、`K` の型から長さ `r - r'` の合流チェインで
到達する。 -/
theorem coarsening_chain {K' : α → α} (hK' : Idempotent K') :
    ∀ (n : ℕ) (K : α → α), Idempotent K → Coarsens K K' →
      (fixSet K).card = (fixSet K').card + n → Chain n (type K) (type K') := by
  intro n
  induction n with
  | zero =>
    intro K hK hKK' hcard
    exact type_eq_of_coarsens_card hK hK' hKK' hcard
  | succ n ih =>
    intro K hK hKK' hcard
    -- 鳩の巣：K' で同じ値になる二つの代表点
    obtain ⟨c₁, hc₁, c₂, hc₂, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := fixSet K) (t := fixSet K') (by omega) (fun a _ => mem_fixSet.mpr (hK' a))
    have h₁ : K c₁ = c₁ := mem_fixSet.mp hc₁
    have h₂ : K c₂ = c₂ := mem_fixSet.mp hc₂
    refine ⟨type (mergeFibers K c₁ c₂), ?_, ih _ (mergeFibers_idempotent hK h₁ hne)
      (mergeFibers_coarsens_to hKK' heq) ?_⟩
    · obtain ⟨hTK, hTK₁⟩ := type_mergeFibers h₁ h₂ hne
      exact ⟨_, _, _, fiber_card_pos h₁, fiber_card_pos h₂, hTK, hTK₁⟩
    · have := Finset.card_erase_add_one (mem_fixSet.mpr h₂)
      rw [fixSet_mergeFibers h₁ h₂ hne]
      omega

/-- 合流チェインは、固定点がその長さだけ少ない冪等な粗化で実現される。 -/
theorem chain_realized :
    ∀ (n : ℕ) (K : α → α) (q : Multiset ℕ), Idempotent K → Chain n (type K) q →
      ∃ K' : α → α, Idempotent K' ∧ Coarsens K K' ∧ type K' = q ∧
        (fixSet K').card + n = (fixSet K).card := by
  intro n
  induction n with
  | zero =>
    intro K q hK h
    exact ⟨K, hK, coarsens_refl K hK, h, rfl⟩
  | succ n ih =>
    intro K q hK h
    obtain ⟨r, hmerge, hrest⟩ := h
    obtain ⟨K₁, hK₁, hKK₁, hT, hc₁⟩ := merge_realized hK hmerge
    rw [← hT] at hrest
    obtain ⟨K', hK', hK₁K', hT', hc'⟩ := ih K₁ q hK₁ hrest
    exact ⟨K', hK', coarsens_trans hKK₁ hK₁K', hT', by omega⟩

/-- **対応**：`type K` から長さ `n` の合流チェインで `q` へ行ける ⇔ 固定点が `n` 個少ない冪等な
粗化 `K'` で `type K' = q` となるものがある。 -/
theorem chain_iff_coarsening (hK : Idempotent K) (n : ℕ) (q : Multiset ℕ) :
    Chain n (type K) q ↔
      ∃ K' : α → α, Idempotent K' ∧ Coarsens K K' ∧ type K' = q ∧
        (fixSet K').card + n = (fixSet K).card := by
  constructor
  · exact chain_realized n K q hK
  · rintro ⟨K', hK', hKK', rfl, hcard⟩
    exact coarsening_chain hK' n K hK hKK' (by omega)

end F0CoarseningMerge

#print axioms F0CoarseningMerge.merge_realized
#print axioms F0CoarseningMerge.coarsening_chain
#print axioms F0CoarseningMerge.chain_iff_coarsening
