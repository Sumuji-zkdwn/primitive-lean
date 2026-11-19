import Mathlib.Tactic

/-!
# F0：条件 B を外しても区別は必ずしも復活しない

F0 の会話資料（`sources/f0_math_chat_2026-10-29/03_conjecture_and_cautions.md` 第5節）は
「B を外すと区別不能性が壊れる」を「壊れる例が存在する」という意味に限定し、
`r = 1` や `K` が単射の場合には区別が起こらないことを注意している。ERG-Aout R005 では
この注意が `cand.f0.drop_b_not_always` として未束縛のまま残っていた。

ここでは冪等な `K` を固定し、`F0Retractions.inc` と同じ定義

* `liftK K v = fun i => K (v i)`（`K^(d)`）
* `Compatible K S : ∀ x i, S (K x) i = K (S x i)`（条件 B）

を用いて、次を完全に分類する（出力成分の添字型 `I` は空でないとする）。

1. 条件 B を破る `S` が存在する ⇔ `K ≠ id`（`exists_incompatible_iff`）。
2. B を破るのに区別を復活させない `S` が存在する ⇔ `K ≠ id`
   （`exists_incompatible_respecting_iff`）。
3. 区別を復活させる `S` が存在する ⇔ `K` が単射でなく、かつ固定点が2個以上
   （`exists_separating_iff`）。

したがって「B の不成立 ⇒ 区別の復活」は、`K = id`（B が破れようがない）を除く
**すべての** 冪等 `K` で偽である（`drop_b_not_always`）。

有限の場合は個数も求める。塊の大きさを `m_a = |K⁻¹(a)|`、`d = |I|` とすると

* 区別を復活させない `S`：`∏_a (∑_b m_b^{m_a})^d`（`respects_count`）
* 条件 B を満たす `S`：`∏_a (∑_b m_b^{m_a-1})^d`（`compatible_count`）
* B を破るが区別を復活させない `S`：その差（`incompatible_respecting_count_eq`）。
  これが正であることと `K ≠ id` は同値（`incompatible_respecting_count_pos_iff`）。

この独立モジュールは定義を `F0Retractions.inc` から写して持つ。両者の定義本文は同じだが、
joint 検査の宣言とこのモジュールの宣言を一つの Lean 環境で同一視する定理は含まない。
-/

namespace F0DropCompatibility

/-! ## 定義（`F0Retractions.inc` と同じ本文） -/

def Idempotent {α : Type*} (K : α → α) : Prop := ∀ x, K (K x) = K x

def liftK {α I : Type*} (K : α → α) (v : I → α) : I → α := fun i => K (v i)

/-- 条件 B：`S ∘ K = K^(d) ∘ S`。 -/
def Compatible {α I : Type*} (K : α → α) (S : α → I → α) : Prop :=
  ∀ x i, S (K x) i = K (S x i)

/-- `K` が潰した区別を `K^(d) ∘ S` が復活させない。 -/
def Respects {α I : Type*} (K : α → α) (S : α → I → α) : Prop :=
  ∀ x y, K x = K y → liftK K (S x) = liftK K (S y)

/-- `K` で同じ値になる二点を `K^(d) ∘ S` が区別する。 -/
def Separates {α I : Type*} (K : α → α) (S : α → I → α) : Prop :=
  ∃ x y, K x = K y ∧ liftK K (S x) ≠ liftK K (S y)

theorem not_respects_iff {α I : Type*} (K : α → α) (S : α → I → α) :
    ¬ Respects K S ↔ Separates K S := by
  simp [Respects, Separates]

/-! ## B は区別不能性を保証する（既知の方向） -/

theorem compatible_respects {α I : Type*} {K : α → α} {S : α → I → α}
    (h : Compatible K S) : Respects K S := by
  intro x y hxy
  funext i
  simp only [liftK]
  rw [← h x i, ← h y i, hxy]

/-- 区別不能性の保存は、`K^(d) ∘ S` が `K` を通って因数分解されることと同値。 -/
theorem respects_iff_factor {α I : Type*} {K : α → α} (hK : Idempotent K)
    (S : α → I → α) :
    Respects K S ↔ ∀ x, liftK K (S (K x)) = liftK K (S x) := by
  constructor
  · intro h x
    exact h (K x) x (hK x)
  · intro h x y hxy
    rw [← h x, ← h y, hxy]

/-! ## `K = id` のとき：B は破れない -/

theorem compatible_of_eq_id {α I : Type*} {K : α → α} (hid : ∀ x, K x = x)
    (S : α → I → α) : Compatible K S := by
  intro x i
  rw [hid x, hid (S x i)]

/-- 単射な冪等写像は恒等写像。 -/
theorem eq_id_of_injective {α : Type*} {K : α → α} (hK : Idempotent K)
    (hinj : Function.Injective K) (x : α) : K x = x :=
  hinj (hK x)

theorem compatible_of_injective {α I : Type*} {K : α → α} (hK : Idempotent K)
    (hinj : Function.Injective K) (S : α → I → α) : Compatible K S :=
  compatible_of_eq_id (eq_id_of_injective hK hinj) S

/-- 単射な `K` では、どの `S` も区別を復活させない（そもそも潰された点がない）。 -/
theorem respects_of_injective {α I : Type*} {K : α → α}
    (hinj : Function.Injective K) (S : α → I → α) : Respects K S := by
  intro x y hxy
  rw [hinj hxy]

/-- 固定点が高々1個（`r ≤ 1`）なら、どの `S` も区別を復活させない。 -/
theorem respects_of_fixed_subsingleton {α I : Type*} {K : α → α} (hK : Idempotent K)
    (hr : ∀ a b, K a = a → K b = b → a = b) (S : α → I → α) : Respects K S := by
  intro x y _
  funext i
  exact hr _ _ (hK _) (hK _)

/-! ## `K ≠ id` のとき：B を破るのに区別を復活させない `S` -/

/-- 固定点でない点 `x₀` を一つ選び、`K x₀` の塊の全体を `x₀` へ、それ以外を自分自身へ送る。 -/
noncomputable def witness {α I : Type*} (K : α → α) (x₀ : α) : α → I → α := by
  classical
  exact fun y _ => if K y = K x₀ then x₀ else y

theorem witness_lift {α I : Type*} {K : α → α} (x₀ y : α) :
    liftK K (witness (I := I) K x₀ y) = fun _ => K y := by
  classical
  funext i
  simp only [liftK, witness]
  split_ifs with h
  · exact h.symm
  · rfl

theorem witness_respects {α I : Type*} {K : α → α} (x₀ : α) :
    Respects K (witness (I := I) K x₀) := by
  intro x y hxy
  rw [witness_lift, witness_lift, hxy]

theorem witness_not_compatible {α I : Type*} [Nonempty I] {K : α → α}
    (hK : Idempotent K) {x₀ : α} (hx₀ : K x₀ ≠ x₀) :
    ¬ Compatible K (witness (I := I) K x₀) := by
  classical
  intro h
  obtain ⟨i⟩ := ‹Nonempty I›
  have := h x₀ i
  simp [witness, hK x₀] at this
  exact hx₀ this.symm

/-! ## 分類定理 -/

/-- **分類1**：条件 B を破る `S` が存在する ⇔ `K` は恒等写像でない。 -/
theorem exists_incompatible_iff {α I : Type*} [Nonempty I] {K : α → α}
    (hK : Idempotent K) :
    (∃ S : α → I → α, ¬ Compatible K S) ↔ ∃ x, K x ≠ x := by
  constructor
  · rintro ⟨S, hS⟩
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hS (compatible_of_eq_id hall S)
  · rintro ⟨x₀, hx₀⟩
    exact ⟨_, witness_not_compatible hK hx₀⟩

/-- **分類2**：B を破るのに区別を復活させない `S` が存在する ⇔ `K` は恒等写像でない。 -/
theorem exists_incompatible_respecting_iff {α I : Type*} [Nonempty I] {K : α → α}
    (hK : Idempotent K) :
    (∃ S : α → I → α, ¬ Compatible K S ∧ Respects K S) ↔ ∃ x, K x ≠ x := by
  constructor
  · rintro ⟨S, hS, -⟩
    exact (exists_incompatible_iff hK).mp ⟨S, hS⟩
  · rintro ⟨x₀, hx₀⟩
    exact ⟨_, witness_not_compatible hK hx₀, witness_respects x₀⟩

/-- **分類3**：区別を復活させる `S` が存在する ⇔ `K` は単射でなく、固定点が2個以上ある。 -/
theorem exists_separating_iff {α I : Type*} [Nonempty I] {K : α → α}
    (hK : Idempotent K) :
    (∃ S : α → I → α, Separates K S) ↔
      ¬ Function.Injective K ∧ ∃ a b, K a = a ∧ K b = b ∧ a ≠ b := by
  classical
  constructor
  · rintro ⟨S, x, y, hxy, hne⟩
    refine ⟨fun hinj => hne (by rw [hinj hxy]), ?_⟩
    obtain ⟨i, hi⟩ : ∃ i, K (S x i) ≠ K (S y i) := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      exact hne (funext hall)
    exact ⟨K (S x i), K (S y i), hK _, hK _, hi⟩
  · rintro ⟨hninj, a, b, ha, hb, hab⟩
    obtain ⟨x, y, hxy, hne⟩ : ∃ x y, K x = K y ∧ x ≠ y := by
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      exact hninj fun x y h => hall x y h
    refine ⟨fun z _ => if z = x then a else b, x, y, hxy, ?_⟩
    intro h
    obtain ⟨i⟩ := ‹Nonempty I›
    have := congrFun h i
    simp [liftK, Ne.symm hne, ha, hb] at this
    exact hab this

/-- **系**：`K = id` でない冪等 `K` では必ず、B を破りながら区別を復活させない `S` がある。
したがって「B の不成立 ⇒ 区別の復活」という推論は、B が破れうるどの `K` でも成り立たない。 -/
theorem drop_b_not_always {α I : Type*} [Nonempty I] {K : α → α} (hK : Idempotent K) :
    (∃ S : α → I → α, ¬ Compatible K S) →
      ∃ S : α → I → α, ¬ Compatible K S ∧ ¬ Separates K S := by
  intro h
  obtain ⟨S, hS, hR⟩ :=
    (exists_incompatible_respecting_iff (I := I) hK).mpr
      ((exists_incompatible_iff (I := I) hK).mp h)
  exact ⟨S, hS, fun hsep => (not_respects_iff K S).mpr hsep hR⟩

/-! ## 計数（有限の場合） -/

abbrev Fixed {α : Type*} (K : α → α) := {a : α // K a = a}

abbrev Fiber {α : Type*} (K : α → α) (a : Fixed K) := {x : α // K x = a.val}

/-- `α ≃ Σ a ∈ Fix K, K⁻¹(a)`。 -/
def fiberEquiv {α : Type*} {K : α → α} (hK : Idempotent K) : α ≃ Σ a : Fixed K, Fiber K a where
  toFun x := ⟨⟨K x, hK x⟩, ⟨x, rfl⟩⟩
  invFun p := p.2.val
  left_inv _ := rfl
  right_inv p := Sigma.subtype_ext (Subtype.ext p.2.2) rfl

/-- 塊ごとに積をまとめる：`∏_x f(K x) = ∏_a f(a)^{m_a}`。 -/
theorem prod_over_fibers {α : Type*} [Fintype α] [DecidableEq α] {K : α → α} (hK : Idempotent K)
    (f : Fixed K → ℕ) :
    ∏ x : α, f ⟨K x, hK x⟩ = ∏ a : Fixed K, f a ^ Fintype.card (Fiber K a) := by
  rw [Fintype.prod_equiv (fiberEquiv hK) (fun x => f ⟨K x, hK x⟩)
    (fun p => f p.1) (fun x => rfl), Fintype.prod_sigma]
  simp

/-- 一成分の、区別を復活させない写像。 -/
def RespectMap {α : Type*} (K : α → α) := {s : α → α // ∀ x, K (s (K x)) = K (s x)}

def respectSigma {α : Type*} {K : α → α} (hK : Idempotent K) :
    RespectMap K ≃ Σ g : Fixed K → Fixed K, {s : α → α // ∀ x, K (s x) = (g ⟨K x, hK x⟩).val} where
  toFun s := ⟨fun a => ⟨K (s.1 a.1), hK _⟩, ⟨s.1, fun x => (s.2 x).symm⟩⟩
  invFun p := ⟨p.2.1, fun x => by
    rw [p.2.2 (K x), p.2.2 x]
    exact congrArg (fun a => (p.1 a).val) (Subtype.ext (hK x))⟩
  left_inv _ := rfl
  right_inv p := by
    refine Sigma.subtype_ext (funext fun a => Subtype.ext ?_) rfl
    show K (p.2.1 a.1) = (p.1 a).val
    rw [p.2.2 a.1]
    exact congrArg (fun b => (p.1 b).val) (Subtype.ext a.2)

theorem respectMap_card {α : Type*} [Fintype α] [DecidableEq α] {K : α → α} (hK : Idempotent K) :
    Nat.card (RespectMap K) =
      ∏ a : Fixed K, ∑ b : Fixed K, Fintype.card (Fiber K b) ^ Fintype.card (Fiber K a) := by
  classical
  rw [Nat.card_congr (respectSigma hK), Nat.card_eq_fintype_card, Fintype.card_sigma,
    Fintype.prod_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (β := fun _ : α => α)
    (p := fun x y => K y = (g ⟨K x, hK x⟩).val)), Fintype.card_pi]
  exact prod_over_fibers hK (fun a => Fintype.card (Fiber K (g a)))


/-- 一成分の、条件 B を満たす写像（`s ∘ K = K ∘ s`）。 -/
def CompatMap {α : Type*} (K : α → α) := {s : α → α // ∀ x, s (K x) = K (s x)}

def compatSigma {α : Type*} {K : α → α} (hK : Idempotent K) :
    CompatMap K ≃ Σ g : Fixed K → Fixed K, {s : α → α // ∀ x,
      K (s x) = (g ⟨K x, hK x⟩).val ∧ (K x = x → s x = (g ⟨K x, hK x⟩).val)} where
  toFun s := ⟨fun a => ⟨s.1 a.1, by have := s.2 a.1; rw [a.2] at this; exact this.symm⟩,
    ⟨s.1, fun x => ⟨(s.2 x).symm, fun h => congrArg s.1 h.symm⟩⟩⟩
  invFun p := ⟨p.2.1, fun x => by
    rw [(p.2.2 (K x)).2 (hK x), (p.2.2 x).1]
    exact congrArg (fun a => (p.1 a).val) (Subtype.ext (hK x))⟩
  left_inv _ := rfl
  right_inv p := by
    refine Sigma.subtype_ext (funext fun a => Subtype.ext ?_) rfl
    show p.2.1 a.1 = (p.1 a).val
    rw [(p.2.2 a.1).2 a.2]
    exact congrArg (fun b => (p.1 b).val) (Subtype.ext a.2)

theorem prod_fiber_ite {α : Type*} [Fintype α] [DecidableEq α] {K : α → α} (a : Fixed K)
    (c : ℕ) :
    ∏ y : Fiber K a, (if K y.1 = y.1 then 1 else c) = c ^ (Fintype.card (Fiber K a) - 1) := by
  have key : ∀ y : Fiber K a, (K y.1 = y.1 ↔ y = ⟨a.1, a.2⟩) := fun y =>
    ⟨fun h => Subtype.ext (by rw [← h, y.2]), fun h => by rw [h]; exact a.2⟩
  simp_rw [key]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

theorem prod_over_fibers_ite {α : Type*} [Fintype α] [DecidableEq α] {K : α → α}
    (hK : Idempotent K) (f : Fixed K → ℕ) :
    ∏ x : α, (if K x = x then 1 else f ⟨K x, hK x⟩) =
      ∏ a : Fixed K, f a ^ (Fintype.card (Fiber K a) - 1) := by
  rw [Fintype.prod_equiv (fiberEquiv hK) (fun x => if K x = x then 1 else f ⟨K x, hK x⟩)
    (fun p => if K p.2.1 = p.2.1 then 1 else f p.1) (fun x => rfl), Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun a _ => prod_fiber_ite a (f a)

theorem compatMap_card {α : Type*} [Fintype α] [DecidableEq α] {K : α → α} (hK : Idempotent K) :
    Nat.card (CompatMap K) =
      ∏ a : Fixed K, ∑ b : Fixed K, Fintype.card (Fiber K b) ^ (Fintype.card (Fiber K a) - 1) := by
  classical
  rw [Nat.card_congr (compatSigma hK), Nat.card_eq_fintype_card, Fintype.card_sigma,
    Fintype.prod_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (β := fun _ : α => α)
    (p := fun x y => K y = (g ⟨K x, hK x⟩).val ∧ (K x = x → y = (g ⟨K x, hK x⟩).val))),
    Fintype.card_pi]
  rw [← prod_over_fibers_ite hK (fun a => Fintype.card (Fiber K (g a)))]
  refine Finset.prod_congr rfl fun x _ => ?_
  split_ifs with h
  · rw [Fintype.card_congr (Equiv.subtypeEquivRight (q := fun y => y = (g ⟨K x, hK x⟩).val)
      (fun y => ⟨fun hy => hy.2 h, fun hy => ⟨by rw [hy]; exact (g _).2, fun _ => hy⟩⟩)),
      Fintype.card_subtype_eq]
  · exact Fintype.card_congr (Equiv.subtypeEquivRight
      (fun y => ⟨fun hy => hy.1, fun hy => ⟨hy, fun h' => absurd h' h⟩⟩))

/-- 成分ごとに分ける：`{S // Respects K S} ≃ (I → RespectMap K)`。 -/
def respectsEquiv {α I : Type*} {K : α → α} (hK : Idempotent K) :
    {S : α → I → α // Respects K S} ≃ (I → RespectMap K) where
  toFun S i := ⟨fun x => S.1 x i, fun x => congrFun ((respects_iff_factor hK S.1).mp S.2 x) i⟩
  invFun c := ⟨fun x i => (c i).1 x, (respects_iff_factor hK _).mpr fun x =>
    funext fun i => (c i).2 x⟩
  left_inv _ := rfl
  right_inv _ := rfl

def compatibleEquiv {α I : Type*} (K : α → α) :
    {S : α → I → α // Compatible K S} ≃ (I → CompatMap K) where
  toFun S i := ⟨fun x => S.1 x i, fun x => S.2 x i⟩
  invFun c := ⟨fun x i => (c i).1 x, fun x i => (c i).2 x⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **計数1**：区別を復活させない `S` の個数 `∏_a (∑_b m_b^{m_a})^{|I|}`。 -/
theorem respects_count {α I : Type*} [Fintype α] [DecidableEq α] [Fintype I] {K : α → α}
    (hK : Idempotent K) :
    Nat.card {S : α → I → α // Respects K S} =
      ∏ a : Fixed K, (∑ b : Fixed K,
        Fintype.card (Fiber K b) ^ Fintype.card (Fiber K a)) ^ Fintype.card I := by
  rw [Nat.card_congr (respectsEquiv hK), Nat.card_fun, respectMap_card hK,
    Nat.card_eq_fintype_card, Finset.prod_pow]

/-- **計数2**：条件 B を満たす `S` の個数 `∏_a (∑_b m_b^{m_a-1})^{|I|}`
（`F0Retractions.inc` の `compatible_split_count` と同じ式を、このモジュール内で独立に示す）。 -/
theorem compatible_count {α I : Type*} [Fintype α] [DecidableEq α] [Fintype I] {K : α → α}
    (hK : Idempotent K) :
    Nat.card {S : α → I → α // Compatible K S} =
      ∏ a : Fixed K, (∑ b : Fixed K,
        Fintype.card (Fiber K b) ^ (Fintype.card (Fiber K a) - 1)) ^ Fintype.card I := by
  rw [Nat.card_congr (compatibleEquiv K), Nat.card_fun, compatMap_card hK,
    Nat.card_eq_fintype_card, Finset.prod_pow]

/-- **計数3**：B を破るが区別を復活させない `S` の個数は、二つの積の差。 -/
theorem incompatible_respecting_count {α I : Type*} [Fintype α] [Fintype I]
    (K : α → α) :
    Nat.card {S : α → I → α // ¬ Compatible K S ∧ Respects K S} =
      Nat.card {S : α → I → α // Respects K S} - Nat.card {S : α → I → α // Compatible K S} := by
  classical
  have hsplit : Nat.card {S : α → I → α // Respects K S} =
      Nat.card {S : α → I → α // ¬ Compatible K S ∧ Respects K S} +
        Nat.card {S : α → I → α // Compatible K S} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [← Finset.card_filter_add_card_filter_not (p := fun S => Compatible K S)]
    rw [add_comm]
    congr 2
    · ext S; simp [and_comm]
    · ext S; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨compatible_respects h, h⟩⟩
  omega

/-- **計数3の明示形**：B を破るが区別を復活させない `S` の個数
`∏_a (∑_b m_b^{m_a})^{|I|} - ∏_a (∑_b m_b^{m_a-1})^{|I|}`。 -/
theorem incompatible_respecting_count_eq {α I : Type*} [Fintype α] [DecidableEq α] [Fintype I]
    {K : α → α} (hK : Idempotent K) :
    Nat.card {S : α → I → α // ¬ Compatible K S ∧ Respects K S} =
      ∏ a : Fixed K, (∑ b : Fixed K,
          Fintype.card (Fiber K b) ^ Fintype.card (Fiber K a)) ^ Fintype.card I -
        ∏ a : Fixed K, (∑ b : Fixed K,
          Fintype.card (Fiber K b) ^ (Fintype.card (Fiber K a) - 1)) ^ Fintype.card I := by
  rw [incompatible_respecting_count K, respects_count hK, compatible_count hK]

/-- その個数が正であることと `K ≠ id` は同値（`d = |I| ≥ 1`）。 -/
theorem incompatible_respecting_count_pos_iff {α I : Type*} [Fintype α] [Fintype I]
    [Nonempty I] {K : α → α} (hK : Idempotent K) :
    0 < Nat.card {S : α → I → α // ¬ Compatible K S ∧ Respects K S} ↔ ∃ x, K x ≠ x := by
  rw [Nat.card_pos_iff, ← exists_incompatible_respecting_iff (I := I) hK]
  constructor
  · rintro ⟨⟨S, hS⟩, -⟩
    exact ⟨S, hS⟩
  · rintro ⟨S, hS⟩
    exact ⟨⟨⟨S, hS⟩⟩, inferInstance⟩

/-! ## 会話資料の例 `𝓑 = {0,1,2}`, `K = (0,0,2)` との対照 -/

def exampleK (x : Fin 3) : Fin 3 := if x = 2 then 2 else 0

theorem exampleK_idempotent : Idempotent exampleK := by
  unfold Idempotent
  decide

/-- 会話資料の `S = (0,2,0)` は B を破り、区別を復活させる。 -/
def exampleSeparating (x : Fin 3) (_ : Fin 1) : Fin 3 := if x = 1 then 2 else 0

theorem example_separating :
    ¬ Compatible exampleK exampleSeparating ∧ Separates exampleK exampleSeparating := by
  refine ⟨?_, 0, 1, by decide, ?_⟩
  · intro h
    exact absurd (h 1 0) (by decide)
  · intro h
    exact absurd (congrFun h 0) (by decide)

/-- 同じ `K` で、`S = (1,1,2)` は B を破るが区別を復活させない。 -/
def exampleRespecting (x : Fin 3) (_ : Fin 1) : Fin 3 := if x = 2 then 2 else 1

theorem example_respecting :
    ¬ Compatible exampleK exampleRespecting ∧ ¬ Separates exampleK exampleRespecting := by
  refine ⟨?_, ?_⟩
  · intro h
    exact absurd (h 0 0) (by decide)
  · rintro ⟨x, y, hxy, hne⟩
    apply hne
    funext i
    revert x y i
    decide

/-- 一塊（`r = 1`）の `K = (0,0,0)` では、B を破る `S` もどれも区別しない。 -/
def constK (_ : Fin 3) : Fin 3 := 0

theorem constK_never_separates {I : Type*} (S : Fin 3 → I → Fin 3) :
    ¬ Separates constK S := by
  rw [← not_respects_iff, not_not]
  exact respects_of_fixed_subsingleton (by intro x; rfl)
    (by intro a b ha hb; rw [← ha, ← hb]; rfl) S

end F0DropCompatibility

#print axioms F0DropCompatibility.exists_incompatible_iff
#print axioms F0DropCompatibility.exists_incompatible_respecting_iff
#print axioms F0DropCompatibility.exists_separating_iff
#print axioms F0DropCompatibility.drop_b_not_always
#print axioms F0DropCompatibility.respects_count
#print axioms F0DropCompatibility.compatible_count
#print axioms F0DropCompatibility.incompatible_respecting_count_eq
#print axioms F0DropCompatibility.incompatible_respecting_count_pos_iff
