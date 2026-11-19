import Mathlib.Tactic

/-!
# F0：更新 `T = K ∘ C ∘ K^(d) ∘ S` が取りうる写像と、その個数

F0 の会話資料（`sources/f0_math_chat_2026-10-29/03_conjecture_and_cautions.md` 第4・7節）は、
B 適合な `S` の個数が多いことを「異なる `T` の個数」と同一視しないよう注意し、
`(K, S, C)` の同値類や異なる `T` の個数の計数を今後の課題に挙げていた。

冪等な `K`、出力成分の添字型 `I`（空でない）、`F = Fix K`（`r = |F|`）について、
`F0Retractions.inc` と同じ本文の `liftK`・`Compatible`（条件 B）・`Reconstructs`（条件 A）・
`step` を使い、`T = step K S C` が取りうる写像の集合を完全に決定する。

* 条件なし（`range_free`）：値が `F` に入る写像すべて。有限なら `r^N` 個（`card_free`）。
* 条件 B（`range_compatible`）：値が `F` に入り `T ∘ K = T` となる写像すべて。
  `F → F` の写像と一対一で、`r^r` 個（`card_compatible`）。
* 条件 A と B（`range_reconstructs_compatible`）：`T = K` ただ一つ。

例えば 7 点で型 `(4,3)`、`d = 2` なら B 適合な `S` は 5,175,625 個あるが、B のもとで
異なる `T` は `2^2 = 4` 個しかない（`example_seven_points`）。
条件 A だけの場合の `T` の集合は今回扱わない。
-/

namespace F0StepRange

/-! ## 定義（`F0Retractions.inc` と同じ本文） -/

def Idempotent {α : Type*} (K : α → α) : Prop := ∀ x, K (K x) = K x

def liftK {α I : Type*} (K : α → α) (v : I → α) : I → α := fun i => K (v i)

def Compatible {α I : Type*} (K : α → α) (S : α → I → α) : Prop :=
  ∀ x i, S (K x) i = K (S x i)

def Reconstructs {α I : Type*} (S : α → I → α) (C : (I → α) → α) : Prop :=
  ∀ x, C (S x) = x

def step {α I : Type*} (K : α → α) (S : α → I → α) (C : (I → α) → α) (x : α) : α :=
  K (C (liftK K (S x)))

variable {α I : Type*} {K : α → α}

/-! ## 取りうる `T` の集合 -/

/-- **条件なし**：`T` は値が `Fix K` に入る写像ちょうどすべて。 -/
theorem range_free [Nonempty I] (hK : Idempotent K) (T : α → α) :
    (∃ S : α → I → α, ∃ C : (I → α) → α, T = step K S C) ↔ ∀ x, K (T x) = T x := by
  constructor
  · rintro ⟨S, C, rfl⟩ x
    exact hK _
  · intro hT
    obtain ⟨i₀⟩ := ‹Nonempty I›
    refine ⟨fun x _ => T x, fun v => v i₀, ?_⟩
    funext x
    simp [step, liftK, hT x]

/-- **条件 B**：`T` は値が `Fix K` に入り、`K` の塊の上で一定な写像ちょうどすべて。 -/
theorem range_compatible [Nonempty I] (hK : Idempotent K) (T : α → α) :
    (∃ S : α → I → α, ∃ C : (I → α) → α, Compatible K S ∧ T = step K S C) ↔
      (∀ x, K (T x) = T x) ∧ ∀ x, T (K x) = T x := by
  constructor
  · rintro ⟨S, C, hS, rfl⟩
    refine ⟨fun x => hK _, fun x => ?_⟩
    have : liftK K (S (K x)) = liftK K (S x) := by
      funext i
      simp only [liftK]
      rw [hS x i, hK]
    simp only [step, this]
  · rintro ⟨hT, hTK⟩
    obtain ⟨i₀⟩ := ‹Nonempty I›
    refine ⟨fun x _ => K x, fun v => T (v i₀), fun x i => by simp [hK x], ?_⟩
    funext x
    simp only [step, liftK, hK x]
    rw [hTK, hT]

/-- **条件 A と B**：`T = K` ただ一つ（対角写像 `S` と射影 `C` が A・B を満たす）。 -/
theorem range_reconstructs_compatible [Nonempty I] (hK : Idempotent K) (T : α → α) :
    (∃ S : α → I → α, ∃ C : (I → α) → α,
        Compatible K S ∧ Reconstructs S C ∧ T = step K S C) ↔ T = K := by
  constructor
  · rintro ⟨S, C, hS, hA, rfl⟩
    funext x
    have : liftK K (S x) = S (K x) := by
      funext i
      simp only [liftK]
      rw [hS x i]
    simp only [step, this]
    rw [hA (K x), hK x]
  · rintro rfl
    obtain ⟨i₀⟩ := ‹Nonempty I›
    refine ⟨fun x _ => x, fun v => v i₀, fun x i => rfl, fun x => rfl, ?_⟩
    funext x
    simp [step, liftK, hK x]

/-! ## 個数 -/

variable [Fintype α] [DecidableEq α]

/-- 値が `Fix K` に入る写像は `α → Fix K` と一対一。 -/
def freeEquiv : {T : α → α // ∀ x, K (T x) = T x} ≃ (α → {a : α // K a = a}) where
  toFun T x := ⟨T.1 x, T.2 x⟩
  invFun t := ⟨fun x => (t x).1, fun x => (t x).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- B のもとで取りうる `T` は `Fix K → Fix K` と一対一。 -/
def compatibleEquiv (hK : Idempotent K) :
    {T : α → α // (∀ x, K (T x) = T x) ∧ ∀ x, T (K x) = T x} ≃
      ({a : α // K a = a} → {a : α // K a = a}) where
  toFun T a := ⟨T.1 a.1, T.2.1 a.1⟩
  invFun t := ⟨fun x => (t ⟨K x, hK x⟩).1, fun x => (t ⟨K x, hK x⟩).2,
    fun x => by simp only [hK x]⟩
  left_inv T := by
    apply Subtype.ext
    funext x
    exact T.2.2 x
  right_inv t := by
    funext a
    apply Subtype.ext
    simp only
    congr 2
    exact Subtype.ext a.2

/-- **条件なしの個数** `r^N`。 -/
theorem card_free [Nonempty I] (hK : Idempotent K) :
    Nat.card {T : α → α // ∃ S : α → I → α, ∃ C : (I → α) → α, T = step K S C} =
      Fintype.card {a : α // K a = a} ^ Fintype.card α := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun T => range_free (I := I) hK T),
    Nat.card_congr freeEquiv, Nat.card_eq_fintype_card, Fintype.card_fun]

/-- **条件 B のもとでの個数** `r^r`。 -/
theorem card_compatible [Nonempty I] (hK : Idempotent K) :
    Nat.card {T : α → α // ∃ S : α → I → α, ∃ C : (I → α) → α,
        Compatible K S ∧ T = step K S C} =
      Fintype.card {a : α // K a = a} ^ Fintype.card {a : α // K a = a} := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun T => range_compatible (I := I) hK T),
    Nat.card_congr (compatibleEquiv hK), Nat.card_eq_fintype_card, Fintype.card_fun]

omit [Fintype α] [DecidableEq α] in
/-- **条件 A と B のもとでの個数** 1。 -/
theorem card_reconstructs_compatible [Nonempty I] (hK : Idempotent K) :
    Nat.card {T : α → α // ∃ S : α → I → α, ∃ C : (I → α) → α,
        Compatible K S ∧ Reconstructs S C ∧ T = step K S C} = 1 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun T =>
    range_reconstructs_compatible (I := I) hK T)]
  simp

/-! ## 例：7 点、型 `(4,3)` -/

/-- 7 点で塊 `{0,1,2,3}` と `{4,5,6}`、代表点 `0` と `4`。 -/
def K43 (x : Fin 7) : Fin 7 := if x.val < 4 then 0 else 4

theorem K43_idempotent : Idempotent K43 := by
  unfold Idempotent
  decide

theorem K43_fixed : Fintype.card {a : Fin 7 // K43 a = a} = 2 := by
  decide

/-- 型 `(4,3)`、`d = 2`：条件なしで `2^7 = 128` 個、B のもとで `2^2 = 4` 個、A と B のもとで 1 個。 -/
theorem example_seven_points :
    Nat.card {T : Fin 7 → Fin 7 // ∃ S : Fin 7 → Fin 2 → Fin 7, ∃ C : (Fin 2 → Fin 7) → Fin 7,
        T = step K43 S C} = 128 ∧
    Nat.card {T : Fin 7 → Fin 7 // ∃ S : Fin 7 → Fin 2 → Fin 7, ∃ C : (Fin 2 → Fin 7) → Fin 7,
        Compatible K43 S ∧ T = step K43 S C} = 4 ∧
    Nat.card {T : Fin 7 → Fin 7 // ∃ S : Fin 7 → Fin 2 → Fin 7, ∃ C : (Fin 2 → Fin 7) → Fin 7,
        Compatible K43 S ∧ Reconstructs S C ∧ T = step K43 S C} = 1 := by
  refine ⟨?_, ?_, card_reconstructs_compatible K43_idempotent⟩
  · rw [card_free K43_idempotent, K43_fixed]
    rfl
  · rw [card_compatible K43_idempotent, K43_fixed]
    rfl

end F0StepRange

#print axioms F0StepRange.range_free
#print axioms F0StepRange.range_compatible
#print axioms F0StepRange.range_reconstructs_compatible
#print axioms F0StepRange.card_compatible
#print axioms F0StepRange.example_seven_points
