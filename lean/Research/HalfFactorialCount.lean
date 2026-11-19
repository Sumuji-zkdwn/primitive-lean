import Mathlib.Tactic

/-!
# `⟨4, 6, 9⟩` の全既約分解の個数

`docs/verification/2026-11-03-half-factorial-probe.md` の「数学的な全分解数（Lean未形式化）」で、
乗法モノイド `G = ⟨4, 6, 9⟩ ⊆ ℕ` の元 `n` について `a = v₂(n)`, `b = v₃(n)` とおくと
全既約分解の個数は `⌊min(a, b)/2⌋ + 1` だと手計算で述べ、その閉形式を直接与える
Lean 宣言はないとしていた。ここでそれを証明する。

* 生成子の出現回数 `(r, s, t)` で `4^r 6^s 9^t = n` となる組の個数
  （`card_counts_eq`）。
* 4・6・9 だけからなる多重集合で積が `n` になるものの個数（`card_factorizations_eq`）。
  `4, 6, 9` が `G` の既約元のすべてであることは既存の
  `AtomicGeneratorClassification.inc` の `atom_iff_three_generators` にあり、
  このモジュールでは「4・6・9 の多重集合」として数える。

どちらも `⌊min(a, b)/2⌋ + 1`。資料の例 `36, 216, 1296, 46656` の 2, 2, 3, 4 通りも確認する。
-/

namespace HalfFactorialCount

/-! ## 指数の連立方程式の解の個数 -/

/-- `2r + s = a`, `s + 2t = b` の自然数解 `(r, s, t)`。 -/
def Sol (a b : ℕ) := {c : ℕ × ℕ × ℕ // 2 * c.1 + c.2.1 = a ∧ c.2.1 + 2 * c.2.2 = b}

/-- 偶奇が等しければ、解は `s = min a b - 2k`（`0 ≤ k ≤ min a b / 2`）で一対一に並ぶ。 -/
def solEquiv (a b : ℕ) (h : a % 2 = b % 2) : Sol a b ≃ Fin (min a b / 2 + 1) where
  toFun c := ⟨(min a b - c.1.2.1) / 2, by have := c.2; omega⟩
  invFun k := ⟨((a - (min a b - 2 * k.1)) / 2, min a b - 2 * k.1, (b - (min a b - 2 * k.1)) / 2),
    by have := k.2; simp only; constructor <;> omega⟩
  left_inv c := by
    obtain ⟨⟨r, s, t⟩, h1, h2⟩ := c
    simp only at h1 h2
    apply Subtype.ext
    simp only [Prod.mk.injEq]
    refine ⟨by omega, by omega, by omega⟩
  right_inv k := by
    apply Fin.ext
    simp only
    have := k.2
    omega

theorem sol_empty (a b : ℕ) (h : a % 2 ≠ b % 2) : IsEmpty (Sol a b) :=
  ⟨fun c => h (by have := c.2; omega)⟩

theorem card_sol (a b : ℕ) :
    Nat.card (Sol a b) = if a % 2 = b % 2 then min a b / 2 + 1 else 0 := by
  split_ifs with h
  · rw [Nat.card_congr (solEquiv a b h), Nat.card_eq_fintype_card, Fintype.card_fin]
  · have := sol_empty a b h
    exact Nat.card_of_isEmpty

/-! ## 生成子の出現回数と積 -/

/-- 生成子の出現回数 `(r, s, t)` の積 `4^r 6^s 9^t`。 -/
def value (c : ℕ × ℕ × ℕ) : ℕ := 4 ^ c.1 * 6 ^ c.2.1 * 9 ^ c.2.2

theorem value_eq_pow (c : ℕ × ℕ × ℕ) :
    value c = 2 ^ (2 * c.1 + c.2.1) * 3 ^ (c.2.1 + 2 * c.2.2) := by
  simp only [value, pow_add, pow_mul]
  rw [show (6 : ℕ) = 2 * 3 by norm_num, mul_pow]
  norm_num
  ring

theorem two_three_pow_inj {a b a' b' : ℕ} (h : 2 ^ a * 3 ^ b = 2 ^ a' * 3 ^ b') :
    a = a' ∧ b = b' := by
  have h2 := congrArg (fun n => n.factorization 2) h
  have h3 := congrArg (fun n => n.factorization 3) h
  simp only [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ three_ne_zero),
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.prime_two.factorization_self, Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)] at h2 h3
  omega

/-- 積が等しい ⇔ 2 と 3 の指数が等しい。 -/
theorem value_eq_iff (c c' : ℕ × ℕ × ℕ) :
    value c = value c' ↔
      2 * c.1 + c.2.1 = 2 * c'.1 + c'.2.1 ∧ c.2.1 + 2 * c.2.2 = c'.2.1 + 2 * c'.2.2 := by
  rw [value_eq_pow, value_eq_pow]
  constructor
  · exact two_three_pow_inj
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-- **分解数（生成子の計数）**：`n = 4^r₀ 6^s₀ 9^t₀`、`a = 2r₀ + s₀ = v₂(n)`、
`b = s₀ + 2t₀ = v₃(n)` なら、`4^r 6^s 9^t = n` となる `(r, s, t)` は `⌊min(a,b)/2⌋ + 1` 個。 -/
theorem card_counts_eq (c₀ : ℕ × ℕ × ℕ) :
    Nat.card {c : ℕ × ℕ × ℕ // value c = value c₀} =
      min (2 * c₀.1 + c₀.2.1) (c₀.2.1 + 2 * c₀.2.2) / 2 + 1 := by
  have e : {c : ℕ × ℕ × ℕ // value c = value c₀} ≃
      Sol (2 * c₀.1 + c₀.2.1) (c₀.2.1 + 2 * c₀.2.2) :=
    Equiv.subtypeEquivRight fun c => value_eq_iff c c₀
  rw [Nat.card_congr e, card_sol]
  split_ifs with h
  · rfl
  · omega

/-- 2 と 3 の指数は `Nat.factorization` で読める。 -/
theorem factorization_value (c : ℕ × ℕ × ℕ) :
    (value c).factorization 2 = 2 * c.1 + c.2.1 ∧
      (value c).factorization 3 = c.2.1 + 2 * c.2.2 := by
  rw [value_eq_pow]
  simp only [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ three_ne_zero),
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.prime_two.factorization_self, Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
  omega

/-- `v₂, v₃` で書いた形：`n ∈ G` の分解数は `⌊min(v₂ n, v₃ n)/2⌋ + 1`。 -/
theorem card_counts_eq_factorization (c₀ : ℕ × ℕ × ℕ) :
    Nat.card {c : ℕ × ℕ × ℕ // value c = value c₀} =
      min ((value c₀).factorization 2) ((value c₀).factorization 3) / 2 + 1 := by
  rw [card_counts_eq, (factorization_value c₀).1, (factorization_value c₀).2]

/-! ## 4・6・9 の多重集合としての分解 -/

/-- 4・6・9 だけからなり、積が `n` の多重集合。 -/
def Factorization (n : ℕ) :=
  {w : Multiset ℕ // (∀ x ∈ w, x = 4 ∨ x = 6 ∨ x = 9) ∧ w.prod = n}

/-- 出現回数の組から多重集合を作る。 -/
def toMultiset (c : ℕ × ℕ × ℕ) : Multiset ℕ :=
  Multiset.replicate c.1 4 + Multiset.replicate c.2.1 6 + Multiset.replicate c.2.2 9

theorem toMultiset_prod (c : ℕ × ℕ × ℕ) : (toMultiset c).prod = value c := by
  simp [toMultiset, value, Multiset.prod_replicate]

theorem toMultiset_mem (c : ℕ × ℕ × ℕ) : ∀ x ∈ toMultiset c, x = 4 ∨ x = 6 ∨ x = 9 := by
  intro x hx
  simp only [toMultiset, Multiset.mem_add, Multiset.mem_replicate] at hx
  rcases hx with (⟨-, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩ <;> simp

theorem eq_toMultiset {w : Multiset ℕ} (hw : ∀ x ∈ w, x = 4 ∨ x = 6 ∨ x = 9) :
    w = toMultiset (w.count 4, w.count 6, w.count 9) := by
  ext x
  simp only [toMultiset, Multiset.count_add, Multiset.count_replicate]
  by_cases h4 : x = 4
  · subst h4; simp
  by_cases h6 : x = 6
  · subst h6; simp
  by_cases h9 : x = 9
  · subst h9; simp
  rw [Multiset.count_eq_zero.mpr fun hx => by rcases hw x hx with h | h | h <;> contradiction]
  simp [Ne.symm h4, Ne.symm h6, Ne.symm h9]

def factorizationEquiv (n : ℕ) : Factorization n ≃ {c : ℕ × ℕ × ℕ // value c = n} where
  toFun w := ⟨(w.1.count 4, w.1.count 6, w.1.count 9), by
    rw [← toMultiset_prod, ← eq_toMultiset w.2.1, w.2.2]⟩
  invFun c := ⟨toMultiset c.1, toMultiset_mem c.1, (toMultiset_prod c.1).trans c.2⟩
  left_inv w := Subtype.ext (eq_toMultiset w.2.1).symm
  right_inv c := by
    obtain ⟨⟨r, s, t⟩, hc⟩ := c
    apply Subtype.ext
    simp [toMultiset, Multiset.count_replicate]

/-- **分解数（多重集合）**：`n ∈ G` を 4・6・9 の積に分ける方法は `⌊min(v₂ n, v₃ n)/2⌋ + 1` 通り。 -/
theorem card_factorizations_eq (c₀ : ℕ × ℕ × ℕ) :
    Nat.card (Factorization (value c₀)) =
      min ((value c₀).factorization 2) ((value c₀).factorization 3) / 2 + 1 := by
  rw [Nat.card_congr (factorizationEquiv _), card_counts_eq_factorization]

/-- 半階乗性：同じ積の分解は同じ長さ `(v₂ n + v₃ n)/2` を持つ。 -/
theorem length_eq (c c' : ℕ × ℕ × ℕ) (h : value c = value c') :
    c.1 + c.2.1 + c.2.2 = c'.1 + c'.2.1 + c'.2.2 := by
  have := (value_eq_iff c c').mp h
  omega

/-! ## 資料の例 -/

theorem example_counts :
    Nat.card (Factorization 36) = 2 ∧ Nat.card (Factorization 216) = 2 ∧
      Nat.card (Factorization 1296) = 3 ∧ Nat.card (Factorization 46656) = 4 := by
  have h36 : (36 : ℕ) = value (0, 2, 0) := by decide
  have h216 : (216 : ℕ) = value (0, 3, 0) := by decide
  have h1296 : (1296 : ℕ) = value (0, 4, 0) := by decide
  have h46656 : (46656 : ℕ) = value (0, 6, 0) := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h36, Nat.card_congr (factorizationEquiv _), card_counts_eq]
    rfl
  · rw [h216, Nat.card_congr (factorizationEquiv _), card_counts_eq]
    rfl
  · rw [h1296, Nat.card_congr (factorizationEquiv _), card_counts_eq]
    rfl
  · rw [h46656, Nat.card_congr (factorizationEquiv _), card_counts_eq]
    rfl

end HalfFactorialCount

#print axioms HalfFactorialCount.card_counts_eq
#print axioms HalfFactorialCount.card_factorizations_eq
#print axioms HalfFactorialCount.example_counts
