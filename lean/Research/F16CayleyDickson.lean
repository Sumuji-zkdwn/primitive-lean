import Mathlib.Tactic

/-!
# F16：符号表 `epsTable` は Cayley–Dickson 倍化から生成される

`docs/verification/2026-11-01-f16-rank-certificate.md` は「Cayley–Dickson 再帰による
`epsTable` の生成の Lean 内検証」を未証明として挙げていた。`F16Holonomy.inc` の
`epsTable`（基底の積 `e_a e_b = eps a b · e_(a xor b)` の符号）を、倍化

  `(a, b)(c, d) = (a c - d̄ b, d a + b c̄)`

から再帰的に定まる符号 `cdSign k i j`（`2^k` 次元、`conjSign j = if j = 0 then 1 else -1`）と
比較し、`k = 4` で全256成分が一致することを示す（`eps_eq_cdSign`）。
あわせて、すべての次数 `k` について

* `e_0` は両側単位元：`cdSign k 0 j = cdSign k j 0 = 1`（`cdSign_zero`）、
* 虚単位の平方は `-1`：`0 < i` なら `cdSign k i i = -1`（`cdSign_self`）、
* 異なる虚単位は反可換：`cdSign k i j = - cdSign k j i`（`cdSign_anticomm`）、
* 次数を上げても下位の符号は変わらない（`cdSign_succ_low`）

を帰納法で証明する。`epsTable` と `eps` の本文は `F16Holonomy.inc` から変更せずに写した。
両者のバイト列が一致することは `tests/test_f16_cayley_dickson.py` が確認するが、
joint 検査の宣言との同一視を Lean の定理として与えるものではない。
-/

namespace F16CayleyDickson

def epsTable : Array (Array ℤ) := #[
  #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  #[1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1],
  #[1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1],
  #[1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1],
  #[1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1],
  #[1, 1, -1, 1, -1, -1, -1, 1, 1, -1, 1, -1, 1, -1, 1, -1],
  #[1, 1, 1, -1, -1, 1, -1, -1, 1, -1, -1, 1, 1, -1, -1, 1],
  #[1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1],
  #[1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1],
  #[1, 1, -1, 1, -1, 1, 1, -1, -1, -1, -1, 1, -1, 1, 1, -1],
  #[1, 1, 1, -1, -1, -1, 1, 1, -1, 1, -1, -1, -1, -1, 1, 1],
  #[1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, -1, -1, 1, -1, 1],
  #[1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, -1],
  #[1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, -1],
  #[1, -1, -1, 1, 1, -1, 1, 1, -1, -1, -1, 1, 1, -1, -1, 1],
  #[1, 1, -1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1]
]

def eps (a b : Fin 16) : ℤ := (epsTable[a.val]!)[b.val]!

/-! ## Cayley–Dickson の符号 -/

/-- 共役の符号：実単位 `e_0` は `1`、虚単位は `-1`。 -/
def conjSign (j : ℕ) : ℤ := if j = 0 then 1 else -1

/-- `2^k` 次元 Cayley–Dickson 代数の基底の積の符号。 -/
def cdSign : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 1
  | k + 1, i, j =>
    if i < 2 ^ k then
      (if j < 2 ^ k then cdSign k i j else cdSign k (j - 2 ^ k) i)
    else
      (if j < 2 ^ k then conjSign j * cdSign k (i - 2 ^ k) j
       else -(conjSign (j - 2 ^ k)) * cdSign k (j - 2 ^ k) (i - 2 ^ k))

/-- **表の一致**：`F16Holonomy.inc` の符号表は 16 次元 Cayley–Dickson 代数（十六元数）の符号。 -/
theorem eps_eq_cdSign : ∀ a b : Fin 16, eps a b = cdSign 4 a b := by
  decide

/-- 次数を上げても下位の基底どうしの符号は変わらない。 -/
theorem cdSign_succ_low (k i j : ℕ) (hi : i < 2 ^ k) (hj : j < 2 ^ k) :
    cdSign (k + 1) i j = cdSign k i j := by
  simp [cdSign, hi, hj]

/-- `e_0` は両側単位元。 -/
theorem cdSign_zero : ∀ (k j : ℕ), j < 2 ^ k → cdSign k 0 j = 1 ∧ cdSign k j 0 = 1 := by
  intro k
  induction k with
  | zero => intro j _; simp [cdSign]
  | succ k ih =>
    intro j hj
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    rw [pow_succ] at hj
    by_cases hjk : j < 2 ^ k
    · simp [cdSign, hpos, hjk, (ih j hjk).1, (ih j hjk).2]
    · have hj' : j - 2 ^ k < 2 ^ k := by omega
      simp [cdSign, hpos, hjk, (ih _ hj').2, conjSign]

/-- 虚単位の平方は `-1`。 -/
theorem cdSign_self : ∀ (k i : ℕ), 0 < i → i < 2 ^ k → cdSign k i i = -1 := by
  intro k
  induction k with
  | zero => intro i hi hik; simp at hik; omega
  | succ k ih =>
    intro i hi hik
    rw [pow_succ] at hik
    by_cases hlow : i < 2 ^ k
    · simp [cdSign, hlow, ih i hi hlow]
    · have hi' : i - 2 ^ k < 2 ^ k := by omega
      simp only [cdSign, hlow, ↓reduceIte]
      by_cases h0 : i - 2 ^ k = 0
      · rw [h0, (cdSign_zero k 0 (Nat.two_pow_pos k)).1]
        simp [conjSign]
      · rw [ih _ (by omega) hi']
        simp [conjSign, h0]

/-- 異なる虚単位は反可換。 -/
theorem cdSign_anticomm : ∀ (k i j : ℕ), 0 < i → 0 < j → i ≠ j → i < 2 ^ k → j < 2 ^ k →
    cdSign k i j = -cdSign k j i := by
  intro k
  induction k with
  | zero => intro i j hi _ _ hik _; simp at hik; omega
  | succ k ih =>
    intro i j hi hj hij hik hjk
    rw [pow_succ] at hik hjk
    have hz := cdSign_zero k
    by_cases hil : i < 2 ^ k <;> by_cases hjl : j < 2 ^ k
    · simp only [cdSign, hil, hjl, ↓reduceIte]
      exact ih i j hi hj hij hil hjl
    · simp only [cdSign, hil, hjl, ↓reduceIte]
      simp [conjSign, Nat.pos_iff_ne_zero.mp hi]
    · simp only [cdSign, hil, hjl, ↓reduceIte]
      simp [conjSign, Nat.pos_iff_ne_zero.mp hj]
    · simp only [cdSign, hil, hjl, ↓reduceIte]
      have ha : i - 2 ^ k < 2 ^ k := by omega
      have hb : j - 2 ^ k < 2 ^ k := by omega
      by_cases ha0 : i - 2 ^ k = 0
      · have hb0 : j - 2 ^ k ≠ 0 := by omega
        rw [ha0, (hz _ hb).1, (hz _ hb).2]
        simp [conjSign, hb0]
      · by_cases hb0 : j - 2 ^ k = 0
        · rw [hb0, (hz _ ha).1, (hz _ ha).2]
          simp [conjSign, ha0]
        · rw [ih (j - 2 ^ k) (i - 2 ^ k) (by omega) (by omega) (by omega) hb ha]
          simp [conjSign, ha0, hb0]

/-! ## 表への帰結 -/

theorem fin16_lt (a : Fin 16) : (a : ℕ) < 2 ^ 4 := by
  rw [show (2 : ℕ) ^ 4 = 16 by norm_num]; exact a.isLt

theorem fin16_pos {a : Fin 16} (ha : a ≠ 0) : 0 < (a : ℕ) :=
  Nat.pos_of_ne_zero fun h => ha (Fin.ext h)

theorem eps_zero_left (b : Fin 16) : eps 0 b = 1 := by
  rw [eps_eq_cdSign]
  exact (cdSign_zero 4 b (fin16_lt b)).1

theorem eps_zero_right (a : Fin 16) : eps a 0 = 1 := by
  rw [eps_eq_cdSign]
  exact (cdSign_zero 4 a (fin16_lt a)).2

theorem eps_self (a : Fin 16) (ha : a ≠ 0) : eps a a = -1 := by
  rw [eps_eq_cdSign]
  exact cdSign_self 4 a (fin16_pos ha) (fin16_lt a)

theorem eps_anticomm (a b : Fin 16) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    eps a b = -eps b a := by
  rw [eps_eq_cdSign, eps_eq_cdSign]
  exact cdSign_anticomm 4 a b (fin16_pos ha) (fin16_pos hb) (Fin.val_ne_iff.mpr hab)
    (fin16_lt a) (fin16_lt b)

/-- 下位 8 成分は 8 次元（八元数）の Cayley–Dickson 符号。 -/
theorem eps_low_octonion (a b : Fin 16) (ha : (a : ℕ) < 8) (hb : (b : ℕ) < 8) :
    eps a b = cdSign 3 a b := by
  rw [eps_eq_cdSign]
  exact cdSign_succ_low 3 a b (by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact ha)
    (by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact hb)

end F16CayleyDickson

#print axioms F16CayleyDickson.eps_eq_cdSign
#print axioms F16CayleyDickson.cdSign_self
#print axioms F16CayleyDickson.cdSign_anticomm
#print axioms F16CayleyDickson.eps_anticomm
