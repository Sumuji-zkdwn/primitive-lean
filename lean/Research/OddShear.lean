import Mathlib

/-!
# Shear conjugates of the order-six rotation (orbit-trace section 6, all `d`)

Section 6 of `docs/research/2026-11-04-orbit-trace-integrals.md` considers
`L(u,v) = (v, v-u)`, `H_d(u,v) = (u + v^d, v)` and `E_d = H_d⁻¹ ∘ L ∘ H_d` and states, for odd
`d ≥ 3`, `det DE_d = 1`, `E_d³ = -id`, `E_d⁶ = id`, and that `Q ∘ H_d` is `E_d`-invariant for
`Q(u,v) = u² - uv + v²`. `lean/OrbitTrace.lean` proves the case `d = 3`. This module treats
every `d`:

* `Ed_explicit`: `E_d(u,v) = (v - (v - u - v^d)^d, v - u - v^d)`;
* `Ed_six`: `E_d⁶ = id` for every `d`;
* `Ed_cube_iff`: `E_d³ = -id` iff `d` is odd (for even `d`, `E_d³(0,1) = (-2,-1)`);
* `Ed_invariant`: `Q ∘ H_d` is invariant for every `d`;
* `Ed_partials`, `Ed_jacobian`: the four partial derivatives exist (`HasDerivAt` along the
  coordinate lines) and their `2 × 2` determinant is `1`.
-/

namespace OddShear

/-- `L(u,v) = (v, v - u)`. -/
def L (z : ℝ × ℝ) : ℝ × ℝ := (z.2, z.2 - z.1)

/-- `H_d(u,v) = (u + v^d, v)`. -/
def H (d : ℕ) (z : ℝ × ℝ) : ℝ × ℝ := (z.1 + z.2 ^ d, z.2)

/-- `H_d⁻¹(u,v) = (u - v^d, v)`. -/
def Hinv (d : ℕ) (z : ℝ × ℝ) : ℝ × ℝ := (z.1 - z.2 ^ d, z.2)

/-- `E_d = H_d⁻¹ ∘ L ∘ H_d`. -/
def Ed (d : ℕ) (z : ℝ × ℝ) : ℝ × ℝ := Hinv d (L (H d z))

/-- `Q(u,v) = u² - uv + v²`. -/
def Q (z : ℝ × ℝ) : ℝ := z.1 ^ 2 - z.1 * z.2 + z.2 ^ 2

theorem Hinv_H (d : ℕ) (z : ℝ × ℝ) : Hinv d (H d z) = z := by
  simp [H, Hinv]

theorem H_Hinv (d : ℕ) (z : ℝ × ℝ) : H d (Hinv d z) = z := by
  simp [H, Hinv]

theorem L_three (z : ℝ × ℝ) : L (L (L z)) = -z := by
  obtain ⟨u, v⟩ := z
  simp only [L, Prod.neg_mk, Prod.mk.injEq]; constructor <;> ring

theorem Ed_explicit (d : ℕ) (u v : ℝ) :
    Ed d (u, v) = (v - (v - u - v ^ d) ^ d, v - u - v ^ d) := by
  simp only [Ed, H, L, Hinv, Prod.mk.injEq]
  constructor <;> ring

theorem Ed_iter (d : ℕ) (n : ℕ) (z : ℝ × ℝ) :
    (Ed d)^[n] z = Hinv d (L^[n] (H d z)) := by
  induction n generalizing z with
  | zero => simp [Hinv_H]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Ed, H_Hinv, Function.iterate_succ_apply']

theorem L_six (z : ℝ × ℝ) : L^[6] z = z := by
  show L (L (L (L (L (L z))))) = z
  rw [L_three, L_three, neg_neg]

/-- **`E_d⁶ = id` for every `d`.** -/
theorem Ed_six (d : ℕ) (z : ℝ × ℝ) : (Ed d)^[6] z = z := by
  rw [Ed_iter, L_six, Hinv_H]

theorem Ed_cube (d : ℕ) (z : ℝ × ℝ) : (Ed d)^[3] z = Hinv d (-(H d z)) := by
  rw [Ed_iter]
  show Hinv d (L (L (L (H d z)))) = _
  rw [L_three]

/-- **`E_d³ = -id` iff `d` is odd.** -/
theorem Ed_cube_iff (d : ℕ) : (∀ z, (Ed d)^[3] z = -z) ↔ Odd d := by
  constructor
  · intro h
    by_contra hd
    have he : Even d := Nat.not_odd_iff_even.mp hd
    have := h (0, 1)
    rw [Ed_cube] at this
    simp only [H, Hinv, Prod.neg_mk, one_pow, zero_add, he.neg_one_pow, Prod.mk.injEq] at this
    norm_num at this
  · intro hd z
    rw [Ed_cube]
    obtain ⟨u, v⟩ := z
    simp only [H, Hinv, Prod.neg_mk, Prod.mk.injEq, neg_pow, hd.neg_one_pow, and_true]
    ring

theorem Q_L (z : ℝ × ℝ) : Q (L z) = Q z := by
  simp only [Q, L]; ring

/-- **`Q ∘ H_d` is invariant under `E_d`** (every `d`). -/
theorem Ed_invariant (d : ℕ) (z : ℝ × ℝ) : Q (H d (Ed d z)) = Q (H d z) := by
  rw [Ed]
  have : H d (Hinv d (L (H d z))) = L (H d z) := by simp [H, Hinv]
  rw [this, Q_L]

/-- `g = v - u - v^d` and its partials. -/
def gfun (d : ℕ) (u v : ℝ) : ℝ := v - u - v ^ d

/-- The four partial derivatives of `E_d = (v - g^d, g)`. -/
theorem Ed_partials (d : ℕ) (u v : ℝ) :
    HasDerivAt (fun s => (Ed d (s, v)).1) (d * gfun d u v ^ (d - 1)) u ∧
    HasDerivAt (fun s => (Ed d (u, s)).1)
      (1 - d * gfun d u v ^ (d - 1) * (1 - d * v ^ (d - 1))) v ∧
    HasDerivAt (fun s => (Ed d (s, v)).2) (-1) u ∧
    HasDerivAt (fun s => (Ed d (u, s)).2) (1 - d * v ^ (d - 1)) v := by
  have hg_u : HasDerivAt (fun s => gfun d s v) (-1) u := by
    have := ((hasDerivAt_const u v).sub (hasDerivAt_id u)).sub_const (v ^ d)
    simpa [gfun] using this
  have hg_v : HasDerivAt (fun s => gfun d u s) (1 - d * v ^ (d - 1)) v := by
    have := ((hasDerivAt_id v).sub_const u).sub (hasDerivAt_pow d v)
    convert this using 1
    funext s; simp [gfun]
  simp only [Ed_explicit]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (hasDerivAt_const u v).sub (hg_u.pow d)
    convert this using 1
    · funext s; simp [gfun]
    · ring
  · have := (hasDerivAt_id v).sub (hg_v.pow d)
    convert this using 1
    funext s; simp [gfun]
  · simpa [gfun] using hg_u
  · simpa [gfun] using hg_v

/-- **`det DE_d = 1`.** -/
theorem Ed_jacobian (d : ℕ) (u v : ℝ) :
    (d * gfun d u v ^ (d - 1)) * (1 - d * v ^ (d - 1)) -
      (1 - d * gfun d u v ^ (d - 1) * (1 - d * v ^ (d - 1))) * (-1) = 1 := by
  ring

end OddShear

#print axioms OddShear.Ed_six
#print axioms OddShear.Ed_cube_iff
#print axioms OddShear.Ed_invariant
#print axioms OddShear.Ed_partials
#print axioms OddShear.Ed_jacobian
