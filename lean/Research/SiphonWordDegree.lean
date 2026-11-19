import Research.SiphonFreeProduct

/-!
# Exact degrees of reduced siphon words

`docs/research/2026-11-17-siphon-free-product.md` proves by hand that a reduced word
`a^{j₀} b a^{j_1} ⋯ b a^{j_s}` (`a = L`, `b = E L³`, interior `j_i ∈ 1..5`) is a polynomial map of
the plane of total degree exactly `18^m`, where `m = 1 + #{i : j_i ≠ 3}` counts the maximal
blocks `E^h`; for instance `deg((ba)^n) = 18^n` and `deg((ba³)^n) = 18`.
`Research/SiphonFreeProduct.lean` proved the free-product structure without this formula.
This module proves it.

* The word is applied to the generic point `(u, v) = (X 0, X 1)` of
  `MvPolynomial (Fin 2) ℝ`; `eval_word` shows that evaluating the resulting pair at
  `x ∈ ℝ²` gives the word applied to `x`, so `deg` is the total degree of the word's map.
* `EIter_degrees`: if `deg w₁ = e ≥ 1` and `deg w₂ ≤ e`, then `E^h w` (`h ≥ 1`) has degrees
  `(6e, 18e)`.
* `Inv_step_three`: after an interior `a³`, `b` merges the block (`E^h ↦ E^(h+1)`); the
  degrees do not change. `Inv_step_other`: any other interior power starts a new block and
  multiplies `e` by `18`. `Inv_initial`: the first block has `e = 1`.
* `word_degree`: the total degree is exactly `18^m`; `deg_ba_pow`, `deg_ba3_pow` are the two
  examples of the note.

Only total-degree arithmetic over the domain `MvPolynomial (Fin 2) ℝ` is used
(`totalDegree_mul_of_isDomain`, `totalDegree_add_eq_left_of_totalDegree_lt`).
-/
namespace SiphonWordDegree

open SiphonFreeProduct MvPolynomial

noncomputable section

/-- Bivariate real polynomials in `u = X 0`, `v = X 1`. -/
abbrev P := MvPolynomial (Fin 2) ℝ

theorem totalDegree_pow_eq {p : P} (hp : p ≠ 0) (n : ℕ) :
    (p ^ n).totalDegree = n * p.totalDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, totalDegree_mul_of_isDomain (pow_ne_zero _ hp) hp, ih]; ring

theorem ne_zero_of_totalDegree_pos {p : P} (h : 0 < p.totalDegree) : p ≠ 0 := by
  rintro rfl; simp at h

/-- Degrees of `E^h w` for `h ≥ 1`, `deg w₁ = e ≥ 1`, `deg w₂ ≤ e`. -/
theorem EIter_degrees {w : P × P} {e : ℕ} (he : 1 ≤ e) (h1 : w.1.totalDegree = e)
    (h2 : w.2.totalDegree ≤ e) {h : ℕ} (hh : 1 ≤ h) :
    (EIter (C (h : ℝ)) w).1.totalDegree = 6 * e ∧ (EIter (C (h : ℝ)) w).2.totalDegree = 18 * e := by
  obtain ⟨p, q⟩ := w
  simp only at h1 h2
  have hp : p ≠ 0 := ne_zero_of_totalDegree_pos (by omega)
  have hp3 : (p ^ 3).totalDegree = 3 * e := by rw [totalDegree_pow_eq hp, h1]
  have hr : (rr (p, q)).totalDegree = 3 * e := by
    simp only [rr]; rw [totalDegree_add_eq_right_of_totalDegree_lt (by rw [hp3]; omega), hp3]
  have hr0 : rr (p, q) ≠ 0 := ne_zero_of_totalDegree_pos (by omega)
  have hC : (C (h : ℝ) : P) ≠ 0 := by
    rw [Ne, C_eq_zero]; exact_mod_cast (show h ≠ 0 by omega)
  have hCr : (C (h : ℝ) * rr (p, q) ^ 2).totalDegree = 6 * e := by
    rw [totalDegree_mul_of_isDomain hC (pow_ne_zero _ hr0), totalDegree_C,
      totalDegree_pow_eq hr0, hr]; ring
  have hu : (p + C (h : ℝ) * rr (p, q) ^ 2).totalDegree = 6 * e := by
    rw [totalDegree_add_eq_right_of_totalDegree_lt (by rw [hCr]; omega), hCr]
  have hu0 : p + C (h : ℝ) * rr (p, q) ^ 2 ≠ 0 := ne_zero_of_totalDegree_pos (by omega)
  have hu3 : ((p + C (h : ℝ) * rr (p, q) ^ 2) ^ 3).totalDegree = 18 * e := by
    rw [totalDegree_pow_eq hu0, hu]; ring
  refine ⟨hu, ?_⟩
  show (rr (p, q) - (p + C (h : ℝ) * rr (p, q) ^ 2) ^ 3).totalDegree = 18 * e
  rw [sub_eq_add_neg, totalDegree_add_eq_right_of_totalDegree_lt (by rw [totalDegree_neg, hu3, hr]; omega),
    totalDegree_neg, hu3]

/-- The total degree of a polynomial map `(f, g)`: the larger of the two total degrees. -/
def deg (z : P × P) : ℕ := max z.1.totalDegree z.2.totalDegree

/-- One step `z ↦ b (a^j z)` of a word, applied right to left. -/
def step (j : ℕ) (z : P × P) : P × P := Bf ((Lperm P ^ j) z)

/-- The reduced word `a^{j₀} b a^{j_1} b ⋯ b a^{j_s}` applied to `z` (the rightmost letter
first); `inner` lists the interior exponents in the order of application. -/
def word (j0 : ℕ) (inner : List ℕ) (js : ℕ) (z : P × P) : P × P :=
  (Lperm P ^ j0) (inner.foldl (fun z j => step j z) (step js z))

/-- The number `m` of maximal blocks `E^h`: interior `a³` merges neighbouring blocks. -/
def blocks (inner : List ℕ) : ℕ := 1 + (inner.filter (· ≠ 3)).length

/-- The generic point `(u, v)`; a word applied to it gives the word's component polynomials. -/
def generic : P × P := (X 0, X 1)

/-- Invariant: the current point is `E^h w` with `deg w₁ = e`, `deg w₂ ≤ e`, `h ≥ 1`. -/
def Inv (e : ℕ) (z : P × P) : Prop :=
  ∃ h : ℕ, 1 ≤ h ∧ ∃ w : P × P, w.1.totalDegree = e ∧ w.2.totalDegree ≤ e ∧
    z = EIter (C (h : ℝ)) w

theorem Inv_degrees {e : ℕ} (he : 1 ≤ e) {z : P × P} (hz : Inv e z) :
    z.1.totalDegree = 6 * e ∧ z.2.totalDegree = 18 * e := by
  obtain ⟨h, hh, w, h1, h2, rfl⟩ := hz
  exact EIter_degrees he h1 h2 hh

theorem Bf_L3 (y : P × P) : Bf ((Lperm P ^ 3) y) = Ef y := by
  rw [(Lperm_pow_apply y).2.2.1, Bf]; simp

/-- An interior `a³` merges two blocks: `b a³ E^h = E^(h+1)`. -/
theorem Inv_step_three {e : ℕ} {z : P × P} (hz : Inv e z) : Inv e (step 3 z) := by
  obtain ⟨h, hh, w, h1, h2, rfl⟩ := hz
  refine ⟨h + 1, by omega, w, h1, h2, ?_⟩
  rw [step, Bf_L3, Ef_EIter, Nat.cast_add, Nat.cast_one, map_add, map_one]

/-- Any other interior power starts a new block and multiplies `e` by `18`. -/
theorem Inv_step_other {e : ℕ} (he : 1 ≤ e) {z : P × P} (hz : Inv e z) {j : ℕ} (hj1 : 1 ≤ j)
    (hj5 : j ≤ 5) (hj3 : j ≠ 3) : Inv (18 * e) (step j z) := by
  obtain ⟨d1, d2⟩ := Inv_degrees he hz
  obtain ⟨p, q⟩ := z
  simp only at d1 d2
  have hlt : p.totalDegree < q.totalDegree := by omega
  have e1 : (q - p).totalDegree = 18 * e := by
    rw [sub_eq_add_neg, totalDegree_add_eq_left_of_totalDegree_lt (by rw [totalDegree_neg]; exact hlt), d2]
  have e2 : (p - q).totalDegree = 18 * e := by
    rw [sub_eq_add_neg, totalDegree_add_eq_right_of_totalDegree_lt (by rw [totalDegree_neg]; exact hlt),
      totalDegree_neg, d2]
  obtain ⟨f1, f2, -, f4, f5⟩ := Lperm_pow_apply (p, q)
  refine ⟨1, le_rfl, (-((Lperm P ^ j) (p, q)).1, -((Lperm P ^ j) (p, q)).2), ?_, ?_, ?_⟩
  · interval_cases j <;> simp only [f1, f2, f4, f5, totalDegree_neg, neg_sub, neg_neg] at * <;>
      first | exact e1 | exact e2 | exact d2 | omega
  · interval_cases j <;> simp only [f1, f2, f4, f5, totalDegree_neg, neg_sub, neg_neg] at * <;>
      omega
  · rw [step, Bf, Nat.cast_one, map_one, EIter_one]

theorem totalDegree_X_sub_X {i j : Fin 2} (hij : i ≠ j) : (X i - X j : P).totalDegree = 1 := by
  apply le_antisymm
  · exact (totalDegree_sub _ _).trans (by simp [totalDegree_X])
  · have hmem : Finsupp.single i 1 ∈ (X i - X j : P).support := by
      have hne : Finsupp.single j 1 ≠ Finsupp.single i 1 := fun h =>
        hij (Finsupp.single_left_injective one_ne_zero h).symm
      rw [mem_support_iff, coeff_sub, coeff_X_same, coeff_X]
      simp [hne]
    have := le_totalDegree hmem
    simpa using this

theorem Inv_initial {js : ℕ} (hjs : js ≤ 5) : Inv 1 (step js generic) := by
  have hX : ∀ i : Fin 2, (X i : P).totalDegree = 1 := fun i => totalDegree_X i
  have h01 : (X 0 - X 1 : P).totalDegree = 1 := totalDegree_X_sub_X (by decide)
  have h10 : (X 1 - X 0 : P).totalDegree = 1 := totalDegree_X_sub_X (by decide)
  refine ⟨1, le_rfl, (-((Lperm P ^ js) generic).1, -((Lperm P ^ js) generic).2), ?_, ?_, ?_⟩
  · obtain ⟨f1, f2, f3, f4, f5⟩ := Lperm_pow_apply (generic : P × P)
    interval_cases js <;> simp only [f1, f2, f3, f4, f5, pow_zero, Equiv.Perm.coe_one, id_eq] <;>
      simp [generic, totalDegree_neg, neg_sub, hX, h01, h10]
  · obtain ⟨f1, f2, f3, f4, f5⟩ := Lperm_pow_apply (generic : P × P)
    interval_cases js <;> simp only [f1, f2, f3, f4, f5, pow_zero, Equiv.Perm.coe_one, id_eq] <;>
      simp [generic, totalDegree_neg, neg_sub, hX, h01, h10]
  · rw [step, Bf, Nat.cast_one, map_one, EIter_one]

theorem Inv_fold {e : ℕ} (he : 1 ≤ e) (inner : List ℕ) (hin : ∀ j ∈ inner, 1 ≤ j ∧ j ≤ 5)
    {z : P × P} (hz : Inv e z) :
    Inv (e * 18 ^ (inner.filter (· ≠ 3)).length) (inner.foldl (fun z j => step j z) z) := by
  induction inner generalizing e z with
  | nil => simpa using hz
  | cons j rest ih =>
    obtain ⟨hj1, hj5⟩ := hin j (by simp)
    have hrest : ∀ j ∈ rest, 1 ≤ j ∧ j ≤ 5 := fun k hk => hin k (by simp [hk])
    simp only [List.foldl_cons]
    by_cases hj3 : j = 3
    · subst hj3
      have := ih he hrest (Inv_step_three hz)
      simpa [List.filter_cons] using this
    · have := ih (by omega) hrest (Inv_step_other he hz hj1 hj5 hj3)
      have hlen : ((j :: rest).filter (· ≠ 3)).length = (rest.filter (· ≠ 3)).length + 1 := by
        simp [hj3]
      rw [hlen, pow_succ, show e * (18 ^ (rest.filter (· ≠ 3)).length * 18) =
        18 * e * 18 ^ (rest.filter (· ≠ 3)).length by ring]
      exact this

theorem deg_final {e : ℕ} (he : 1 ≤ e) {z : P × P} (hz : Inv e z) {j0 : ℕ} (hj0 : j0 ≤ 5) :
    deg ((Lperm P ^ j0) z) = 18 * e := by
  obtain ⟨d1, d2⟩ := Inv_degrees he hz
  obtain ⟨p, q⟩ := z
  simp only at d1 d2
  have hlt : p.totalDegree < q.totalDegree := by omega
  have e1 : (q - p).totalDegree = 18 * e := by
    rw [sub_eq_add_neg, totalDegree_add_eq_left_of_totalDegree_lt (by rw [totalDegree_neg]; exact hlt), d2]
  have e2 : (p - q).totalDegree = 18 * e := by
    rw [sub_eq_add_neg, totalDegree_add_eq_right_of_totalDegree_lt (by rw [totalDegree_neg]; exact hlt),
      totalDegree_neg, d2]
  obtain ⟨f1, f2, f3, f4, f5⟩ := Lperm_pow_apply (p, q)
  interval_cases j0 <;> simp only [deg, pow_zero, Equiv.Perm.coe_one, id_eq, f1, f2, f3, f4, f5,
    totalDegree_neg, d1, d2, e1, e2] <;> omega

/-- **Degree of reduced words**: a reduced word `a^{j₀} b a^{j_1} ⋯ b a^{j_s}` (`s ≥ 1`
letters `b`, interior exponents in `1..5`, end exponents in `0..5`) is a polynomial map of
total degree exactly `18^m`, `m = 1 + #{interior j_i ≠ 3}`. -/
theorem word_degree {j0 js : ℕ} (hj0 : j0 ≤ 5) (hjs : js ≤ 5) (inner : List ℕ)
    (hin : ∀ j ∈ inner, 1 ≤ j ∧ j ≤ 5) :
    deg (word j0 inner js generic) = 18 ^ blocks inner := by
  have h := Inv_fold le_rfl inner hin (Inv_initial hjs)
  rw [word, deg_final (Nat.one_le_iff_ne_zero.mpr (by positivity)) h hj0, blocks, one_mul,
    pow_add, pow_one]

theorem foldl_replicate (j k : ℕ) (z : P × P) :
    (List.replicate k j).foldl (fun z j => step j z) z = (step j)^[k] z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.foldl_cons, ih, Function.iterate_succ_apply]

/-- `deg ((b a)^n) = 18^n`. -/
theorem deg_ba_pow (n : ℕ) : deg ((step 1)^[n + 1] generic) = 18 ^ (n + 1) := by
  have h := word_degree (j0 := 0) (js := 1) (by norm_num) (by norm_num) (List.replicate n 1)
    (fun j hj => by rw [(List.mem_replicate.mp hj).2]; norm_num)
  rw [word, pow_zero, Equiv.Perm.coe_one, id_eq, foldl_replicate,
    ← Function.iterate_succ_apply] at h
  rw [h, blocks, List.filter_replicate]
  simp; ring

/-- `deg ((b a³)^n) = 18` for every `n ≥ 1`: the blocks merge into `E^n`. -/
theorem deg_ba3_pow (n : ℕ) : deg ((step 3)^[n + 1] generic) = 18 := by
  have h := word_degree (j0 := 0) (js := 3) (by norm_num) (by norm_num) (List.replicate n 3)
    (fun j hj => by rw [(List.mem_replicate.mp hj).2]; norm_num)
  rw [word, pow_zero, Equiv.Perm.coe_one, id_eq, foldl_replicate,
    ← Function.iterate_succ_apply] at h
  rw [h, blocks, List.filter_replicate]
  simp

/-- The components of `word … generic` are the word's polynomial map: evaluating them at
`x` gives the word applied to `(x 0, x 1) ∈ ℝ²`. -/
theorem eval_word (j0 : ℕ) (inner : List ℕ) (js : ℕ) (x : Fin 2 → ℝ) :
    pmap (MvPolynomial.eval x) (word j0 inner js generic) =
      (Lperm ℝ ^ j0) (inner.foldl (fun z j => Bf ((Lperm ℝ ^ j) z))
        (Bf ((Lperm ℝ ^ js) (x 0, x 1)))) := by
  have hL : ∀ (j : ℕ) (z : P × P), pmap (MvPolynomial.eval x) ((Lperm P ^ j) z) =
      (Lperm ℝ ^ j) (pmap (MvPolynomial.eval x) z) := fun j z =>
    pmap_gen_pow (MvPolynomial.eval x) true j z
  have hfold : ∀ (l : List ℕ) (z : P × P), pmap (MvPolynomial.eval x)
      (l.foldl (fun z j => step j z) z) =
      l.foldl (fun z j => Bf ((Lperm ℝ ^ j) z)) (pmap (MvPolynomial.eval x) z) := by
    intro l
    induction l with
    | nil => intro z; rfl
    | cons j rest ih =>
      intro z
      rw [List.foldl_cons, List.foldl_cons, ih, step, pmap_Bf, hL]
  rw [word, hL, hfold, step, pmap_Bf, hL]
  congr
  simp [pmap, generic]

end

end SiphonWordDegree

#print axioms SiphonWordDegree.EIter_degrees
#print axioms SiphonWordDegree.Inv_step_three
#print axioms SiphonWordDegree.Inv_step_other
#print axioms SiphonWordDegree.Inv_initial
#print axioms SiphonWordDegree.word_degree
#print axioms SiphonWordDegree.deg_ba_pow
#print axioms SiphonWordDegree.deg_ba3_pow
#print axioms SiphonWordDegree.eval_word
