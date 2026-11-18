import Research.SiphonPolynomialE
import OrbitTrace

/-!
Finite, degree-bounded version of PR #146.
Upstream snapshot: 763d5d88d26d5fe8a8830c3b74f57461213ba4ed.
All polynomial observations are exact scalar evaluations; seed coordinates are known.
-/
namespace SiphonFiniteDetermination

set_option maxHeartbeats 800000

open Polynomial Elastica.SiphonPolynomialE

noncomputable section

/-- Definitionally the same observation as PR #146's `readPoly`. -/
def readPoly (p : MvPolynomial Bool ℝ) (z : ℝ × ℝ) : ℝ :=
  MvPolynomial.eval (fun i => if i then z.2 else z.1) p

def pathPoly (p : MvPolynomial Bool ℝ) (a b : Polynomial ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C (fun i => if i then b else a) p

theorem pathPoly_eval (p : MvPolynomial Bool ℝ) (a b : Polynomial ℝ) (t : ℝ) :
    (pathPoly p a b).eval t = readPoly p (a.eval t, b.eval t) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [pathPoly, readPoly]
  | add p q hp hq => simp_all [pathPoly, readPoly]
  | mul_X p i hp => cases i <;> simp_all [pathPoly, readPoly]

theorem pathPoly_natDegree_le (p : MvPolynomial Bool ℝ) (a b : Polynomial ℝ)
    (k : ℕ) (ha : a.natDegree ≤ k) (hb : b.natDegree ≤ k) :
    (pathPoly p a b).natDegree ≤ k * p.totalDegree := by
  classical
  unfold pathPoly
  rw [MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  simp only [Fintype.prod_bool, ↓reduceIte]
  have ht := MvPolynomial.le_totalDegree hs
  rw [Finsupp.sum_fintype] at ht
  · simp only [Fintype.sum_bool] at ht
    calc
      (C (p.coeff s) * (b ^ s true * a ^ s false)).natDegree
          ≤ (b ^ s true * a ^ s false).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ (b ^ s true).natDegree + (a ^ s false).natDegree := natDegree_mul_le
      _ ≤ s true * b.natDegree + s false * a.natDegree :=
        Nat.add_le_add natDegree_pow_le natDegree_pow_le
      _ ≤ k * p.totalDegree := by
        have h1 := Nat.mul_le_mul_left (s true) hb
        have h2 := Nat.mul_le_mul_left (s false) ha
        have h3 := Nat.mul_le_mul_left k ht
        nlinarith
  · intro i; rfl

def fibre (r u : ℝ) : ℝ × ℝ := (u, r - u ^ 3)

theorem fibre_degree (p : MvPolynomial Bool ℝ) (r : ℝ) (d : ℕ)
    (hd : p.totalDegree ≤ d) :
    (pathPoly p X (C r - X ^ 3)).natDegree ≤ 3 * d := by
  apply (pathPoly_natDegree_le p _ _ 3 (by simp) ?_).trans (Nat.mul_le_mul_left 3 hd)
  exact (natDegree_sub_le _ _).trans (by norm_num)

theorem transverse_degree (p : MvPolynomial Bool ℝ) (u : ℝ) (d : ℕ)
    (hd : p.totalDegree ≤ d) :
    (pathPoly p (C u) (X - C (u ^ 3))).natDegree ≤ d := by
  simpa using (pathPoly_natDegree_le p _ _ 1 (by simp)
    ((natDegree_sub_le _ _).trans (by norm_num))).trans (Nat.mul_le_mul_left 1 hd)

theorem outgoing_strictAnti (r : ℝ) :
    StrictAnti (fun x : ℝ => I (OrbitTrace.linearE (fibre r x))) := by
  intro x y hxy
  have cube : StrictMono (fun a : ℝ => a ^ 3) := Odd.strictMono_pow (by decide : Odd 3)
  have hv : r - y ^ 3 < r - x ^ 3 := sub_lt_sub_left (cube hxy) r
  change r - y ^ 3 - y + (r - y ^ 3) ^ 3 < r - x ^ 3 - x + (r - x ^ 3) ^ 3
  exact add_lt_add (sub_lt_sub hv hxy) (cube hv)

theorem regular_after_turn (z : ℝ × ℝ) (hz : z ≠ (0,0)) (hI : I z = 0) :
    I (OrbitTrace.linearE z) ≠ 0 := by
  rcases z with ⟨u,v⟩
  change v + u ^ 3 = 0 at hI
  have hv : v = -u ^ 3 := by linarith
  subst v
  have hu : u ≠ 0 := by
    intro h
    subst u
    simp at hz
  change -u ^ 3 - u + (-u ^ 3) ^ 3 ≠ 0
  have hfac : -u ^ 3 - u + (-u ^ 3) ^ 3 = -u * (u ^ 8 + u ^ 2 + 1) := by ring
  rw [hfac]
  exact mul_ne_zero (neg_ne_zero.mpr hu) (by positivity)

def regularSeed (z : ℝ × ℝ) : ℝ × ℝ := if I z = 0 then OrbitTrace.linearE z else z

theorem regularSeed_regular (z : ℝ × ℝ) (hz : z ≠ (0,0)) : I (regularSeed z) ≠ 0 := by
  by_cases h : I z = 0
  · simpa [regularSeed, h] using regular_after_turn z hz h
  · simp [regularSeed, h]

def outgoing (z : ℝ × ℝ) (n : ℕ) : ℝ := I (OrbitTrace.linearE (iterate n z))

def sample (z : ℝ × ℝ) (n m : ℕ) : ℝ × ℝ :=
  iterate m (OrbitTrace.linearE (iterate n z))

theorem outgoing_injective (z : ℝ × ℝ) (hr : I z ≠ 0) :
    Function.Injective (outgoing z) := by
  apply StrictAnti.injective
  intro n m hnm
  have hc : (n : ℝ) < m := by exact_mod_cast hnm
  have ht := add_lt_add_right (mul_lt_mul_of_pos_right hc (sq_pos_of_ne_zero hr)) z.1
  simpa only [outgoing, iterate_eq_closedOrbit, closedOrbit, fibre] using
    outgoing_strictAnti (I z) ht

/-- At most one of the first d+2 outgoing curves is singular. -/
theorem select_curves (z : ℝ × ℝ) (hr : I z ≠ 0) (d : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (d + 2) ∧ S.card = d + 1 ∧
      ∀ n ∈ S, outgoing z n ≠ 0 := by
  classical
  let bad := (Finset.range (d + 2)).filter (fun n => outgoing z n = 0)
  have hb : bad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact outgoing_injective z hr
      ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have hc : d + 1 ≤ ((Finset.range (d + 2)) \ bad).card := by
    have hh := Finset.le_card_sdiff bad (Finset.range (d + 2))
    simp only [Finset.card_range] at hh
    omega
  obtain ⟨S, hs, hcard⟩ := Finset.exists_subset_card_eq hc
  refine ⟨S, fun n hn => (Finset.mem_sdiff.mp (hs hn)).1, hcard, ?_⟩
  intro n hn hzero
  have hh := Finset.mem_sdiff.mp (hs hn)
  exact hh.2 (Finset.mem_filter.mpr ⟨hh.1, hzero⟩)

/-- The degree estimate turns 3d+1 distinct samples into a full cubic fibre. -/
theorem fill_fibre_finite (p : MvPolynomial Bool ℝ) (d : ℕ) (hd : p.totalDegree ≤ d)
    (z : ℝ × ℝ) (hr : I z ≠ 0)
    (hs : ∀ m < 3 * d + 1, readPoly p (iterate m z) = 0) (u : ℝ) :
    readPoly p (fibre (I z) u) = 0 := by
  let q := pathPoly p X (C (I z) - X ^ 3)
  have hcurve (x : ℝ) : q.eval x = readPoly p (fibre (I z) x) := by
    dsimp only [q]
    rw [pathPoly_eval]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, fibre]
  let t : Fin (3 * d + 1) → ℝ := fun m => z.1 + (m.val : ℝ) * I z ^ 2
  have ht : Function.Injective t := by
    intro i j hij
    have h : (i.val : ℝ) * I z ^ 2 = (j.val : ℝ) * I z ^ 2 := add_left_cancel hij
    have hcast := mul_right_cancel₀ (pow_ne_zero 2 hr) h
    apply Fin.ext
    exact_mod_cast hcast
  have hq : q = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero q ht
    · intro m
      rw [hcurve]
      simpa only [iterate_eq_closedOrbit, closedOrbit, fibre, t] using hs m.val m.isLt
    · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le (fibre_degree p (I z) d hd)
  rw [← hcurve, hq]
  simp

/-- Interpolation across any d+1 distinct regular outgoing fibres. -/
theorem polynomial_zero_of_selected (p : MvPolynomial Bool ℝ) (d : ℕ)
    (hd : p.totalDegree ≤ d) (z : ℝ × ℝ) (hr : I z ≠ 0)
    (S : Finset ℕ) (hcard : d < S.card) (hregular : ∀ n ∈ S, outgoing z n ≠ 0)
    (hzero : ∀ n ∈ S, ∀ m < 3 * d + 1, readPoly p (sample z n m) = 0) : p = 0 := by
  classical
  have hrows (n : ℕ) (hn : n ∈ S) (u : ℝ) : readPoly p (fibre (outgoing z n) u) = 0 :=
    fill_fibre_finite p d hd _ (hregular n hn) (hzero n hn) u
  have full (u v : ℝ) : readPoly p (u,v) = 0 := by
    let q := pathPoly p (C u) (X - C (u ^ 3))
    have hline (r : ℝ) : q.eval r = readPoly p (fibre r u) := by
      dsimp only [q]
      rw [pathPoly_eval]
      simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, fibre]
    have hq : q = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q (S.image (outgoing z))
      · intro r hrange
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hrange
        rw [hline]
        exact hrows n hn u
      · rw [Finset.card_image_of_injective _ (outgoing_injective z hr)]
        exact (transverse_degree p u d hd).trans_lt hcard
    have hv := hline (v + u ^ 3)
    simpa [fibre, hq] using hv.symm
  apply MvPolynomial.funext
  intro x
  have hcoords : (fun i : Bool => if i then x true else x false) = x := by
    funext i
    cases i <;> rfl
  simpa [readPoly, hcoords] using full (x false) (x true)

/-- The originally proposed rectangular bound, including zero-invariant seeds. -/
theorem polynomial_zero_of_rectangle (p : MvPolynomial Bool ℝ) (d : ℕ)
    (hd : p.totalDegree ≤ d) (z : ℝ × ℝ) (hz : z ≠ (0,0))
    (hzero : ∀ n < d + 2, ∀ m < 3 * d + 1,
      readPoly p (sample (regularSeed z) n m) = 0) : p = 0 := by
  have hr := regularSeed_regular z hz
  obtain ⟨S, hs, hc, hreg⟩ := select_curves (regularSeed z) hr d
  apply polynomial_zero_of_selected p d hd (regularSeed z) hr S (by omega) hreg
  intro n hn m hm
  exact hzero n (Finset.mem_range.mp (hs hn)) m hm

theorem polynomial_eq_of_rectangle (p q : MvPolynomial Bool ℝ) (d : ℕ)
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d)
    (z : ℝ × ℝ) (hz : z ≠ (0,0))
    (h : ∀ n < d + 2, ∀ m < 3 * d + 1,
      readPoly p (sample (regularSeed z) n m) =
      readPoly q (sample (regularSeed z) n m)) : p = q := by
  apply sub_eq_zero.mp
  apply polynomial_zero_of_rectangle (p - q) d
    ((MvPolynomial.totalDegree_sub p q).trans (max_le hp hq)) z hz
  intro n hn m hm
  simpa [readPoly, sub_eq_zero] using h n hn m hm

/-- A seed-dependent, polynomial-independent set of at most (d+1)(3d+1)
reachable points determines all polynomials of total degree at most d. -/
theorem exists_finite_determining_set (z : ℝ × ℝ) (hz : z ≠ (0,0)) (d : ℕ) :
    ∃ T : Finset (ℝ × ℝ), T.card ≤ (d + 1) * (3 * d + 1) ∧
      (∀ x ∈ T, ∃ n < d + 2, ∃ m < 3 * d + 1,
        x = sample (regularSeed z) n m) ∧
      ∀ p q : MvPolynomial Bool ℝ, p.totalDegree ≤ d → q.totalDegree ≤ d →
        (∀ x ∈ T, readPoly p x = readPoly q x) → p = q := by
  classical
  have hr := regularSeed_regular z hz
  obtain ⟨S, hs, hc, hreg⟩ := select_curves (regularSeed z) hr d
  let T := (S.product (Finset.range (3 * d + 1))).image
    (fun nm => sample (regularSeed z) nm.1 nm.2)
  refine ⟨T, ?_, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by simp [Finset.card_product, hc])
  · intro x hx
    obtain ⟨⟨n,m⟩, hnm, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hn, hm⟩ := Finset.mem_product.mp hnm
    exact ⟨n, Finset.mem_range.mp (hs hn), m, Finset.mem_range.mp hm, rfl⟩
  · intro p q hp hq heq
    apply sub_eq_zero.mp
    apply polynomial_zero_of_selected (p - q) d
      ((MvPolynomial.totalDegree_sub p q).trans (max_le hp hq))
      (regularSeed z) hr S (by omega) hreg
    intro n hn m hm
    have hmem : sample (regularSeed z) n m ∈ T :=
      Finset.mem_image.mpr ⟨(n,m), Finset.mem_product.mpr
        ⟨hn, Finset.mem_range.mpr hm⟩, rfl⟩
    simpa [readPoly, sub_eq_zero] using heq _ hmem

end
end SiphonFiniteDetermination

#print axioms SiphonFiniteDetermination.fibre_degree
#print axioms SiphonFiniteDetermination.transverse_degree
#print axioms SiphonFiniteDetermination.regularSeed_regular
#print axioms SiphonFiniteDetermination.select_curves
#print axioms SiphonFiniteDetermination.polynomial_eq_of_rectangle
#print axioms SiphonFiniteDetermination.exists_finite_determining_set
