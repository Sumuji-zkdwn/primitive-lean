import Research.OperationalWorldGeneration

/-!
# A nonzero forward orbit determines every polynomial on the real plane

Two applications of univariate polynomial rigidity suffice, first along an
invariant level of the siphon map, then across levels reached by the linear
map. Joint polynomial invariants are therefore constant.
-/

namespace SiphonCommonInvariant

open Elastica.SiphonPolynomialE
open Polynomial

noncomputable section

/-- Evaluate a polynomial with two variables, indexed by false and true. -/
def readPoly (p : MvPolynomial Bool ℝ) (z : ℝ × ℝ) : ℝ :=
  MvPolynomial.eval (fun i => if i then z.2 else z.1) p

/-- Substitution of two polynomial paths again gives a univariate polynomial. -/
private theorem curvePolynomial (p : MvPolynomial Bool ℝ) (a b : Polynomial ℝ) :
    ∃ q : Polynomial ℝ, ∀ t : ℝ, readPoly p (a.eval t, b.eval t) = q.eval t := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    exact ⟨Polynomial.C c, by intro t; simp [readPoly]⟩
  | add p s hp hs =>
    obtain ⟨q, hq⟩ := hp
    obtain ⟨k, hk⟩ := hs
    refine ⟨q + k, ?_⟩
    intro t
    simpa [readPoly, Polynomial.eval_add] using congrArg₂ (· + ·) (hq t) (hk t)
  | mul_X p i hp =>
    obtain ⟨q, hq⟩ := hp
    cases i
    · refine ⟨q * a, ?_⟩
      intro t
      simpa [readPoly, Polynomial.eval_mul] using congrArg (fun x => x * a.eval t) (hq t)
    · refine ⟨q * b, ?_⟩
      intro t
      simpa [readPoly, Polynomial.eval_mul] using congrArg (fun x => x * b.eval t) (hq t)

private def fibre (r u : ℝ) : ℝ × ℝ := (u, r - u ^ 3)

/-- If the evaluations agree on an injective sequence, they agree everywhere. -/
private theorem constant_of_samples (p : Polynomial ℝ) (c : ℝ) (s : ℕ → ℝ)
    (hinj : Function.Injective s) (hs : ∀ n, p.eval (s n) = c) (x : ℝ) :
    p.eval x = c := by
  have heq : p = Polynomial.C c := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨n, rfl⟩
    simpa using hs n
  simp [heq]

private theorem fill_regular_fibre (p : MvPolynomial Bool ℝ) (z : ℝ × ℝ)
    (hr : I z ≠ 0) (hs : ∀ n, readPoly p (iterate n z) = 0) (u : ℝ) :
    readPoly p (fibre (I z) u) = 0 := by
  obtain ⟨q, hq⟩ := curvePolynomial p Polynomial.X (Polynomial.C (I z) - Polynomial.X ^ 3)
  have hcurve (x : ℝ) : readPoly p (fibre (I z) x) = q.eval x := by
    simpa [fibre] using hq x
  let s : ℕ → ℝ := fun n => z.1 + (n : ℝ) * I z ^ 2
  have hinj : Function.Injective s := by
    intro m n heq
    have h := add_left_cancel (show z.1 + m * I z ^ 2 = z.1 + n * I z ^ 2 from heq)
    have hcast : (m : ℝ) = n := mul_right_cancel₀ (pow_ne_zero 2 hr) h
    exact_mod_cast hcast
  rw [hcurve]
  apply constant_of_samples q 0 s hinj
  intro n
  rw [← hcurve]
  simpa only [iterate_eq_closedOrbit, closedOrbit, fibre, s] using hs n

private theorem outgoing_invariant_strictAnti (r : ℝ) :
    StrictAnti (fun x : ℝ => I (OrbitTrace.linearE (fibre r x))) := by
  intro x y hxy
  have cube : StrictMono (fun a : ℝ => a ^ 3) := Odd.strictMono_pow (by decide : Odd 3)
  have hv : r - y ^ 3 < r - x ^ 3 := sub_lt_sub_left (cube hxy) r
  change r - y ^ 3 - y + (r - y ^ 3) ^ 3 < r - x ^ 3 - x + (r - x ^ 3) ^ 3
  exact add_lt_add (sub_lt_sub hv hxy) (cube hv)

/-- Every polynomial is determined by the two-block forward trajectories
E^m L E^n from a single seed whose siphon invariant is nonzero. -/
theorem polynomial_zero_of_regular_orbit (p : MvPolynomial Bool ℝ) (z : ℝ × ℝ)
    (hr : I z ≠ 0)
    (hzero : ∀ n m : ℕ, readPoly p (iterate m (OrbitTrace.linearE (iterate n z))) = 0) :
    p = 0 := by
  let t : ℕ → ℝ := fun n => z.1 + (n : ℝ) * I z ^ 2
  let s : ℕ → ℝ := fun n => I (OrbitTrace.linearE (iterate n z))
  have ht : StrictMono t := by
    intro n m hnm
    have hc : (n : ℝ) < m := by exact_mod_cast hnm
    exact add_lt_add_right (mul_lt_mul_of_pos_right hc (sq_pos_of_ne_zero hr)) z.1
  have hiter (n : ℕ) : iterate n z = fibre (I z) (t n) := by
    rw [iterate_eq_closedOrbit]
    rfl
  have hs : StrictAnti s := by
    intro n m hnm
    simp only [s, hiter]
    exact outgoing_invariant_strictAnti (I z) (ht hnm)
  have hrows (n : ℕ) (hn : s n ≠ 0) (u : ℝ) : readPoly p (fibre (s n) u) = 0 :=
    fill_regular_fibre p _ hn (hzero n) u
  have full (u v : ℝ) : readPoly p (u,v) = 0 := by
    obtain ⟨q, hq⟩ := curvePolynomial p (Polynomial.C u) (Polynomial.X - Polynomial.C (u ^ 3))
    have hline (r : ℝ) : readPoly p (fibre r u) = q.eval r := by
      simpa [fibre] using hq r
    have hq0 : q = 0 := by
      apply Polynomial.eq_of_infinite_eval_eq
      apply ((Set.infinite_range_of_injective hs.injective).sdiff (Set.finite_singleton 0)).mono
      rintro x ⟨⟨n, rfl⟩, hx⟩
      have hne : s n ≠ 0 := by simpa using hx
      simpa using (hline _).symm.trans (hrows n hne u)
    have hvalue := hline (v + u ^ 3)
    simpa [fibre, hq0] using hvalue
  apply MvPolynomial.funext
  intro x
  have hcoords : (fun i : Bool => if i then x true else x false) = x := by
    funext i
    cases i <;> rfl
  simpa [readPoly, hcoords] using full (x false) (x true)

private theorem zero_fibre_regular_after_turn (z : ℝ × ℝ) (hz : z ≠ (0,0)) (hI : I z = 0) :
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

/-- For each nonzero seed, all real bivariate polynomials are determined by
forward words of the form E^m L E^n, allowing one initial L when needed. -/
theorem polynomial_zero_of_nonzero_orbit (p : MvPolynomial Bool ℝ) (z : ℝ × ℝ)
    (hz : z ≠ (0,0))
    (hzero : ∀ a ∈ ({z, OrbitTrace.linearE z} : Set (ℝ × ℝ)), ∀ n m : ℕ,
      readPoly p (iterate m (OrbitTrace.linearE (iterate n a))) = 0) :
    p = 0 := by
  by_cases hI : I z = 0
  · exact polynomial_zero_of_regular_orbit p (OrbitTrace.linearE z)
      (zero_fibre_regular_after_turn z hz hI) (hzero _ (by simp))
  · exact polynomial_zero_of_regular_orbit p z hI (hzero _ (by simp))

/-- On the fixed cubic of E, the trajectories with at most one L never
determine every polynomial. The two-turn bound at a nonzero such seed is sharp. -/
theorem one_turn_insufficient_on_zero_fibre (z : ℝ × ℝ) (hz : I z = 0) :
    ∃ p : MvPolynomial Bool ℝ, p ≠ 0 ∧
      (∀ n, readPoly p (iterate n z) = 0) ∧
      (∀ n m, readPoly p (iterate m (OrbitTrace.linearE (iterate n z))) = 0) := by
  let c := I (OrbitTrace.linearE z)
  let J : MvPolynomial Bool ℝ := MvPolynomial.X true + MvPolynomial.X false ^ 3
  let p := J * (J - MvPolynomial.C c)
  have heval (a : ℝ × ℝ) : readPoly p a = I a * (I a - c) := by
    simp [readPoly, p, J, I]
  have hfix (n : ℕ) : iterate n z = z := OperationalWorldGeneration.zero_fibre_fixed n z hz
  refine ⟨p, ?_, ?_, ?_⟩
  · intro hp
    let k : ℝ := max 0 c + 1
    have hk : 0 < k := by dsimp [k]; linarith [le_max_left (0 : ℝ) c]
    have hkc : 0 < k - c := by dsimp [k]; linarith [le_max_right (0 : ℝ) c]
    have hh := heval (0,k)
    simp [hp, readPoly, I] at hh
    exact hh.elim hk.ne' hkc.ne'
  · intro n
    simp [heval, I_iterate, hz]
  · intro n m
    simp [heval, I_iterate, hfix, c]

open OperationalWorldGeneration

/-- Every nonzero forward orbit determines every real bivariate polynomial. -/
theorem polynomial_eq_of_agree_on_orbit (z : State) (hz : z ≠ (0, 0))
    (p q : MvPolynomial Bool ℝ)
    (h : ∀ w, readPoly p (run OrbitTrace.linearE z w) = readPoly q (run OrbitTrace.linearE z w)) :
    p = q := by
  have hv (w : List Move) : readPoly (p - q) (run OrbitTrace.linearE z w) = 0 := by
    simpa [readPoly, sub_eq_zero] using h w
  apply sub_eq_zero.mp
  apply polynomial_zero_of_nonzero_orbit (p - q) z hz
  intro a ha n m
  let w : List Move := List.replicate n .advance ++ .turn :: List.replicate m .advance
  have block (x : State) : run OrbitTrace.linearE x w = iterate m (OrbitTrace.linearE (iterate n x)) := by
    simp only [w, run_append, run_advances, run]
  rcases (show a = z ∨ a = OrbitTrace.linearE z by simpa using ha) with rfl | rfl
  · exact (block a) ▸ hv w
  · have ht : readPoly (p - q) (run OrbitTrace.linearE (OrbitTrace.linearE z) w) = 0 :=
      hv (.turn :: w)
    exact (block (OrbitTrace.linearE z)) ▸ ht

/-- A common polynomial invariant of the two generators is a constant in the polynomial ring. -/
theorem common_polynomial_eq_C (p : MvPolynomial Bool ℝ)
    (hE : ∀ z, readPoly p (E z) = readPoly p z)
    (hL : ∀ z, readPoly p (OrbitTrace.linearE z) = readPoly p z) :
    p = MvPolynomial.C (readPoly p (0, 1)) := by
  have hw (w : List Move) (z : State) : readPoly p (run OrbitTrace.linearE z w) = readPoly p z := by
    induction w generalizing z with
    | nil => rfl
    | cons a w ih =>
      cases a with
      | advance => exact (ih _).trans (hE z)
      | turn => exact (ih _).trans (hL z)
  apply polynomial_eq_of_agree_on_orbit (0, 1) (by norm_num) p
  intro w
  rw [hw]
  simp [readPoly]

end

end SiphonCommonInvariant
