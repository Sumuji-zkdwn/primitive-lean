import Mathlib

/-!
# Arbitrary-p first-shell transfer formula

For the relation x^(p+1) = s*x^p - a, a weighted moment sequence
with initial data M(k)=s^k (k<=p) has a completely explicit next shell.
This is a universal theorem for every commutative ring; no distinct-root
or characteristic-zero hypotheses are required for the recurrence itself.

This is the first nontrivial uniform layer of the residue-class chains,
not yet the full Jordan similarity theorem.
-/

namespace OrbitTrace

theorem first_shell_moment
    {K : Type*} [CommRing K]
    (p : ℕ) (s a : K) (M : ℕ → K)
    (hinit : ∀ k : ℕ, k ≤ p → M k = s ^ k)
    (hrec : ∀ k : ℕ,
      M (k + p + 1) = s * M (k + p) - a * M k) :
    ∀ j : ℕ, j ≤ p →
      M (p + 1 + j) =
        s ^ (p + 1 + j) - ((j + 1 : ℕ) : K) * a * s ^ j := by
  intro j
  induction j with
  | zero =>
      intro _
      have hp := hinit p (le_refl p)
      have hzero := hinit 0 (Nat.zero_le p)
      have hr := hrec 0
      have heq : M (p + 1) = s * s ^ p - a := by
        simpa [hp, hzero] using hr
      have hbase : M (p + 1) = s ^ (p + 1) - a := by
        rw [heq, pow_succ]
        ring
      simpa using hbase
  | succ j ih =>
      intro hj
      have hj' : j ≤ p := by omega
      have hjs : j + 1 ≤ p := by omega
      have hr := hrec (j + 1)
      have hstep : M (p + 1 + (j + 1)) =
          s * M (p + 1 + j) - a * M (j + 1) := by
        have hi1 : j + 1 + p + 1 = p + 1 + (j + 1) := by omega
        have hi2 : j + 1 + p = p + 1 + j := by omega
        simpa only [hi1, hi2] using hr
      calc
        M (p + 1 + (j + 1)) =
            s * M (p + 1 + j) - a * M (j + 1) := hstep
        _ = s ^ (p + 1 + (j + 1)) -
            (((j + 1 + 1 : ℕ) : K) * a * s ^ (j + 1)) := by
          rw [ih hj', hinit (j + 1) hjs]
          push_cast
          ring

theorem first_shell_constant
    {K : Type*} [CommRing K]
    (p : ℕ) (s a : K) (M : ℕ → K)
    (hinit : ∀ k : ℕ, k ≤ p → M k = s ^ k)
    (hrec : ∀ k : ℕ,
      M (k + p + 1) = s * M (k + p) - a * M k) :
    M (p + 1) = s ^ (p + 1) - a := by
  have h := first_shell_moment p s a M hinit hrec 0 (Nat.zero_le p)
  simpa using h

theorem first_shell_linear
    {K : Type*} [CommRing K]
    (p j : ℕ) (s a : K) (M : ℕ → K)
    (hinit : ∀ k : ℕ, k ≤ p → M k = s ^ k)
    (hrec : ∀ k : ℕ,
      M (k + p + 1) = s * M (k + p) - a * M k)
    (hj : j ≤ p) :
    M (p + 1 + j) - s ^ (p + 1 + j) =
      -(((j + 1 : ℕ) : K) * a * s ^ j) := by
  rw [first_shell_moment p s a M hinit hrec j hj]
  ring


/-!
Concrete polynomial sequence in the formal observation variable X.
This recursion is constructed, rather than postulated as an arbitrary M.
-/

noncomputable def canonicalMoment (p : ℕ) (a : ℚ) (k : ℕ) : Polynomial ℚ :=
  if hk : k ≤ p then
    Polynomial.X ^ k
  else
    Polynomial.X * canonicalMoment p a (k - 1) -
      Polynomial.C a * canonicalMoment p a (k - (p + 1))
termination_by k
decreasing_by all_goals omega

theorem canonicalMoment_initial (p k : ℕ) (a : ℚ) (hk : k ≤ p) :
    canonicalMoment p a k = (Polynomial.X : Polynomial ℚ) ^ k := by
  rw [canonicalMoment]
  simp [hk]

theorem canonicalMoment_recurrence (p k : ℕ) (a : ℚ) :
    canonicalMoment p a (k + p + 1) =
      (Polynomial.X : Polynomial ℚ) * canonicalMoment p a (k + p) -
        Polynomial.C a * canonicalMoment p a k := by
  have hgt : ¬ k + p + 1 ≤ p := by omega
  have hi1 : k + p + 1 - 1 = k + p := by omega
  have hi2 : k + p + 1 - (p + 1) = k := by omega
  conv_lhs => rw [canonicalMoment]
  simp only [dif_neg hgt, hi1, hi2]

theorem canonicalMoment_first_shell
    (p j : ℕ) (a : ℚ) (hj : j ≤ p) :
    canonicalMoment p a (p + 1 + j) =
      (Polynomial.X : Polynomial ℚ) ^ (p + 1 + j) -
        ((j + 1 : ℕ) : Polynomial ℚ) * Polynomial.C a *
          (Polynomial.X : Polynomial ℚ) ^ j := by
  apply first_shell_moment p (Polynomial.X : Polynomial ℚ)
    (Polynomial.C a) (canonicalMoment p a)
  · intro k hk
    exact canonicalMoment_initial p k a hk
  · intro k
    exact canonicalMoment_recurrence p k a
  · exact hj


/-!
Actual polynomial-observable bridge for the full two-shell range of degrees.
The canonical transfer here is defined on linear combinations of monomials,
so the equality below is not merely an unrelated companion matrix identity.
-/

noncomputable def twoLayerEncode (p : ℕ) (low high : Fin (p + 1) → ℚ) : Polynomial ℚ :=
  ∑ i : Fin (p + 1),
    (Polynomial.C (low i) * Polynomial.X ^ i.val +
      Polynomial.C (high i) * Polynomial.X ^ (p + 1 + i.val))

noncomputable def twoLayerTransfer (p : ℕ) (a : ℚ)
    (low high : Fin (p + 1) → ℚ) : Polynomial ℚ :=
  ∑ i : Fin (p + 1),
    (Polynomial.C (low i) * canonicalMoment p a i.val +
      Polynomial.C (high i) * canonicalMoment p a (p + 1 + i.val))

/-- The actual transfer of every polynomial in the two-shell span is the
explicit weighted nilpotent block action in polynomial coordinates. -/
theorem twoLayerTransfer_eq_encode (p : ℕ) (a : ℚ)
    (low high : Fin (p + 1) → ℚ) :
    twoLayerTransfer p a low high =
      twoLayerEncode p
        (fun i => low i - ((i.val + 1 : ℕ) : ℚ) * a * high i)
        high := by
  unfold twoLayerTransfer twoLayerEncode
  apply Finset.sum_congr rfl
  intro i hi
  have hle : i.val ≤ p := by omega
  rw [canonicalMoment_initial p i.val a hle,
      canonicalMoment_first_shell p i.val a hle]
  simp only [map_sub, map_mul, map_natCast]
  ring


theorem twoLayerEncode_coeff_low (p : ℕ)
    (low high : Fin (p + 1) → ℚ) (j : Fin (p + 1)) :
    (twoLayerEncode p low high).coeff j.val = low j := by
  classical
  unfold twoLayerEncode
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  have hhigh (i : Fin (p + 1)) : j.val ≠ p + 1 + i.val := by omega
  have hlow (i : Fin (p + 1)) : (j.val = i.val) ↔ (j = i) := by
    exact Fin.val_inj
  simp [hhigh, hlow]

theorem twoLayerEncode_coeff_high (p : ℕ)
    (low high : Fin (p + 1) → ℚ) (j : Fin (p + 1)) :
    (twoLayerEncode p low high).coeff (p + 1 + j.val) = high j := by
  classical
  unfold twoLayerEncode
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  have hlow (i : Fin (p + 1)) : p + 1 + j.val ≠ i.val := by omega
  have hhigh (i : Fin (p + 1)) :
      (p + 1 + j.val = p + 1 + i.val) ↔ (j = i) := by
    constructor
    · intro h
      apply Fin.ext
      omega
    · intro h
      subst i
      rfl
  simp only [hlow, ite_false, zero_add, hhigh]
  simp

theorem twoLayerEncode_injective (p : ℕ) :
    Function.Injective
      (fun v : (Fin (p + 1) → ℚ) × (Fin (p + 1) → ℚ) =>
        twoLayerEncode p v.1 v.2) := by
  intro v w h
  apply Prod.ext
  · funext i
    have hc := congrArg (fun P : Polynomial ℚ => P.coeff i.val) h
    simpa only [twoLayerEncode_coeff_low] using hc
  · funext i
    have hc :=
      congrArg (fun P : Polynomial ℚ => P.coeff (p + 1 + i.val)) h
    simpa only [twoLayerEncode_coeff_high] using hc


/-!
Uniform second shell of the algebraic moment recurrence (three-layer data).
The natural coefficient `secondShellCoeff` equals binomial(j+2,2).
We retain the recurrence formulation to avoid choosing rational denominators.
-/

def secondShellCoeff : ℕ → ℕ
  | 0 => 1
  | j + 1 => secondShellCoeff j + (j + 2)

theorem second_shell_moment
    {K : Type*} [CommRing K]
    (p : ℕ) (s a : K) (M : ℕ → K)
    (hinit : ∀ k : ℕ, k ≤ p → M k = s ^ k)
    (hrec : ∀ k : ℕ,
      M (k + p + 1) = s * M (k + p) - a * M k) :
    ∀ j : ℕ, j ≤ p →
      M (2 * (p + 1) + j) =
        s ^ j *
          ((s ^ (p + 1)) ^ 2 -
           (((p + 2 + j : ℕ) : K) * a * s ^ (p + 1)) +
           ((secondShellCoeff j : ℕ) : K) * a ^ 2) := by
  intro j
  induction j with
  | zero =>
      intro _
      have hp := first_shell_moment p s a M hinit hrec p (le_refl p)
      have h0 := first_shell_moment p s a M hinit hrec 0 (Nat.zero_le p)
      have hq : M (p + 1) = s ^ (p + 1) - a := by simpa using h0
      have hr : M (2 * (p + 1)) =
          s * M (p + 1 + p) - a * M (p + 1) := by
        convert hrec (p + 1) using 1 <;> omega
      simp only [Nat.add_zero, pow_zero, one_mul, secondShellCoeff]
      rw [hr, hp, hq]
      rw [pow_add, pow_succ]
      push_cast
      ring
  | succ j ih =>
      intro hj
      have hj' : j ≤ p := by omega
      have hfirst :=
        first_shell_moment p s a M hinit hrec (j + 1) hj
      have hr : M (2 * (p + 1) + (j + 1)) =
          s * M (2 * (p + 1) + j) -
            a * M (p + 1 + (j + 1)) := by
        convert hrec (p + 1 + (j + 1)) using 1 <;> omega
      rw [hr, ih hj', hfirst]
      have hpow : s ^ (p + 1 + (j + 1)) =
          s ^ (p + 1) * s ^ (j + 1) := by rw [pow_add]
      rw [hpow, pow_succ]
      simp only [secondShellCoeff, Nat.cast_add, Nat.cast_succ]
      push_cast
      ring

#print axioms OrbitTrace.second_shell_moment


#print axioms OrbitTrace.twoLayerEncode_injective

#print axioms OrbitTrace.twoLayerTransfer_eq_encode

#print axioms OrbitTrace.canonicalMoment_first_shell

#print axioms OrbitTrace.first_shell_moment
#print axioms OrbitTrace.first_shell_linear

end OrbitTrace
