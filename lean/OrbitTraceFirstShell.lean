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

#print axioms OrbitTrace.canonicalMoment_first_shell

#print axioms OrbitTrace.first_shell_moment
#print axioms OrbitTrace.first_shell_linear

end OrbitTrace
