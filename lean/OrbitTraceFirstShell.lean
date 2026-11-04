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
      simpa only [Nat.add_zero, Nat.cast_one, one_mul, pow_zero, mul_one] using
        (show M (p + 1) = s ^ (p + 1) - a from by
          rw [heq, pow_succ]
          ring)
  | succ j ih =>
      intro hj
      have hj' : j ≤ p := by omega
      have hjs : j + 1 ≤ p := by omega
      have hr := hrec (j + 1)
      have hstep : M (p + 1 + (j + 1)) =
          s * M (p + 1 + j) - a * M (j + 1) := by
        convert hr using 1 <;> omega
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

#print axioms OrbitTrace.first_shell_moment
#print axioms OrbitTrace.first_shell_linear

end OrbitTrace
