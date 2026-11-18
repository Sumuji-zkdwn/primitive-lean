import Mathlib

/-!
# Degree-decreasing maps terminate in finitely many steps

This is a general kernel-checked nilpotence bridge.
It does not assume that any particular transfer operator decreases degree:
that hypothesis must be proved separately before applying the theorem.
-/

namespace OrbitTrace

universe u

def iterDrop {A : Type u} (f : A → A) : ℕ → A → A
  | 0, x => x
  | n + 1, x => iterDrop f n (f x)

theorem iterDrop_fixed {A : Type u}
    (f : A → A) (z : A) (hz : f z = z) (n : ℕ) :
    iterDrop f n z = z := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [iterDrop, hz] using ih

theorem iterDrop_nilpotent_of_rank_drop {A : Type u}
    (f : A → A) (z : A) (hz : f z = z)
    (rank : A → ℕ)
    (hdrop : ∀ x, x ≠ z → f x = z ∨ rank (f x) < rank x)
    (d : ℕ) (x : A) (hx : rank x ≤ d) :
    iterDrop f (d + 1) x = z := by
  induction d generalizing x with
  | zero =>
      by_cases hzero : x = z
      · subst x
        exact iterDrop_fixed f z hz (0 + 1)
      · rcases hdrop x hzero with h | h
        · simp [iterDrop, h]
        · omega
  | succ d ih =>
      by_cases hzero : x = z
      · subst x
        exact iterDrop_fixed f z hz (d + 1 + 1)
      · rcases hdrop x hzero with h | h
        · change iterDrop f (d + 1) (f x) = z
          rw [h]
          exact iterDrop_fixed f z hz (d + 1)
        · have hbound : rank (f x) ≤ d := by omega
          change iterDrop f (d + 1) (f x) = z
          exact ih (f x) hbound

theorem polynomial_degree_drop_nilpotent
    {K : Type u} [Field K]
    (N : Polynomial K →ₗ[K] Polynomial K)
    (hdrop : ∀ p, p ≠ 0 →
       N p = 0 ∨ (N p).natDegree < p.natDegree)
    (d : ℕ) (p : Polynomial K) (hdegree : p.natDegree ≤ d) :
    iterDrop (fun q : Polynomial K => N q) (d + 1) p = 0 := by
  exact iterDrop_nilpotent_of_rank_drop
    (fun q : Polynomial K => N q) (0 : Polynomial K)
    (by simp) (fun q : Polynomial K => q.natDegree)
    hdrop d p hdegree

#print axioms OrbitTrace.iterDrop_nilpotent_of_rank_drop
#print axioms OrbitTrace.polynomial_degree_drop_nilpotent

end OrbitTrace
