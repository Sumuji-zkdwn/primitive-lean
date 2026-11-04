import OrbitTraceFirstShell
import OrbitTraceRootRecurrence
import OrbitTraceMonicSequence

/-!
# Identification of the canonical polynomial moment with the root trace

The finite root trace over any field K with an algebra of Q is precisely the
specialization of the recursively constructed canonicalMoment ∈ Q[X] at s.
No numerical root solving is used.

The factorization hypothesis says the p+1 roots are distinct and exhaustive.
-/

namespace OrbitTrace

open Polynomial

/-- The actual recursively constructed canonical moments, without an
external recurrence hypothesis, form a basis of Q[X]. -/
noncomputable def canonicalMomentBasis (p : ℕ) (a : ℚ) :
    Module.Basis ℕ ℚ (Polynomial ℚ) :=
  polynomial_moment_basis p a (canonicalMoment p a)
    (by
      intro k hk
      exact canonicalMoment_initial p k a hk)
    (by
      intro k
      exact canonicalMoment_recurrence p k a)

#print axioms OrbitTrace.canonicalMomentBasis

noncomputable def specializeCanonicalMoment
    {K : Type*} [Field K] [Algebra ℚ K]
    (p : ℕ) (a : ℚ) (s : K) (k : ℕ) : K :=
  (canonicalMoment p a k).eval₂ (algebraMap ℚ K) s

theorem specializeCanonicalMoment_initial
    {K : Type*} [Field K] [Algebra ℚ K]
    (p : ℕ) (a : ℚ) (s : K) (k : ℕ) (hk : k ≤ p) :
    specializeCanonicalMoment p a s k = s ^ k := by
  unfold specializeCanonicalMoment
  rw [canonicalMoment_initial p k a hk]
  simp

theorem specializeCanonicalMoment_recurrence
    {K : Type*} [Field K] [Algebra ℚ K]
    (p : ℕ) (a : ℚ) (s : K) (k : ℕ) :
    specializeCanonicalMoment p a s (k + p + 1) =
      s * specializeCanonicalMoment p a s (k + p) -
        (algebraMap ℚ K a) * specializeCanonicalMoment p a s k := by
  unfold specializeCanonicalMoment
  rw [canonicalMoment_recurrence]
  simp only [eval₂_sub, eval₂_mul, eval₂_X, eval₂_C]

theorem rootMoment_eq_canonicalSpecialization
    {K : Type*} [Field K] [Algebra ℚ K]
    {ι : Type*} [DecidableEq ι]
    (nodes : Finset ι) (roots : ι → K)
    (hinj : Set.InjOn roots (↑nodes : Set ι))
    (p : ℕ) (hcard : nodes.card = p + 1)
    (a : ℚ) (s : K)
    (hfactor : ((X : Polynomial K) ^ (p + 1) -
       C s * X ^ p + C (algebraMap ℚ K a)) =
       Lagrange.nodal nodes roots) :
    rootMoment nodes roots p = specializeCanonicalMoment p a s := by
  symm
  exact rootMoment_unique nodes roots hinj p hcard s
    (algebraMap ℚ K a) hfactor
    (specializeCanonicalMoment p a s)
    (specializeCanonicalMoment_initial p a s)
    (specializeCanonicalMoment_recurrence p a s)

#print axioms OrbitTrace.specializeCanonicalMoment_initial
#print axioms OrbitTrace.specializeCanonicalMoment_recurrence
#print axioms OrbitTrace.rootMoment_eq_canonicalSpecialization

end OrbitTrace
