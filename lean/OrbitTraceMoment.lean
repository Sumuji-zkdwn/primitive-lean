import Mathlib

/-!
# Algebraic moments of a polynomial root relation

This establishes a recurrence for *arbitrary* finite root families with weights,
not only the cubic numerical example.  It avoids polynomial root solving and
works over every commutative ring.
-/

namespace OrbitTrace

universe u v

def weightedMoment {K : Type u} [CommRing K]
    {ι : Type v} [DecidableEq ι]
    (nodes : Finset ι) (r w : ι → K) (k : ℕ) : K :=
  ∑ i ∈ nodes, w i * r i ^ k

theorem weighted_moment_recurrence
    {K : Type u} [CommRing K]
    {ι : Type v} [DecidableEq ι]
    (nodes : Finset ι) (r w : ι → K)
    (p k : ℕ) (s a : K)
    (hroot : ∀ i ∈ nodes, r i ^ (p + 1) = s * r i ^ p - a) :
    weightedMoment nodes r w (k + p + 1) =
      s * weightedMoment nodes r w (k + p) -
        a * weightedMoment nodes r w k := by
  unfold weightedMoment
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    w i * r i ^ (k + p + 1) =
        w i * (r i ^ k * r i ^ (p + 1)) := by
      rw [show k + p + 1 = k + (p + 1) by omega, pow_add]
    _ = s * (w i * r i ^ (k + p)) - a * (w i * r i ^ k) := by
      rw [hroot i hi, pow_add]
      ring

#print axioms OrbitTrace.weighted_moment_recurrence

end OrbitTrace
