import Mathlib

/-!
# Algebraic Jacobian minor obstruction for four siphon squared reads

The four expressions are the candidate 2x2 minors for
F(u,v) = (u², (u+(v+u³)²)², v², (v+(v-u+v³)²)²).
Their identification with derivatives is separately checked by exact
dual-number arithmetic. This module kernel-proves that at least one
of the displayed polynomial minors is nonzero off the origin.
-/

namespace SiphonFourProbeRegularity

def minor13 (u v : ℝ) : ℝ := 4 * u * v

def minor12 (u v : ℝ) : ℝ :=
  8 * u * (v + u ^ 3) * (u + (v + u ^ 3) ^ 2)

def minor23 (u v : ℝ) : ℝ :=
  4 * v * (u + (v + u ^ 3) ^ 2) * (1 + 6 * u ^ 2 * (v + u ^ 3))

def minor14 (u v : ℝ) : ℝ :=
  4 * u * (v + (v - u + v ^ 3) ^ 2) *
    (1 + 2 * (v - u + v ^ 3) * (1 + 3 * v ^ 2))

private theorem at_u_zero (v : ℝ) (hv : v ≠ 0) : minor23 0 v ≠ 0 := by
  have h : minor23 0 v = 4 * v ^ 3 := by
    dsimp [minor23]
    ring
  rw [h]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hv)

private theorem at_v_zero (u : ℝ) (hu : u ≠ 0) :
    minor12 u 0 ≠ 0 ∨ minor14 u 0 ≠ 0 := by
  by_cases hU : u + u ^ 6 = 0
  · have hneg : u < 0 := by
      by_contra h
      have hnonneg : 0 ≤ u := le_of_not_gt h
      have hpos : 0 < u := lt_of_le_of_ne hnonneg (Ne.symm hu)
      have hpow : 0 ≤ u ^ 6 := pow_nonneg hnonneg _
      have hsum : 0 < u + u ^ 6 := add_pos_of_pos_of_nonneg hpos hpow
      exact (ne_of_gt hsum) hU
    have hfactor : 1 - 2 * u ≠ 0 := by
      have hp : 0 < 1 - 2 * u := by linarith
      exact ne_of_gt hp
    have h14 : minor14 u 0 = 4 * u ^ 3 * (1 - 2 * u) := by
      dsimp [minor14]
      ring
    right
    rw [h14]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hu)) hfactor
  · have h12 : minor12 u 0 = 8 * u * u ^ 3 * (u + u ^ 6) := by
      dsimp [minor12]
      ring
    left
    rw [h12]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) hu) (pow_ne_zero 3 hu)) hU

/-- Algebraic witness that at least one of four derivative-minor
polynomials is nonzero at every nonzero real state. -/
theorem some_minor_nonzero (u v : ℝ) (hz : (u, v) ≠ (0, 0)) :
    minor13 u v ≠ 0 ∨ minor12 u v ≠ 0 ∨
    minor23 u v ≠ 0 ∨ minor14 u v ≠ 0 := by
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      intro hv
      apply hz
      simp [hu, hv]
    right
    right
    left
    simpa [hu] using at_u_zero v hv
  · by_cases hv : v = 0
    · obtain h | h := at_v_zero u hu
      · right
        left
        simpa [hv] using h
      · right
        right
        right
        simpa [hv] using h
    · left
      dsimp [minor13]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hu) hv

end SiphonFourProbeRegularity

#print axioms SiphonFourProbeRegularity.some_minor_nonzero
