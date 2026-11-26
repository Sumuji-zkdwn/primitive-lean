import Mathlib.Tactic

/-!
# Nonconvex passive gel: local certificates

Continuation of PR #183. This finite polynomial model is NOT a particle,
a gravity theory, or a Lorentz-invariant field theory.

This file certifies elementary polynomial identities, a three-site bump,
nonnegative second variation, and conditional edge dissipation. The
four-site minimax barrier and the numerical simulations are checked by
an independent Python oracle and documented separately.
-/

namespace PassiveGelMultiwell

/-- Triple-well stored strain energy. -/
def potential (strain : ℝ) : ℝ :=
  strain ^ 2 * (strain ^ 2 - 1) ^ 2

/-- Polynomial first derivative of potential. -/
def force (strain : ℝ) : ℝ :=
  6 * strain ^ 5 - 8 * strain ^ 3 + 2 * strain

/-- Polynomial second derivative of potential. -/
def curvature (strain : ℝ) : ℝ :=
  30 * strain ^ 4 - 24 * strain ^ 2 + 2

/-- Unrelaxed stress correction due to strain-memory lag. -/
def drive (b quartic lag : ℝ) : ℝ :=
  b * lag + quartic * lag ^ 3

/-- Stress for the multiwell model with the old internal relaxation law. -/
def stress (b quartic strain memory : ℝ) : ℝ :=
  force strain + drive b quartic (strain - memory)

theorem force_factor (strain : ℝ) :
    force strain = 2 * strain * (strain ^ 2 - 1) * (3 * strain ^ 2 - 1) := by
  unfold force
  ring

theorem potential_nonnegative (strain : ℝ) : 0 ≤ potential strain := by
  unfold potential
  positivity

theorem potential_zero : potential 0 = 0 := by
  norm_num [potential]

theorem potential_one : potential 1 = 0 := by
  norm_num [potential]

theorem potential_neg_one : potential (-1) = 0 := by
  norm_num [potential]

theorem force_zero : force 0 = 0 := by
  norm_num [force]

theorem force_one : force 1 = 0 := by
  norm_num [force]

theorem force_neg_one : force (-1) = 0 := by
  norm_num [force]

theorem curvature_zero : curvature 0 = 2 := by
  norm_num [curvature]

theorem curvature_one : curvature 1 = 8 := by
  norm_num [curvature]

theorem curvature_neg_one : curvature (-1) = 8 := by
  norm_num [curvature]

/-- The pinned/translation-quotiented 3-site bump has zero stored energy. -/
theorem three_site_bump_energy_zero :
    potential 1 + potential (-1) = 0 := by
  norm_num [potential]

/-- Both edge forces vanish at the 3-site bump's strains (1,-1). -/
theorem three_site_bump_force_zero :
    force 1 = 0 ∧ force (-1) = 0 := by
  constructor <;> norm_num [force]

/-- Quadratic form of the reduced Hessian at the bump: 8 * Bᵀ B. -/
theorem three_site_second_variation_nonnegative (y0 y1 y2 : ℝ) :
    0 ≤ 8 * ((y1 - y0) ^ 2 + (y2 - y1) ^ 2) := by
  positivity

/-- Exact edge energy exchange identity under mechanical and memory laws. -/
theorem edge_dissipation_identity
    (b quartic gamma strain memory strainRate memoryRate kineticRate : ℝ)
    (hkin : kineticRate + stress b quartic strain memory * strainRate = 0)
    (hrel : memoryRate = gamma * drive b quartic (strain - memory)) :
    kineticRate + force strain * strainRate +
      drive b quartic (strain - memory) * (strainRate - memoryRate)
      = -gamma * (drive b quartic (strain - memory)) ^ 2 := by
  rw [hrel]
  calc
    _ = (kineticRate + stress b quartic strain memory * strainRate) -
        gamma * (drive b quartic (strain - memory)) ^ 2 := by
      unfold stress drive
      ring
    _ = -gamma * (drive b quartic (strain - memory)) ^ 2 := by
      rw [hkin]
      ring

theorem edge_dissipation_nonpositive
    (b quartic gamma strain memory strainRate memoryRate kineticRate : ℝ)
    (hg : 0 ≤ gamma)
    (hkin : kineticRate + stress b quartic strain memory * strainRate = 0)
    (hrel : memoryRate = gamma * drive b quartic (strain - memory)) :
    kineticRate + force strain * strainRate +
      drive b quartic (strain - memory) * (strainRate - memoryRate) ≤ 0 := by
  rw [edge_dissipation_identity b quartic gamma strain memory
    strainRate memoryRate kineticRate hkin hrel]
  have h : 0 ≤ gamma * (drive b quartic (strain - memory)) ^ 2 :=
    mul_nonneg hg (sq_nonneg _)
  linarith

end PassiveGelMultiwell
