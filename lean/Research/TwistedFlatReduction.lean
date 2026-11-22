import Mathlib.Tactic

/-!
# Twisted reduction of flat five-dimensional space

The 5D flat metric in cylindrical coordinates is
  -dt² + dz² + dr² + r²(dtheta + B dy)² + dy².
Completed squares expose a lower-dimensional geometric connection with
nonzero curvature after quotienting the helical fibre. These are exact
rational polynomial identities, not Lean proofs of Ricci flatness (which is
checked independently by a Cartesian coordinate pullback).
-/

namespace TwistedFlatReduction

/-- Squared length of the helical circle fibre. -/
def lambda (B r : ℚ) : ℚ := 1 + (B * r) ^ 2

theorem lambda_positive (B r : ℚ) : 0 < lambda B r := by
  dsimp [lambda]
  positivity

/-- The KK square-completion identity after clearing the positive denominator. -/
theorem helical_square_completion (B r dtheta dy : ℚ) :
    lambda B r * (dy ^ 2 + r ^ 2 * (dtheta + B * dy) ^ 2) =
      r ^ 2 * dtheta ^ 2 +
      (lambda B r * dy + B * r ^ 2 * dtheta) ^ 2 := by
  dsimp [lambda]
  ring

/-- The connection induced by the helix, with the physicist's factor-of-two
    gauge normalization *not* included. -/
def connectionTheta (B r : ℚ) : ℚ := B * r ^ 2 / lambda B r

/-- The r-theta component of d(connectionTheta dtheta). -/
def curvatureRTheta (B r : ℚ) : ℚ :=
  2 * B * r / (lambda B r) ^ 2

theorem connection_relation (B r : ℚ) :
    lambda B r * connectionTheta B r = B * r ^ 2 := by
  have h : lambda B r ≠ 0 := ne_of_gt (lambda_positive B r)
  unfold connectionTheta
  field_simp

theorem curvature_relation (B r : ℚ) :
    (lambda B r) ^ 2 * curvatureRTheta B r = 2 * B * r := by
  have h : lambda B r ≠ 0 := ne_of_gt (lambda_positive B r)
  unfold curvatureRTheta
  field_simp

theorem nonzero_induced_curvature : curvatureRTheta 1 1 = 1 / 2 := by
  norm_num [curvatureRTheta, lambda]

theorem zero_twist_zero_curvature (r : ℚ) : curvatureRTheta 0 r = 0 := by
  simp [curvatureRTheta]

theorem circle_size_changes : lambda 1 1 ≠ lambda 1 2 := by
  norm_num [lambda]

theorem twist_sign_reverses_field (B r : ℚ) :
    curvatureRTheta (-B) r = - curvatureRTheta B r := by
  have h : lambda (-B) r = lambda B r := by
    dsimp [lambda]
    ring
  unfold curvatureRTheta
  rw [h]
  ring

end TwistedFlatReduction
