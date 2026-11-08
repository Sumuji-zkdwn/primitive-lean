import Mathlib

/-!
# Polynomial E for the siphon/interaction-body test

This is an algebraic polynomial automorphism, *not* a calibrated hydraulic
time step. It is the explicit 2-shear example already independently checked
in tools/check_orbit_trace.py, now formalized as an update with an invariant.

The old scalar energy E(x,y;u) is not silently identified with this map.
The example exhibits preservation of a nonconstant polynomial under
nontrivial iteration, without positing fluid motion as a primitive.
-/

namespace Elastica.SiphonPolynomialE

/-- Scalar quantity that remains constant under the polynomial update. -/
def I (z : ℝ × ℝ) : ℝ := z.2 + z.1 ^ 3

/-- Conjugate a polynomial shear by (u,v) ↦ (u,v+u³). -/
def E (z : ℝ × ℝ) : ℝ × ℝ :=
  let r := I z
  let x := z.1 + r ^ 2
  (x, r - x ^ 3)

/-- The polynomial I is preserved exactly, not merely approximately. -/
theorem I_E (z : ℝ × ℝ) : I (E z) = I z := by
  rcases z with ⟨u, v⟩
  dsimp [E, I]
  ring

/-- Repeated application of the same chosen interaction. -/
def iterate : ℕ → (ℝ × ℝ) → (ℝ × ℝ)
  | 0, z => z
  | n + 1, z => E (iterate n z)

/-- The same I is preserved for arbitrarily long finite operation words E^n. -/
theorem I_iterate (n : ℕ) (z : ℝ × ℝ) :
    I (iterate n z) = I z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change I (E (iterate n z)) = I z
      rw [I_E, ih]

/-- The Jacobian computed from the actual polynomial components has
the following algebraic determinant identity. Derivative formulas are
independently checked in tools/check_orbit_trace.py. -/
theorem jacobian_identity (u r x : ℝ) :
    (1 + 6 * u ^ 2 * r) * (1 - 6 * x ^ 2 * r) -
      (2 * r) * (3 * u ^ 2 - 3 * x ^ 2 * (1 + 6 * u ^ 2 * r)) = 1 := by
  ring

/-- Even at a point with I=1, E need not leave the state unchanged. -/
theorem nontrivial_step : E (1, 0) = (2, -7) := by
  norm_num [E, I]

end Elastica.SiphonPolynomialE

#print axioms Elastica.SiphonPolynomialE.I_E
#print axioms Elastica.SiphonPolynomialE.I_iterate
#print axioms Elastica.SiphonPolynomialE.jacobian_identity
