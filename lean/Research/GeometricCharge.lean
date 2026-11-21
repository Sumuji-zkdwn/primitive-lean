import Mathlib.Tactic

/-!
# Geometric charge: a minimal Kaluza--Klein algebraic witness

This module establishes exact algebraic identities for a common (1+1)-dimensional
base with an additional one-dimensional fibre. A nontrivial connection appears
as the mixed component of one higher-dimensional quadratic form.

The Einstein field equations, smooth curvature calculations, and derivation of
Euler--Lagrange equations are NOT proved in this file. See the independent
symbolic checker and the research note for the scope boundary.
-/

namespace GeometricCharge

/-- Signature (-,+) on the two-dimensional observed base. -/
def baseQuadratic (ut ux : ℚ) : ℚ := -ut * ut + ux * ux

/-- Connection one-form evaluated on a velocity. -/
def connection (at ax ut ux : ℚ) : ℚ := at * ut + ax * ux

/-- A single higher-dimensional quadratic form, with the extra fibre velocity uy. -/
def liftedQuadratic (at ax ut ux uy : ℚ) : ℚ :=
  baseQuadratic ut ux + (uy + connection at ax ut ux) ^ 2

/-- The fibre momentum is the connection-adjusted fibre velocity. -/
def fibreMomentum (at ax ut ux uy : ℚ) : ℚ :=
  uy + connection at ax ut ux

def lagrangian (at ax ut ux uy : ℚ) : ℚ :=
  liftedQuadratic at ax ut ux uy / 2

/-- Routh reduction after holding the fibre momentum q fixed. -/
def routhian (at ax q ut ux : ℚ) : ℚ :=
  baseQuadratic ut ux / 2 - q * q / 2 +
    q * connection at ax ut ux

theorem lifted_momentum (at ax q ut ux : ℚ) :
    fibreMomentum at ax ut ux (q - connection at ax ut ux) = q := by
  dsimp [fibreMomentum]
  ring

/-- Eliminating the unobserved fibre velocity yields minimal coupling. -/
theorem routh_identity (at ax q ut ux : ℚ) :
    lagrangian at ax ut ux (q - connection at ax ut ux) -
      q * (q - connection at ax ut ux) =
        routhian at ax q ut ux := by
  dsimp [lagrangian, liftedQuadratic, baseQuadratic, connection, routhian]
  ring

/-- Changing the connection by a gradient and shifting the fibre velocity
    preserves the whole quadratic form. -/
theorem gauge_invariant (at ax alpha beta ut ux uy : ℚ) :
    liftedQuadratic (at + alpha) (ax + beta) ut ux
      (uy - alpha * ut - beta * ux) =
        liftedQuadratic at ax ut ux uy := by
  dsimp [liftedQuadratic, baseQuadratic, connection]
  ring

/-- The absolute orientation of the unobserved fibre is not an observable. -/
theorem fibre_orientation_invariant (at ax ut ux uy : ℚ) :
    liftedQuadratic (-at) (-ax) ut ux (-uy) =
      liftedQuadratic at ax ut ux uy := by
  dsimp [liftedQuadratic, baseQuadratic, connection]
  ring

/-- An additive connection's holonomy around an oriented triangle. -/
def cycleHolonomy (e01 e12 e20 : ℚ) : ℚ := e01 + e12 + e20

/-- Local changes of fibre coordinates cancel around a closed loop. -/
theorem cycle_holonomy_gauge_invariant
    (e01 e12 e20 l0 l1 l2 : ℚ) :
    cycleHolonomy (e01 + l1 - l0)
      (e12 + l2 - l1) (e20 + l0 - l2) =
        cycleHolonomy e01 e12 e20 := by
  dsimp [cycleHolonomy]
  ring

/-- The time-time component of the higher-dimensional matrix for A_t = E x. -/
def timeBlock (E x : ℚ) : ℚ := (E * x) ^ 2 - 1

/-- The mixed time-fibre component of the same matrix. -/
def mixedBlock (E x : ℚ) : ℚ := E * x

/-- The diagonal part forgets the sign of E. -/
theorem diagonal_blind_to_sign (E x : ℚ) :
    timeBlock E x = timeBlock (-E) x := by
  dsimp [timeBlock]
  ring

/-- For a fixed fibre orientation, the mixed component can distinguish signs. -/
theorem mixed_detects_sign :
    mixedBlock 1 1 ≠ mixedBlock (-1) 1 := by
  norm_num [mixedBlock]

/-- Projected 'Lorentz-force' acceleration, as derived independently
    from the full geodesic and Euler--Lagrange equations. -/
def accelerateTime (q E ut ux : ℚ) : ℚ := q * E * ux

def accelerateSpace (q E ut ux : ℚ) : ℚ := q * E * ut

/-- q -> -q or E -> -E alone flips the acceleration. -/
theorem charge_reversal (q E ut ux : ℚ) :
    accelerateTime (-q) E ut ux = - accelerateTime q E ut ux ∧
    accelerateSpace (-q) E ut ux = - accelerateSpace q E ut ux := by
  constructor <;> dsimp [accelerateTime, accelerateSpace] <;> ring

/-- Simultaneously reversing fibre orientation and the charge preserves motion. -/
theorem joint_orientation_reversal (q E ut ux : ℚ) :
    accelerateTime (-q) (-E) ut ux = accelerateTime q E ut ux ∧
    accelerateSpace (-q) (-E) ut ux = accelerateSpace q E ut ux := by
  constructor <;> dsimp [accelerateTime, accelerateSpace] <;> ring

/-- The projected acceleration is tangent to a constant Minkowski-norm shell. -/
theorem projected_norm_derivative_zero (q E ut ux : ℚ) :
    -2 * ut * accelerateTime q E ut ux +
      2 * ux * accelerateSpace q E ut ux = 0 := by
  dsimp [accelerateTime, accelerateSpace]
  ring

/-- With q=0 the projected force vanishes. -/
theorem neutral_has_no_force (E ut ux : ℚ) :
    accelerateTime 0 E ut ux = 0 ∧
    accelerateSpace 0 E ut ux = 0 := by
  constructor <;> simp [accelerateTime, accelerateSpace]

/-- The 2+1 metric determinant for G=[[a²-1,0,a],[0,1,0],[a,0,1]]
    is -1. This checks nondegeneracy for every a. -/
theorem kk_determinant (a : ℚ) :
    (a ^ 2 - 1) * 1 - a * a = -1 := by
  ring

end GeometricCharge
