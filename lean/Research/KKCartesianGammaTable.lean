import Research.KKCartesianDerivative
import Mathlib.Tactic

/-!
# Explicit sparse Cartesian 5D KK Christoffel table and formal derivatives

All entries are expressions in H=1+a*z, U=a*x, with no metric-to-
connection claim implicit in the definitions. The separate
KKCartesianMetricConnection module proves the table equals the
Christoffel contraction of the actual analytic metric.
-/

namespace KKCartesianRicci
open KKCartesianDerivative

def ehInv : E := .inv .H
def ehInv2 : E := .mul ehInv ehInv
def ehInv3 : E := .mul ehInv2 ehInv
def eu2 : E := .mul .U .U
def eh2 : E := .mul .H .H
def mulC (c : ℝ) (e : E) : E := .mul (.const c) e
def eadd : E → E → E := E.add
def emul : E → E → E := E.mul
def eneg : E → E := E.neg

/-- All nonzero Γ^i_jk values, with j<=k. -/
noncomputable def gammaOrdered (a : ℝ) : ℕ → ℕ → ℕ → E
  | 1, 1, 3 => mulC (a/2) ehInv
  | 1, 2, 2 => eneg (mulC a (emul .U ehInv2))
  | 1, 2, 4 => eneg (mulC (a/2) ehInv2)
  | 2, 1, 2 => mulC (a/2) (emul .U ehInv2)
  | 2, 1, 4 => mulC (a/2) ehInv2
  | 2, 2, 3 => mulC (a/2) ehInv
  | 3, 1, 1 => eneg (mulC (a/2) ehInv)
  | 3, 2, 2 => mulC (a/2) (emul (eadd eu2 (eneg eh2)) ehInv3)
  | 3, 2, 4 => mulC (a/2) (emul .U ehInv3)
  | 3, 3, 3 => mulC (a/2) ehInv
  | 3, 4, 4 => mulC (a/2) ehInv3
  | 4, 1, 2 => mulC (a/2) (emul (eadd eh2 (eneg eu2)) ehInv2)
  | 4, 1, 4 => eneg (mulC (a/2) (emul .U ehInv2))
  | 4, 2, 3 => eneg (mulC a (emul .U ehInv))
  | 4, 3, 4 => eneg (mulC (a/2) ehInv)
  | _, _, _ => .const 0

noncomputable def gammaE (a : ℝ) (i j k : Fin 5) : E :=
  if j.val ≤ k.val then gammaOrdered a i.val j.val k.val
  else gammaOrdered a i.val k.val j.val

/-- Coordinate derivative applied to an expression in H,U. -/
def partialE (a : ℝ) (d : Fin 5) (e : E) : E :=
  if d = 1 then E.dx a e
  else if d = 3 then E.dz a e
  else .const 0

def sum5 (f : Fin 5 → E) : E :=
  eadd (eadd (f 0) (f 1)) (eadd (f 2) (eadd (f 3) (f 4)))


end KKCartesianRicci
