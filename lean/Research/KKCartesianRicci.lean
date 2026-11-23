import Research.KKCartesianDerivative
import Mathlib.Tactic

/-!
# Full 25-component Ricci certificate from an analytic first-jet connection table

The input of the ricciE definition is an explicit 5D Christoffel
connection table and its coordinate derivatives. The Ricci formula
is evaluated by Lean on each of the 25 entries.
The link between this table and the actual metric-defined Christoffel
symbol remains a separate proof obligation, NOT silently assumed.
Local domain H=1+a*z != 0.
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
def gammaOrdered (a : ℝ) : ℕ → ℕ → ℕ → E
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

def gammaE (a : ℝ) (i j k : Fin 5) : E :=
  if j.val ≤ k.val then gammaOrdered a i.val j.val k.val
  else gammaOrdered a i.val k.val j.val

/-- Coordinate derivative applied to an expression in H,U. -/
def partialE (a : ℝ) (d : Fin 5) (e : E) : E :=
  if d = 1 then E.dx a e
  else if d = 3 then E.dz a e
  else .const 0

def sum5 (f : Fin 5 → E) : E :=
  eadd (eadd (f 0) (f 1)) (eadd (f 2) (eadd (f 3) (f 4)))

/-- R_ij=Σ_c [∂c Γ^c_ij - ∂j Γ^c_ic +
                 Σ_d (Γ^c_ij Γ^d_cd - Γ^c_id Γ^d_jc)]. -/
def ricciTerm (a : ℝ) (i j c : Fin 5) : E :=
  eadd
    (eadd (partialE a c (gammaE a c i j))
          (eneg (partialE a j (gammaE a c i c))))
    (sum5 fun d =>
      eadd (emul (gammaE a c i j) (gammaE a d c d))
           (eneg (emul (gammaE a c i d) (gammaE a d j c))))

def ricciE (a : ℝ) (i j : Fin 5) : E :=
  sum5 (ricciTerm a i j)

/-- Full 25-entry Ricci cancellation from the symbolic connection
table. Proving that this table equals the metric-derived Levi-Civita
connection is still required for a metric-to-Ricci kernel theorem. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem all_25_ricci_entries_zero (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j : Fin 5) :
    (ricciE a i j).eval a x z = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [ricciE, ricciTerm, sum5, gammaE, gammaOrdered,
      partialE, mulC, eadd, emul, eneg, ehInv, ehInv2, ehInv3,
      eh2, eu2, E.dx, E.dz, E.eval] <;>
    field_simp [hh] <;> ring

end KKCartesianRicci
