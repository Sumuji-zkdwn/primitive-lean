import Research.KKCartesianGammaTable
import Mathlib.Tactic

/-!
# All 25 Ricci components from a finite Christoffel table.
The gamma table's metric-to-connection proof lives in
KKCartesianMetricConnection. The present theorem is a direct
kernel-checked Ricci contraction of that table, if CI succeeds.
-/
namespace KKCartesianRicci
open KKCartesianDerivative

/-- R_ij=Σ_c [∂c Γ^c_ij - ∂j Γ^c_ic +
                 Σ_d (Γ^c_ij Γ^d_cd - Γ^c_id Γ^d_jc)]. -/
noncomputable def ricciTerm (a : ℝ) (i j c : Fin 5) : E :=
  eadd
    (eadd (partialE a c (gammaE a c i j))
          (eneg (partialE a j (gammaE a c i c))))
    (sum5 fun d =>
      eadd (emul (gammaE a c i j) (gammaE a d c d))
           (eneg (emul (gammaE a c i d) (gammaE a d j c))))

noncomputable def ricciE (a : ℝ) (i j : Fin 5) : E :=
  sum5 (ricciTerm a i j)

/-- Full 25-entry Ricci cancellation from the symbolic connection
table. Proving that this table equals the metric-derived Levi-Civita
connection is still required for a metric-to-Ricci kernel theorem. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
theorem all_25_ricci_entries_zero (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j : Fin 5) :
    (ricciE a i j).eval a x z = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [ricciE, ricciTerm, sum5, gammaE, gammaOrdered,
      partialE, mulC, eadd, emul, eneg, ehInv, ehInv2, ehInv3,
      eh2, eu2, E.dx, E.dz, E.eval] <;>
    field_simp [hh] <;> ring

end KKCartesianRicci
