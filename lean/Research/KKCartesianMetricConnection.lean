import Research.KKCartesianDerivative
import Research.KKCartesianGammaTable
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Metric-to-Levi-Civita bridge for the affine Cartesian 5D KK chart

This module does not assume a Christoffel table as geometric truth.
It forms its coefficients by contracting the analytically verified
first derivatives of the actual 5D metric, with an explicit inverse.
It then compares all 125 coefficients with the independent sparse
connection table used by KKCartesianRicci. All calculations are on
the H=1+a*z != 0 chart, and are rational-function identities.
The further bridge to full metric-derived Ricci will use second jets.
-/
namespace KKCartesianMetricConnection
open KKCartesianDerivative KKCartesianRicci

abbrev MatrixE := Matrix (Fin 5) (Fin 5) E

/-- Exact inverse entry expressions of the 5D KK metric. -/
def inverseE : MatrixE :=
  !![.const (-1),e0,e0,e0,e0;
     e0,quotientH,e0,e0,e0;
     e0,e0,quotientH,e0,E.neg gaugeEntry;
     e0,e0,e0,quotientH,e0;
     e0,e0,E.neg gaugeEntry,e0,yyEntry]

/-- Full 5x5 inverse matrix is derived by multiplication, with H nonzero. -/
set_option maxHeartbeats 0
theorem metric_inverse_all_entries (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j : Fin 5) :
    (∑ m : Fin 5, (metricE i m).eval a x z *
                     (inverseE m j).eval a x z) =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [metricE, inverseE, e0, quotientH, gaugeEntry, yyEntry,
      E.eval, Fin.sum_univ_succ] <;>
    field_simp [hh] <;> ring

/-- Genuine x and z metric derivative ASTs; other directions constant. -/
def partialMetricE (a : ℝ) (d i j : Fin 5) : E :=
  partialE a d (metricE i j)

/-- Christoffel expression directly contracted from the original metric. -/
noncomputable def gammaFromMetricE (a : ℝ) (i j k : Fin 5) : E :=
  emul (.const (1/2))
    (sum5 fun m =>
      emul (inverseE i m)
        (eadd (eadd (partialMetricE a j m k)
                     (partialMetricE a k m j))
              (eneg (partialMetricE a m j k))))

/-- Every one of the 125 metric-derived connection entries equals
the sparse formula from KKCartesianRicci. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
theorem all_125_gamma_entries_agree (a x z : ℝ)
    (hh : 1+a*z ≠ 0) (i j k : Fin 5) :
    (gammaFromMetricE a i j k).eval a x z =
      (gammaE a i j k).eval a x z := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [gammaFromMetricE, gammaE, gammaOrdered,
      partialMetricE, partialE, inverseE, metricE,
      sum5, eadd, emul, eneg, mulC, e0,
      quotientH, gaugeEntry, yyEntry, eu2, eh2,
      ehInv, ehInv2, ehInv3, E.dx, E.dz, E.eval] <;>
    field_simp [hh] <;> ring

end KKCartesianMetricConnection
