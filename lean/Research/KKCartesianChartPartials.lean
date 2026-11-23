import Research.KKCartesianDerivative
import Mathlib.Tactic

/-!
# Every coordinate first derivative of the local five-dimensional metric

This is the 5D chart-level corollary of the structural HasDerivAt
proof in KKCartesianDerivative. The metric depends only on x and z:
t,y,psi derivatives vanish without being stipulated in a jet table.
Coordinates are (t,x,y,z,psi), with H(z)=1+a*z != 0.
-/
namespace KKCartesianChartPartials
open KKCartesianDerivative

noncomputable def metric5 (a : ℝ) (p : Fin 5 → ℝ)
    (i j : Fin 5) : ℝ := g a (p 1) (p 3) i j

def vary (p : Fin 5 → ℝ) (d : Fin 5) (w : ℝ) :
    Fin 5 → ℝ := fun k => if k = d then w else p k

noncomputable def expectedPartial (a : ℝ) (p : Fin 5 → ℝ)
    (d i j : Fin 5) : ℝ :=
  if d = 1 then ((E.dx a (metricE i j)).eval a (p 1) (p 3))
  else if d = 3 then ((E.dz a (metricE i j)).eval a (p 1) (p 3))
  else 0

/-- Single kernel theorem proving all 5 * 5 * 5 = 125 actual
coordinate partial derivatives, rather than accepting 125 jets. -/
theorem all_125_real_metric_partials (a : ℝ) (p : Fin 5 → ℝ)
    (hh : 1+a*(p 3) ≠ 0) (d i j : Fin 5) :
    HasDerivAt (fun w : ℝ => metric5 a (vary p d w) i j)
      (expectedPartial a p d i j) (p d) := by
  fin_cases d
  · simpa [metric5, vary, expectedPartial] using
      (hasDerivAt_const (p 0) (g a (p 1) (p 3) i j))
  · simpa [metric5, vary, expectedPartial] using
      (all_metric_x_derivatives a (p 1) (p 3) hh i j)
  · simpa [metric5, vary, expectedPartial] using
      (hasDerivAt_const (p 2) (g a (p 1) (p 3) i j))
  · simpa [metric5, vary, expectedPartial] using
      (all_metric_z_derivatives a (p 1) (p 3) hh i j)
  · simpa [metric5, vary, expectedPartial] using
      (hasDerivAt_const (p 4) (g a (p 1) (p 3) i j))

end KKCartesianChartPartials
