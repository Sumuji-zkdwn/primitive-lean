import Research.KKCartesianDerivative
import Mathlib.Tactic

/-!
# Real analytic second-order local KK metric jets

The expression differentiation engine was already proved correct for
HasDerivAt in Research.KKCartesianDerivative. Here we show that
applying it once preserves every inverse side-condition, so a second
application is again a genuine real derivative. Every result is for
all 25 metric entries; no second-derivative tables are assumed.

This proves all (x,x),(x,z),(z,x),(z,z) second partials in the
local affine chart H=1+a*z != 0. Coordinates t,y,psi are absent.
The Ricci-contraction identity remains a separate theorem.
-/

namespace KKCartesianSecondJet
open KKCartesianDerivative

theorem good_dx (a x z : ℝ) (e : E) (he : e.Good a x z) :
    (E.dx a e).Good a x z := by
  induction e with
  | const _ => trivial
  | H => trivial
  | U => trivial
  | add l r ihl ihr => exact ⟨ihl he.1, ihr he.2⟩
  | mul l r ihl ihr =>
      exact ⟨⟨ihl he.1, he.2⟩, ⟨he.1, ihr he.2⟩⟩
  | neg e ih => exact ih he
  | inv e ih => exact ⟨ih he.1, ⟨he, he⟩⟩

theorem good_dz (a x z : ℝ) (e : E) (he : e.Good a x z) :
    (E.dz a e).Good a x z := by
  induction e with
  | const _ => trivial
  | H => trivial
  | U => trivial
  | add l r ihl ihr => exact ⟨ihl he.1, ihr he.2⟩
  | mul l r ihl ihr =>
      exact ⟨⟨ihl he.1, he.2⟩, ⟨he.1, ihr he.2⟩⟩
  | neg e ih => exact ih he
  | inv e ih => exact ⟨ih he.1, ⟨he, he⟩⟩

/-- Each of the following four theorems is universally quantified
over all 25 actual metric expressions in the fixed local chart. -/
theorem second_xx (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j : Fin 5) :
    HasDerivAt (fun w : ℝ => (E.dx a (metricE i j)).eval a w z)
      ((E.dx a (E.dx a (metricE i j))).eval a x z) x := by
  exact E.hasDerivAt_x a x z (E.dx a (metricE i j))
    (good_dx a x z (metricE i j) (metric_good a x z hh i j))

theorem second_zx (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j : Fin 5) :
    HasDerivAt (fun w : ℝ => (E.dx a (metricE i j)).eval a x w)
      ((E.dz a (E.dx a (metricE i j))).eval a x z) z := by
  exact E.hasDerivAt_z a x z (E.dx a (metricE i j))
    (good_dx a x z (metricE i j) (metric_good a x z hh i j))

theorem second_xz (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j : Fin 5) :
    HasDerivAt (fun w : ℝ => (E.dz a (metricE i j)).eval a w z)
      ((E.dx a (E.dz a (metricE i j))).eval a x z) x := by
  exact E.hasDerivAt_x a x z (E.dz a (metricE i j))
    (good_dz a x z (metricE i j) (metric_good a x z hh i j))

theorem second_zz (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j : Fin 5) :
    HasDerivAt (fun w : ℝ => (E.dz a (metricE i j)).eval a x w)
      ((E.dz a (E.dz a (metricE i j))).eval a x z) z := by
  exact E.hasDerivAt_z a x z (E.dz a (metricE i j))
    (good_dz a x z (metricE i j) (metric_good a x z hh i j))

end KKCartesianSecondJet
