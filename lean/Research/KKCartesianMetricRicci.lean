import Research.KKCartesianSecondJet
import Research.KKCartesianMetricConnection
import Research.KKCartesianRicci
import Mathlib.Tactic

/-!
# Completing the analytic 5D metric -> Christoffel -> Ricci bridge

A local theorem for the affine Cartesian KK metric H=1+a*z, U=a*x,
on H != 0. We use the already kernel-verified complete first jets,
exact matrix inverse and all 125 metric-to-connection component
identities. The expression derivative theorem supplies genuine real
derivatives of both connection expressions.

The final theorem below aims to transfer the 25 zero Ricci components
from the independently checked sparse Gamma table to Christoffels
directly derived from the original 5D metric. It is not a formal
theorem about arbitrary 5D Lorentzian metrics or global compactification.
-/

namespace KKCartesianMetricRicci
open KKCartesianDerivative KKCartesianRicci KKCartesianMetricConnection
open KKCartesianSecondJet
open Filter

theorem inverse_good (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j : Fin 5) : (inverseE i j).Good a x z := by
  fin_cases i <;> fin_cases j <;>
    simp [inverseE, e0, quotientH, gaugeEntry, yyEntry,
      E.Good, E.eval, hh]

theorem partial_metric_good (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (d i j : Fin 5) : (partialMetricE a d i j).Good a x z := by
  by_cases h1 : d = 1
  · simpa [partialMetricE, partialE, h1] using
      (good_dx a x z (metricE i j) (metric_good a x z hh i j))
  · by_cases h3 : d = 3
    · simpa [partialMetricE, partialE, h1, h3] using
        (good_dz a x z (metricE i j) (metric_good a x z hh i j))
    · simp [partialMetricE, partialE, h1, h3, E.Good]

theorem gamma_metric_good (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j k : Fin 5) : (gammaFromMetricE a i j k).Good a x z := by
  simp [gammaFromMetricE, sum5, emul, eadd, eneg, E.Good,
    inverse_good a x z hh, partial_metric_good a x z hh]

theorem gamma_table_good (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j k : Fin 5) : (gammaE a i j k).Good a x z := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [gammaE, gammaOrdered, mulC, eadd, emul, eneg,
      ehInv, ehInv2, ehInv3, eh2, eu2, E.Good, E.eval, hh]

/-- Differentiating the actual metric-derived connection in x gives
the same result as differentiating the explicit Gamma table. -/
theorem gamma_dx_agree (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j k : Fin 5) :
    (E.dx a (gammaFromMetricE a i j k)).eval a x z =
      (E.dx a (gammaE a i j k)).eval a x z := by
  have hm := E.hasDerivAt_x a x z (gammaFromMetricE a i j k)
    (gamma_metric_good a x z hh i j k)
  have ht := E.hasDerivAt_x a x z (gammaE a i j k)
    (gamma_table_good a x z hh i j k)
  have heq :
    (fun w : ℝ => (gammaFromMetricE a i j k).eval a w z) =
      (fun w : ℝ => (gammaE a i j k).eval a w z) := by
    funext w
    exact all_125_gamma_entries_agree a w z hh i j k
  calc
    _ = deriv (fun w : ℝ => (gammaFromMetricE a i j k).eval a w z) x :=
      hm.deriv.symm
    _ = deriv (fun w : ℝ => (gammaE a i j k).eval a w z) x := by rw [heq]
    _ = _ := ht.deriv

/-- z differentiation uses pointwise equality in a neighborhood
where H stays nonzero. This avoids assuming a derivative table. -/
theorem gamma_dz_agree (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j k : Fin 5) :
    (E.dz a (gammaFromMetricE a i j k)).eval a x z =
      (E.dz a (gammaE a i j k)).eval a x z := by
  have hm := E.hasDerivAt_z a x z (gammaFromMetricE a i j k)
    (gamma_metric_good a x z hh i j k)
  have ht := E.hasDerivAt_z a x z (gammaE a i j k)
    (gamma_table_good a x z hh i j k)
  have hc : ContinuousAt (fun w : ℝ => 1+a*w) z := by fun_prop
  have hn : ∀ᶠ w in nhds z, 1+a*w ≠ 0 := hc.eventually_ne hh
  have heq :
      (fun w : ℝ => (gammaFromMetricE a i j k).eval a x w) =ᶠ[nhds z]
      (fun w : ℝ => (gammaE a i j k).eval a x w) := by
    filter_upwards [hn] with w hw
    exact all_125_gamma_entries_agree a x w hw i j k
  have htransfer : HasDerivAt
      (fun w : ℝ => (gammaFromMetricE a i j k).eval a x w)
      ((E.dz a (gammaE a i j k)).eval a x z) z :=
    ht.congr_of_eventuallyEq heq
  exact hm.deriv.symm.trans htransfer.deriv

/-- Agreement of any one of the five coordinate partials. -/
theorem partial_gamma_agree (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (d i j k : Fin 5) :
    (partialE a d (gammaFromMetricE a i j k)).eval a x z =
      (partialE a d (gammaE a i j k)).eval a x z := by
  fin_cases d
  · simp [partialE, E.eval]
  · simpa [partialE] using (gamma_dx_agree a x z hh i j k)
  · simp [partialE, E.eval]
  · simpa [partialE] using (gamma_dz_agree a x z hh i j k)
  · simp [partialE, E.eval]

/-- Ricci directly constructed from the Christoffels of the metric. -/
noncomputable def ricciMetricTerm (a : ℝ) (i j c : Fin 5) : E :=
  eadd
    (eadd (partialE a c (gammaFromMetricE a c i j))
          (eneg (partialE a j (gammaFromMetricE a c i c))))
    (sum5 fun d =>
      eadd (emul (gammaFromMetricE a c i j) (gammaFromMetricE a d c d))
           (eneg (emul (gammaFromMetricE a c i d) (gammaFromMetricE a d j c))))

noncomputable def ricciFromMetricE (a : ℝ) (i j : Fin 5) : E :=
  sum5 (ricciMetricTerm a i j)

/-- All 25 analytic coordinate Ricci contractions coincide with
the sparse-table contractions, including every off-diagonal entry. -/
theorem ricci_from_metric_eq_table (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j : Fin 5) :
    (ricciFromMetricE a i j).eval a x z = (ricciE a i j).eval a x z := by
  simp [ricciFromMetricE, ricciE, ricciMetricTerm, ricciTerm,
    sum5, eadd, emul, eneg, E.eval,
    all_125_gamma_entries_agree a x z hh,
    partial_gamma_agree a x z hh]

/-- Complete local metric-to-Ricci-flatness statement for the
specified non-spherical affine Cartesian Kaluza--Klein metric. -/
theorem all_25_metric_ricci_zero (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j : Fin 5) :
    (ricciFromMetricE a i j).eval a x z = 0 := by
  rw [ricci_from_metric_eq_table a x z hh i j]
  exact all_25_ricci_entries_zero a x z hh i j

end KKCartesianMetricRicci
