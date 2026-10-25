import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith

/-! A scalar second-order necessary condition used for actual constrained
energy paths.  The second derivative is a derivative of the actual function,
not an independently assumed quadratic form. -/

noncomputable section
open Filter
open scoped Topology
namespace Elastica

/-- The second derivative of a continuous scalar function at a local minimum
is nonnegative, whenever that derivative exists. -/
theorem second_derivative_nonneg_of_local_min {f : ℝ → ℝ} {x q : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x)
    (hsecond : HasDerivAt (deriv f) q x) : 0 ≤ q := by
  by_contra h
  have hq : q < 0 := lt_of_not_ge h
  have hmax : IsLocalMax f x := isLocalMax_of_deriv_deriv_neg
    (by rw [hsecond.deriv]; exact hq) hmin.deriv_eq_zero hc
  have heq : f =ᶠ[nhds x] fun _ => f x := by
    filter_upwards [hmin, hmax] with y hy hy'
    exact le_antisymm hy' hy
  have hz : deriv (deriv f) x = 0 := by
    simpa using heq.deriv.deriv_eq
  rw [hsecond.deriv] at hz
  linarith

end Elastica
