import Mathlib.Tactic
import Research.FiniteConnectionCurvature

/-!
# Curvature core regression: a genuinely non-flat two-dimensional metric

On an open coordinate patch consider the warped Riemannian metric

    ds² = dx² + (1+x²)² dy².

At x=1 its metric is diag(1,4). The Levi-Civita connection and
first partials, independently derived in the companion SymPy script,
have the following finite rational values:

  Γ^1_{01}=Γ^1_{10}=1,   Γ^0_{11}=-4,
  ∂_0 Γ^0_{11}=-8,

with all other entries/first partials zero. A genuine curvature
contraction then gives Ric=diag(-1,-4)=-g at that point.

Lean proves the *algebraic substitution and contraction*. It does NOT
yet prove that these input coefficient tables come from the metric's
Levi-Civita derivative; the companion oracle checks that separately.
-/

namespace FiniteConnectionWitness

open FiniteConnectionCurvature

def metricAt1 (a b : Fin 2) : ℚ :=
  if a = b then (if a = 0 then 1 else 4) else 0

def warpConnection (i a b : Fin 2) : ℚ :=
  if i = 0 ∧ a = 1 ∧ b = 1 then 1
  else if i = 1 ∧ a = 0 ∧ b = 1 then -4
  else if i = 1 ∧ a = 1 ∧ b = 0 then 1
  else 0

/-- dΓᵢⱼᵃ_b: derivative in direction i of Γⱼᵃ_b at x=1. -/
def warpFirstJet (i j a b : Fin 2) : ℚ :=
  if i = 0 ∧ j = 1 ∧ a = 0 ∧ b = 1 then -8 else 0

/-- The full Ricci contraction equals -g in all four components. -/
theorem warped_ricci_eq_negative_metric (i j : Fin 2) :
    ricci warpConnection warpFirstJet i j = -metricAt1 i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [ricci, curvature, warpConnection, warpFirstJet,
      metricAt1, Fin.sum_univ_succ]

/-- This point is not flat: a specific Riemann component is -4. -/
theorem warped_riemann_nonzero :
    curvature warpConnection warpFirstJet 0 1 0 1 = (-4 : ℚ) := by
  norm_num [curvature, warpConnection, warpFirstJet,
    Fin.sum_univ_succ]

end FiniteConnectionWitness
