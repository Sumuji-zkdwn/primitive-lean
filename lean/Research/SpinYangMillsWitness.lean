import Mathlib.Tactic

/-!
# The self-dual 't Hooft symbol: finite algebraic core of a spin instanton

Finite identities for three oriented two-forms on four Euclidean directions.
These identities allow an SU(2) self-dual gauge curvature to be read from the
self-dual spin-connection sector of the round S4 geometry.

Not included in Lean: exterior calculus, the smooth round S4 spin connection,
the global SU(2) bundle, Yang--Mills PDE, or instanton number. Those are
verified at the level of local coordinate equations in the SymPy oracle.
-/

namespace SpinYangMillsWitness

/-- The 3 self-dual 't Hooft symbols on 4 Euclidean coordinates, with
    epsilon_{012}=+1 and eta_{a,a,3}=+1. -/
def eta (a : Fin 3) (i j : Fin 4) : ℤ :=
  if a = 0 then
    if (i = 1 ∧ j = 2) ∨ (i = 0 ∧ j = 3) then 1
    else if (i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 0) then -1 else 0
  else if a = 1 then
    if (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 3) then 1
    else if (i = 0 ∧ j = 2) ∨ (i = 3 ∧ j = 1) then -1 else 0
  else
    if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then 1
    else if (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2) then -1 else 0

theorem eta_skew : ∀ a i j, eta a i j = - eta a j i := by decide

theorem eta_diagonal_zero : ∀ a i, eta a i i = 0 := by decide

/-- Equivalence to *eta = eta: the three independent Hodge-star pairs. -/
theorem self_dual_pairs : ∀ a : Fin 3,
    eta a 0 1 = eta a 2 3 ∧
    eta a 0 2 = - eta a 1 3 ∧
    eta a 0 3 = eta a 1 2 := by decide

/-- Constant multiples of a self-dual 2-form stay self-dual. -/
theorem curvature_self_dual (c : ℤ) (a : Fin 3) :
    c * eta a 0 1 = c * eta a 2 3 ∧
    c * eta a 0 2 = - (c * eta a 1 3) ∧
    c * eta a 0 3 = c * eta a 1 2 := by
  rcases self_dual_pairs a with ⟨h1, h2, h3⟩
  constructor
  · rw [h1]
  constructor
  · rw [h2]; ring
  · rw [h3]

/-- Example of a genuinely nonzero component of the BPST curvature. -/
theorem spin_curvature_nontrivial : (-4 : ℤ) * eta 0 0 3 ≠ 0 := by
  norm_num [eta]

/-- Antisymmetry survives multiplication by the scalar curvature profile. -/
theorem scaled_skew (c : ℚ) (a : Fin 3) (i j : Fin 4) :
    c * (eta a i j : ℚ) = - c * (eta a j i : ℚ) := by
  have h := eta_skew a i j
  have hc : (eta a i j : ℚ) = - (eta a j i : ℚ) := by exact_mod_cast h
  rw [hc]
  ring

end SpinYangMillsWitness
