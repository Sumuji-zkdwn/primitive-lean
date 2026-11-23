import Research.KKCartesianJet
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Analytic first-jet bridge for a Cartesian 5D Kaluza--Klein metric

A syntax tree describes metric entries using H=1+a*z, U=a*x,
real constants, sums, products, negatives, and inverses.
The two recursive differentiation rules are proved with HasDerivAt
by structural induction. The 5D metric entries are analytic functions,
not stipulated jets. Local domain H != 0.
Second derivatives and full Ricci are not yet formalized here.
-/

namespace KKCartesianDerivative

inductive E where
  | const (v : ℝ)
  | H
  | U
  | add (l r : E)
  | mul (l r : E)
  | neg (e : E)
  | inv (e : E)

noncomputable def E.eval (a x z : ℝ) : E → ℝ
  | .const v => v
  | .H => 1 + a*z
  | .U => a*x
  | .add l r => l.eval a x z + r.eval a x z
  | .mul l r => l.eval a x z * r.eval a x z
  | .neg e => -(e.eval a x z)
  | .inv e => (e.eval a x z)⁻¹

def E.Good (a x z : ℝ) : E → Prop
  | .const _ => True
  | .H => True
  | .U => True
  | .add l r => l.Good a x z ∧ r.Good a x z
  | .mul l r => l.Good a x z ∧ r.Good a x z
  | .neg e => e.Good a x z
  | .inv e => e.Good a x z ∧ e.eval a x z ≠ 0

def E.dx (a : ℝ) : E → E
  | .const _ => .const 0
  | .H => .const 0
  | .U => .const a
  | .add l r => .add (l.dx a) (r.dx a)
  | .mul l r => .add (.mul (l.dx a) r) (.mul l (r.dx a))
  | .neg e => .neg (e.dx a)
  | .inv e => .neg (.mul (e.dx a) (.mul (.inv e) (.inv e)))

def E.dz (a : ℝ) : E → E
  | .const _ => .const 0
  | .U => .const 0
  | .H => .const a
  | .add l r => .add (l.dz a) (r.dz a)
  | .mul l r => .add (.mul (l.dz a) r) (.mul l (r.dz a))
  | .neg e => .neg (e.dz a)
  | .inv e => .neg (.mul (e.dz a) (.mul (.inv e) (.inv e)))

theorem E.hasDerivAt_x (a x z : ℝ) (e : E) (he : e.Good a x z) :
    HasDerivAt (fun w : ℝ => e.eval a w z) ((e.dx a).eval a x z) x := by
  induction e with
  | const v => simpa [E.eval, E.dx] using (hasDerivAt_const x v)
  | H => simpa [E.eval, E.dx] using (hasDerivAt_const x (1+a*z))
  | U => simpa [E.eval, E.dx] using ((hasDerivAt_id x).const_mul a)
  | add l r ihl ihr =>
      rcases he with ⟨hl,hr⟩
      convert (ihl hl).add (ihr hr) using 1 <;>
        simp [E.eval, E.dx, Pi.add_apply]
  | mul l r ihl ihr =>
      rcases he with ⟨hl,hr⟩
      convert (ihl hl).mul (ihr hr) using 1 <;>
        simp [E.eval, E.dx, Pi.mul_apply]
  | neg e ih => (by
        convert (ih he).neg using 1 <;>
          simp [E.eval, E.dx, Pi.neg_apply])
  | inv e ih =>
      rcases he with ⟨hw, hnz⟩
      convert (ih hw).fun_inv hnz using 1 <;>
        simp [E.eval, E.dx, div_eq_mul_inv, pow_two] <;> ring

theorem E.hasDerivAt_z (a x z : ℝ) (e : E) (he : e.Good a x z) :
    HasDerivAt (fun w : ℝ => e.eval a x w) ((e.dz a).eval a x z) z := by
  induction e with
  | const v => simpa [E.eval, E.dz] using (hasDerivAt_const z v)
  | H =>
      simpa [E.eval, E.dz] using (KKCartesianJet.affine_H_hasDerivAt a z)
  | U => simpa [E.eval, E.dz] using (hasDerivAt_const z (a*x))
  | add l r ihl ihr =>
      rcases he with ⟨hl,hr⟩
      convert (ihl hl).add (ihr hr) using 1 <;>
        simp [E.eval, E.dz, Pi.add_apply]
  | mul l r ihl ihr =>
      rcases he with ⟨hl,hr⟩
      convert (ihl hl).mul (ihr hr) using 1 <;>
        simp [E.eval, E.dz, Pi.mul_apply]
  | neg e ih => (by
        convert (ih he).neg using 1 <;>
          simp [E.eval, E.dz, Pi.neg_apply])
  | inv e ih =>
      rcases he with ⟨hw, hnz⟩
      convert (ih hw).fun_inv hnz using 1 <;>
        simp [E.eval, E.dz, div_eq_mul_inv, pow_two] <;> ring

abbrev Mat5 := Matrix (Fin 5) (Fin 5) E
def e0 : E := .const 0
def quotientH : E := .inv .H
def gaugeEntry : E := .mul .U quotientH
def yyEntry : E := .add .H (.mul (.mul .U .U) quotientH)

def metricE : Mat5 :=
  !![.const (-1),e0,e0,e0,e0;
     e0,.H,e0,e0,e0;
     e0,e0,yyEntry,e0,gaugeEntry;
     e0,e0,e0,.H,e0;
     e0,e0,gaugeEntry,e0,quotientH]

noncomputable def g (a x z : ℝ) (i j : Fin 5) : ℝ :=
  (metricE i j).eval a x z

theorem metric_good (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j : Fin 5) : (metricE i j).Good a x z := by
  fin_cases i <;> fin_cases j <;>
    simp [metricE, yyEntry, gaugeEntry, quotientH, e0,
      E.Good, E.eval, hh]

/-- All 25 x derivative entries, derived from the metric itself. -/
theorem all_metric_x_derivatives (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j : Fin 5) :
    HasDerivAt (fun w : ℝ => g a w z i j)
      ((E.dx a (metricE i j)).eval a x z) x := by
  exact E.hasDerivAt_x a x z (metricE i j) (metric_good a x z hh i j)

/-- All 25 z derivative entries, derived from the metric itself. -/
theorem all_metric_z_derivatives (a x z : ℝ) (hh : 1+a*z ≠ 0)
    (i j : Fin 5) :
    HasDerivAt (fun w : ℝ => g a x w i j)
      ((E.dz a (metricE i j)).eval a x z) z := by
  exact E.hasDerivAt_z a x z (metricE i j) (metric_good a x z hh i j)

end KKCartesianDerivative
