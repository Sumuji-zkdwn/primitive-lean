import Mathlib.Tactic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Non-Abelian Levi-Civita curvature from vacuum Taub--NUT gravity

Coordinate order (r, theta, phi, psi). The four-dimensional spatial metric is
  H (dr² + r² dtheta² + r² sin²(theta) dphi²)
    + H⁻¹ (dpsi + cos(theta) dphi)², H = 1 + 1/r.
This is the spatial factor of the 5D Ricci-flat KK monopole in draft PR #181.

X,Y,Z below are the actual matrices R^a_{bcd} for cd=(01),(02),(03)
at the regular basepoint r=1, theta=pi/2, computed independently by
tools/check_gh_holonomy.py from two derivatives of the metric. All matrix
entries are rational; this Lean file proves the resulting algebra, not the
metric-to-curvature differential-geometric derivation.

The metric's tangent-bundle SU(2) holonomy is not automatically a
dynamically independent 4D SU(2) Yang--Mills field.
-/

namespace RicciFlatSU2Holonomy

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℚ

/-- Metric at the chosen point, for coordinate tangent vectors. -/
def G : Mat4 := !![2, 0, 0, 0;
                    0, 2, 0, 0;
                    0, 0, 2, 0;
                    0, 0, 0, 1/2]

/-- Curvature R^a_{b 0 1}, obtained from the same Ricci-flat metric. -/
def X : Mat4 := !![0, -1/8, 0, 0;
                    1/8, 0, 0, 0;
                    0, 0, 0, 1/16;
                    0, 0, -1/4, 0]

/-- Curvature R^a_{b 0 2}. -/
def Y : Mat4 := !![0, 0, -1/8, 0;
                    0, 0, 0, -1/16;
                    1/8, 0, 0, 0;
                    0, 1/4, 0, 0]

/-- Curvature R^a_{b 0 3}. -/
def Z : Mat4 := !![0, 0, 0, 1/16;
                    0, 0, -1/8, 0;
                    0, 1/8, 0, 0;
                    -1/4, 0, 0, 0]

def commutator (U V : Mat4) : Mat4 := U * V - V * U

/-- The three independent curvature generators close a compact
    non-Abelian three-dimensional Lie algebra. -/
theorem bracket_XY :
    commutator X Y = (1 / 4 : ℚ) • Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutator, X, Y, Z, Matrix.mul_apply, Fin.sum_univ_succ]

theorem bracket_YZ :
    commutator Y Z = (1 / 4 : ℚ) • X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutator, X, Y, Z, Matrix.mul_apply, Fin.sum_univ_succ]

theorem bracket_ZX :
    commutator Z X = (1 / 4 : ℚ) • Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutator, X, Y, Z, Matrix.mul_apply, Fin.sum_univ_succ]

theorem commutator_nonzero : commutator X Y ≠ 0 := by
  intro h
  have h03 := congrArg (fun M : Mat4 => M 0 3) h
  rw [bracket_XY] at h03
  norm_num [Z, Matrix.smul_apply] at h03

/-- Riemann curvature endomorphisms respect the metric's skewness. -/
def MetricSkew (M : Mat4) : Prop := M.transpose * G + G * M = 0

theorem metric_skew_X : MetricSkew X := by
  unfold MetricSkew
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X, G, Matrix.mul_apply, Fin.sum_univ_succ]

theorem metric_skew_Y : MetricSkew Y := by
  unfold MetricSkew
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Y, G, Matrix.mul_apply, Fin.sum_univ_succ]

theorem metric_skew_Z : MetricSkew Z := by
  unfold MetricSkew
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Z, G, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Distinct curvature planes carry independent directions:
    these three matrices have linearly independent entries. -/
theorem independent_entries (a b c : ℚ)
    (h : a • X + b • Y + c • Z = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have h01 := congrArg (fun M : Mat4 => M 0 1) h
  have h02 := congrArg (fun M : Mat4 => M 0 2) h
  have h03 := congrArg (fun M : Mat4 => M 0 3) h
  have ha : a = 0 := by
    norm_num [X, Y, Z, Matrix.smul_apply, Matrix.add_apply] at h01
    linarith
  have hb : b = 0 := by
    norm_num [X, Y, Z, Matrix.smul_apply, Matrix.add_apply] at h02
    linarith
  have hc : c = 0 := by
    norm_num [X, Y, Z, Matrix.smul_apply, Matrix.add_apply] at h03
    linarith
  exact ⟨ha, hb, hc⟩

/-- The other three Riemann curvature planes, as rational
    consequences of the same one-point metric calculation. -/
def R12 : Mat4 := (-2 : ℚ) • Z
def R13 : Mat4 := (1 / 2 : ℚ) • Y
def R23 : Mat4 := (-1 / 2 : ℚ) • X

/-- The first entry of their nonzero bracket is exactly 1/64. -/
theorem measured_noncommutativity :
    (commutator X Y) 0 3 = (1 / 64 : ℚ) := by
  rw [bracket_XY]
  norm_num [Z, Matrix.smul_apply]


/-!
## A sharp boundary: the circle's KK gauge transformations remain Abelian

The one additional coordinate in the 5D ansatz is a circle. Frame changes
y -> y + alpha(x) act by additive U(1) gauge shifts on the 4D KK one-form.
They commute, even though its *separate* tangent-bundle spin holonomy is SU(2).
This is only a finite simplicial U(1) gauge model; no Lie-group integration
or 4D matter dynamics is claimed.
-/

abbrev CircleLink := Fin 3 → Fin 3 → ℚ

def circleGauge (alpha : Fin 3 → ℚ) (A : CircleLink) : CircleLink :=
  fun i j => A i j + alpha j - alpha i

theorem circle_gauge_commutative
    (alpha beta : Fin 3 → ℚ) (A : CircleLink) :
    circleGauge alpha (circleGauge beta A) =
      circleGauge beta (circleGauge alpha A) := by
  funext i j
  dsimp [circleGauge]
  ring

def triangleFlux (A : CircleLink) : ℚ :=
  A 0 1 + A 1 2 + A 2 0

theorem triangle_flux_gauge_invariant
    (alpha : Fin 3 → ℚ) (A : CircleLink) :
    triangleFlux (circleGauge alpha A) = triangleFlux A := by
  dsimp [triangleFlux, circleGauge]
  ring

theorem curvature_generators_not_commuting : X * Y ≠ Y * X := by
  intro h
  apply commutator_nonzero
  simp [commutator, h]

end RicciFlatSU2Holonomy
