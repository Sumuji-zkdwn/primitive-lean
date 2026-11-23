import Mathlib.Tactic
import Research.KKNutCartesian

/-!
# Positive-definite Cartesian one-centre Taub--NUT metric, as a quadratic form
Proves the Hopf omega contraction satisfies Cauchy-Schwarz using a
six-square Lagrange identity, then proves the actual metric form
q |v|² + beta omega(v)² is strictly positive for |v|²>0.
This is not, on its own, a quotient-bundle atlas.
-/
namespace KKNutQuadraticPositive
abbrev V4 := Fin 4 → ℝ

def radiusSq (X : V4) : ℝ := X 0^2+X 1^2+X 2^2+X 3^2
def omega (X V : V4) : ℝ :=
  -(X 1)*V 0+X 0*V 1-X 3*V 2+X 2*V 3
def w (X : V4) : V4 := fun i =>
  if i=0 then -X 1 else if i=1 then X 0
  else if i=2 then -X 3 else X 2

theorem omega_lagrange (X V : V4) :
    radiusSq X*radiusSq V-(omega X V)^2 =
      (w X 0*V 1-w X 1*V 0)^2 +
      (w X 0*V 2-w X 2*V 0)^2 +
      (w X 0*V 3-w X 3*V 0)^2 +
      (w X 1*V 2-w X 2*V 1)^2 +
      (w X 1*V 3-w X 3*V 1)^2 +
      (w X 2*V 3-w X 3*V 2)^2 := by
  unfold radiusSq omega w
  ring

theorem omega_cauchy (X V : V4) :
    (omega X V)^2 ≤ radiusSq X*radiusSq V := by
  have hs : 0 ≤ radiusSq X*radiusSq V-(omega X V)^2 := by
    rw [omega_lagrange]
    positivity
  exact sub_nonneg.mp hs

noncomputable def metricQuadratic (alpha : ℝ) (X V : V4) : ℝ :=
  KKNutCartesian.q alpha (radiusSq X)*radiusSq V +
  KKNutCartesian.beta alpha (radiusSq X)*(omega X V)^2

theorem metric_ge_euclidean_over_warp (alpha : ℝ)
    (ha : 0 ≤ alpha) (X V : V4) :
    radiusSq V / KKNutCartesian.q alpha (radiusSq X) ≤
      metricQuadratic alpha X V := by
  have hx : 0 ≤ radiusSq X := by unfold radiusSq; positivity
  have hc : (omega X V)^2 ≤ radiusSq X*radiusSq V := omega_cauchy X V
  exact KKNutCartesian.quadratic_lower_bound alpha (radiusSq X)
    (radiusSq V) (omega X V) ha hx hc

theorem metric_strict_positive (alpha : ℝ) (ha : 0 ≤ alpha)
    (X V : V4) (hv : 0 < radiusSq V) :
    0 < metricQuadratic alpha X V := by
  have hx : 0 ≤ radiusSq X := by unfold radiusSq; positivity
  have hq := (KKNutCartesian.eigenvalues_positive alpha (radiusSq X) ha hx).1
  have hlo := metric_ge_euclidean_over_warp alpha ha X V
  exact lt_of_lt_of_le (div_pos hv hq) hlo

end KKNutQuadraticPositive
