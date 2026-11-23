import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Taub--NUT centre: actual C-infinity Cartesian metric coefficients

The 4D spatial metric is, for alpha>=0,
  g_ij(X)=q(X) delta_ij + beta(X) w_i(X) w_j(X)
with q=1+alpha sum X_k^2 and beta=-alpha(2+alpha sum X_k^2)/q.
This module proves each coefficient is C^infinity on *all* R^4,
including the NUT centre X=0 (not merely a formal rational jet).
The topological claim that these X coordinates are the Hopf completion
of the original circle bundle requires a separate atlas theorem.
-/

namespace KKNutSmooth


abbrev X4 := Fin 4 → ℝ

/-- Squared radial coordinate. -/
def radialSq (X : X4) : ℝ := X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2

def warp (alpha : ℝ) (X : X4) : ℝ := 1 + alpha * radialSq X

def omegaComponent (X : X4) (i : Fin 4) : ℝ :=
  if i = 0 then -X 1 else if i = 1 then X 0
  else if i = 2 then -X 3 else X 2

noncomputable def fibreCoefficient (alpha : ℝ) (X : X4) : ℝ :=
  -(alpha * (2 + alpha * radialSq X)) / warp alpha X

noncomputable def metricEntry (alpha : ℝ) (X : X4) (i j : Fin 4) : ℝ :=
  (if i = j then warp alpha X else 0) +
  fibreCoefficient alpha X * omegaComponent X i * omegaComponent X j

private theorem smooth_coord (i : Fin 4) :
    ContDiff ℝ ⊤ (fun X : X4 => X i) :=
  contDiff_apply ℝ (fun _ : Fin 4 => ℝ) i

/-- The squared radius is smooth all the way to X=0. -/
theorem smooth_radialSq : ContDiff ℝ ⊤ radialSq := by
  unfold radialSq
  fun_prop

/-- The warp is a polynomial smooth function. -/
theorem smooth_warp (alpha : ℝ) : ContDiff ℝ ⊤ (warp alpha) := by
  unfold warp
  fun_prop

/-- All four coefficients of the global Hopf one-form are smooth. -/
theorem smooth_omegaComponent (i : Fin 4) :
    ContDiff ℝ ⊤ (fun X : X4 => omegaComponent X i) := by
  fin_cases i
  · simpa [omegaComponent] using (smooth_coord 1).neg
  · simpa [omegaComponent] using smooth_coord 0
  · simpa [omegaComponent] using (smooth_coord 3).neg
  · simpa [omegaComponent] using smooth_coord 2

/-- The warp never vanishes on R4 for alpha>=0. -/
theorem warp_pos (alpha : ℝ) (ha : 0 ≤ alpha) (X : X4) :
    0 < warp alpha X := by
  have hs : 0 ≤ radialSq X := by
    dsimp [radialSq]
    positivity
  have hmul : 0 ≤ alpha * radialSq X := mul_nonneg ha hs
  dsimp [warp]
  linarith

/-- The rational fibre coefficient is smooth globally, not just at
nonzero radial coordinates. -/
theorem smooth_fibreCoefficient (alpha : ℝ) (ha : 0 ≤ alpha) :
    ContDiff ℝ ⊤ (fibreCoefficient alpha) := by
  unfold fibreCoefficient
  apply ContDiff.div
  · fun_prop
  · exact smooth_warp alpha
  · intro X
    exact ne_of_gt (warp_pos alpha ha X)

/-- Every one of the sixteen Cartesian metric coefficients extends
smoothly across X=0; the metric entries are rational with nowhere-zero
denominator, not singular functions of rho=|X|. -/
theorem all_metric_entries_smooth (alpha : ℝ) (ha : 0 ≤ alpha) :
    ∀ i j : Fin 4,
      ContDiff ℝ ⊤ (fun X : X4 => metricEntry alpha X i j) := by
  intro i j
  have hterm := ((smooth_fibreCoefficient alpha ha).mul
      (smooth_omegaComponent i)).mul (smooth_omegaComponent j)
  by_cases hij : i = j
  · simpa [metricEntry, hij] using (smooth_warp alpha).add hterm
  · have hzero : ContDiff ℝ ⊤ (fun _ : X4 => (0 : ℝ)) := contDiff_const
    simpa [metricEntry, hij] using hzero.add hterm

/-- The centre of the completed Cartesian chart has Euclidean entries. -/
theorem centre_metric (alpha : ℝ) (i j : Fin 4) :
    metricEntry alpha (fun _ => 0) i j = if i = j then 1 else 0 := by
  simp [metricEntry, omegaComponent, warp, radialSq, fibreCoefficient]

end KKNutSmooth