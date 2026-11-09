import KerrKoopman.UniformGalerkinLimit
import KerrKoopman.AnalyticClassical
import KerrKoopman.AnalyticFieldTails
import KerrKoopman.AnalyticInitialTails

/-!
# An initial-data-only continuum certificate for the actual explicit formula

All PDE, regularity, Fourier tail and initial attainment obligations are
instantiated from the constructed analytic solution. The sole input is its
weighted initial coefficient datum, with norm at most 57/250, conjugate
symmetry, and a physical time interval of length at most 1/5. The formulas
below use the same real Fourier projection, scalar material inverse and
explicit shears for every datum in that class.
-/

namespace KerrKoopman.AnalyticGalerkinCertificate
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter AnalyticFields AnalyticLift FiniteRepresentatives
open GalerkinClassical AnalyticFieldTails AnalyticInitialTails
open scoped Topology Interval

/-- Actual Haar-normalized interval tail from the actual orthogonal-projection norm. -/
theorem normalized_tail_le (N : ℕ) (f : C(FiniteRepresentatives.Circle, ℝ))
    (A : ℝ) (hA : 0 ≤ A)
    (htail : ‖toL2 f-RealGalerkin.projection N (toL2 f)‖ ≤ A) :
    (∫ x in 0..IntervalFourier.period,
      (realLift f x-IntervalFourier.projection N (realLift f) x)^2)/IntervalFourier.period ≤ A^2 := by
  have hr : ‖RealGalerkin.projection N (toL2 f)-toL2 f‖ ≤ A := by
    simpa only [norm_sub_rev] using htail
  have hs : ‖RealGalerkin.projection N (toL2 f)-toL2 f‖^2 ≤ A^2 :=
    (sq_le_sq₀ (norm_nonneg _) hA).mpr hr
  calc
    _ = (∫ x in 0..IntervalFourier.period,
        (IntervalFourier.projection N (realLift f) x-realLift f x)^2)/IntervalFourier.period := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = ‖RealGalerkin.projection N (toL2 f)-toL2 f‖^2 :=
      (projection_error_sq_eq_interval N f).symm
    _ ≤ A^2 := hs

theorem initial_displacement_match (p : Data) (x : ℝ) :
    Riccati.constitutive ((AnalyticClassical.pair p).E 0 x) = realLift (initialCircleD p) x := by
  change Riccati.constitutive (AnalyticClassical.E p 0 x) = initialCircleD p (x : AnalyticTails.Circle)
  rw [show AnalyticClassical.E p 0 x = AnalyticFields.electric p (AnalyticInitial.zeroTime p) x from
    AnalyticClassical.E_eq p (AnalyticInitial.zeroTime p) x]
  change AnalyticFields.electric p (AnalyticInitial.zeroTime p) x +
    AnalyticFields.electric p (AnalyticInitial.zeroTime p) x ^ 3 / 3 = _
  rw [← material_identity, AnalyticInitial.displacement_initial, initialCircleD_coe]

theorem initial_magnetic_match (p : Data) :
    (AnalyticClassical.pair p).H 0 = realLift (initialCircleH p) := by
  funext x
  change AnalyticClassical.H p 0 x = initialCircleH p (x : AnalyticTails.Circle)
  rw [show AnalyticClassical.H p 0 x = AnalyticFields.magnetic p (AnalyticInitial.zeroTime p) x from
    AnalyticClassical.H_eq p (AnalyticInitial.zeroTime p) x]
  rw [AnalyticInitial.magnetic_initial, initialCircleH_coe]

theorem electric_match (p : Data) (t : ℝ) :
    (AnalyticClassical.pair p).E t = realLift (electricCircle p (AnalyticClassical.timeAt p t)) := by
  funext x
  exact (electricCircle_coe p (AnalyticClassical.timeAt p t) x).symm

theorem magnetic_match (p : Data) (t : ℝ) :
    (AnalyticClassical.pair p).H t = realLift (magneticCircle p (AnalyticClassical.timeAt p t)) := by
  funext x
  exact (magneticCircle_coe p (AnalyticClassical.timeAt p t) x).symm

theorem magnetic_derivative_match (p : Data) (t : ℝ) :
    (AnalyticClassical.pair p).Hx t =
      realLift (magneticDerivativeCircle p (AnalyticClassical.timeAt p t)) := by
  funext x
  exact (magneticDerivativeCircle_coe p (AnalyticClassical.timeAt p t) x).symm

/-- No PDE, tail, energy, or convergence assumption is supplied by the caller. -/
def control (p : Data) : ClassicalTailControl p.T (AnalyticClassical.pair p)
    (initialCircleD p) (initialCircleH p) where
  initial_D := initial_displacement_match p
  initial_H := initial_magnetic_match p
  continuous_E := AnalyticClassical.continuous_E p
  continuous_H := AnalyticClassical.continuous_H p
  continuous_Ex := AnalyticClassical.continuous_Ex p
  continuous_Hx := AnalyticClassical.continuous_Hx p
  bound_Hx t _ x _ := AnalyticClassical.Hx_bound p t x
  tail_Hx N t _ := by
    rw [magnetic_derivative_match]
    exact normalized_tail_le N _ _ (mul_nonneg (by norm_num) (cutoffDecay_pos N).le)
      (magnetic_derivative_projection_tail_two p (AnalyticClassical.timeAt p t) N)
  tail_E N t _ := by
    rw [electric_match]
    exact normalized_tail_le N _ _ (by positivity)
      (electric_projection_tail p (AnalyticClassical.timeAt p t) N)
  initial_tail_D := initialCircleD_tail p
  initial_tail_H := initialCircleH_tail p

/-- The displacement/magnetic initial state is reconstructed directly from the input coefficients. -/
def initialState (p : Data) : GalerkinFlow.Fields :=
  initialFields (initialCircleD p) (initialCircleH p)

/-- The actual electric/magnetic continuum field at physical time t. -/
def exactState (p : Data) (t : ℝ) : GalerkinFlow.Fields :=
  initialFields (electricCircle p (AnalyticClassical.timeAt p t))
    (magneticCircle p (AnalyticClassical.timeAt p t))

/-- A finite explicit shear formula, with no datum-dependent coordinate construction. -/
def finiteFormula (p : Data) (N n : ℕ) (t : ℝ) : GalerkinFlow.Fields :=
  approximation N n t (initialCircleD p) (initialCircleH p)

theorem actual_spatial_error (p : Data) (N : ℕ) (t : ℝ) (ht : t ∈ Icc 0 p.T) :
    ‖GalerkinFlow.decode N (GalerkinFlow.flow N t
      (GalerkinFlow.encode N (initialState p))) - exactState p t‖ ≤ 2*cutoffDecay N := by
  exact spatial_error_from_control p.T p.time_le (AnalyticClassical.pair p)
    (initialCircleD p) (initialCircleH p) (control p) N t _ _
    (electric_match p t) (magnetic_match p t) ht

/-- The explicit physical-time formula has a computable initial-only error budget. -/
theorem finiteFormula_error (p : Data) (N n : ℕ) (hn : 0<n) (t : ℝ) (ht : t ∈ Icc 0 p.T) :
    ‖finiteFormula p N n t-exactState p t‖ ≤
      2*cutoffDecay N+splittingNumerator N t ‖initialState p‖/n := by
  exact approximation_error_le p.T p.time_le (AnalyticClassical.pair p)
    (initialCircleD p) (initialCircleH p) (control p) N n hn t _ _
    (electric_match p t) (magnetic_match p t) ht

theorem joint_error (p : Data) (N : ℕ) (t : ℝ) (ht : t ∈ Icc 0 p.T) :
    ‖finiteFormula p N (jointSteps N t ‖initialState p‖) t-exactState p t‖ ≤
      2*cutoffDecay N+1/((N : ℝ)+1) := by
  exact joint_error_le p.T p.time_le (AnalyticClassical.pair p)
    (initialCircleD p) (initialCircleH p) (control p) N t _ _
    (electric_match p t) (magnetic_match p t) ht

/-- Actual convergence to the constructed nonlinear Maxwell field, including both time endpoints. -/
theorem finiteFormula_tendsto (p : Data) (t : ℝ) (ht : t ∈ Icc 0 p.T) :
    Tendsto (fun N => finiteFormula p N (jointSteps N t ‖initialState p‖) t)
      atTop (𝓝 (exactState p t)) := by
  exact joint_approximation_tendsto p.T p.time_le (AnalyticClassical.pair p)
    (initialCircleD p) (initialCircleH p) (control p) t _ _
    (electric_match p t) (magnetic_match p t) ht

/-- A single initial-only step count certifies every physical time in the closed interval. -/
theorem uniform_error (p : Data) (N : ℕ) (t : ℝ) (ht : t ∈ Icc 0 p.T) :
    ‖finiteFormula p N (jointSteps N p.T ‖initialState p‖) t-exactState p t‖ ≤
      2*cutoffDecay N+1/((N : ℝ)+1) := by
  exact fixed_steps_error_le p.T p.time_le (AnalyticClassical.pair p)
    (initialCircleD p) (initialCircleH p) (control p) N t _ _
    (electric_match p t) (magnetic_match p t) ht

/-- The actual explicit formula converges uniformly in physical time in the real L2 field norm. -/
theorem finiteFormula_tendstoUniformlyOn (p : Data) :
    TendstoUniformlyOn
      (fun N t => finiteFormula p N (jointSteps N p.T ‖initialState p‖) t)
      (exactState p) atTop (Icc 0 p.T) := by
  exact approximation_tendstoUniformlyOn p.T p.time_le (AnalyticClassical.pair p)
    (initialCircleD p) (initialCircleH p) (control p)
    (fun t => electricCircle p (AnalyticClassical.timeAt p t))
    (fun t => magneticCircle p (AnalyticClassical.timeAt p t))
    (fun t _ => electric_match p t) (fun t _ => magnetic_match p t)

end
end KerrKoopman.AnalyticGalerkinCertificate



