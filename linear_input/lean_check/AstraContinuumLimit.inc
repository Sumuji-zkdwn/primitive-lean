/-!
# Initial-data-only continuum limit of the actual Fourier-Galerkin shears

The input is the proved common analytic ball, on a physical time interval
0 <= T <= 1/5. The scalar fields below satisfy the actual Kerr constitutive
law and Maxwell equations. Their real L2 representatives are the limit of
the finite shear formulas with a single initial-only step count for [0,T].
The spatial error has constants independent of the cutoff. The step count
depends on the cutoff; no cutoff-uniform C/n splitting estimate is asserted.
-/

namespace KerrKoopman.ContinuumLimit

noncomputable section

open Set Filter
open scoped Topology

abbrev Input := AnalyticFields.Data
abbrev Fields := GalerkinFlow.Fields

def electric (p : Input) (t x : ℝ) : ℝ := AnalyticClassical.E p t x
def displacement (p : Input) (t x : ℝ) : ℝ := AnalyticClassical.D p t x
def magnetic (p : Input) (t x : ℝ) : ℝ := AnalyticClassical.H p t x

/-- The input state is displacement/magnetic; the restored state is electric/magnetic. -/
def initialState (p : Input) : Fields := AnalyticGalerkinCertificate.initialState p
def solution (p : Input) (t : ℝ) : Fields := AnalyticGalerkinCertificate.exactState p t

/-- One count, determined before evaluation, works for every physical time in [0,T]. -/
def steps (p : Input) (N : ℕ) : ℕ :=
  GalerkinClassical.jointSteps N p.T ‖initialState p‖

def approximation (p : Input) (N : ℕ) (t : ℝ) : Fields :=
  AnalyticGalerkinCertificate.finiteFormula p N (steps p N) t

def spatialApproximation (p : Input) (N : ℕ) (t : ℝ) : Fields :=
  GalerkinFlow.decode N (GalerkinFlow.flow N t (GalerkinFlow.encode N (initialState p)))

def spatialBudget (N : ℕ) : ℝ := 2 * Real.exp (-(3 / 20 : ℝ) * ((N : ℝ) + 1))
def totalBudget (N : ℕ) : ℝ := spatialBudget N + 1 / ((N : ℝ) + 1)

theorem material_identity (p : Input) (t x : ℝ) :
    displacement p t x = electric p t x + electric p t x ^ 3 / 3 :=
  AnalyticFields.material_identity p (AnalyticClassical.timeAt p t) x

theorem displacement_initial (p : Input) (x : ℝ) :
    displacement p 0 x = AnalyticInitial.initialDisplacement p x := by
  exact (AnalyticClassical.D_eq p (AnalyticInitial.zeroTime p) x).trans
    (AnalyticInitial.displacement_initial p x)

theorem magnetic_initial (p : Input) (x : ℝ) :
    magnetic p 0 x = AnalyticInitial.initialMagnetic p x := by
  exact (AnalyticClassical.H_eq p (AnalyticInitial.zeroTime p) x).trans
    (AnalyticInitial.magnetic_initial p x)

theorem electric_initial (p : Input) (x : ℝ) :
    electric p 0 x = ExplicitMaterial.electricOfDisplacement
      (AnalyticInitial.initialDisplacement p x) := by
  exact (AnalyticClassical.E_eq p (AnalyticInitial.zeroTime p) x).trans
    (AnalyticInitial.electric_initial p x)

theorem displacement_time_derivative (p : Input) (t x : ℝ) (ht : t ∈ Ioo 0 p.T) :
    HasDerivAt (fun s => displacement p s x) (-AnalyticClassical.Hx p t x) t := by
  have he : (fun s => displacement p s x) =ᶠ[𝓝 t]
      (fun s => AnalyticPDE.displacementExtension p s x) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    let st : AnalyticLift.Time p.T := ⟨s, hs.1.le, hs.2.le⟩
    exact (AnalyticClassical.D_eq p st x).trans
      (AnalyticPDE.displacementExtension_eq p st x).symm
  have hd := (AnalyticPDE.displacement_time_derivative p t x ht).congr_of_eventuallyEq he
  have hc := AnalyticClassical.timeAt_eq p (⟨t, ht.1.le, ht.2.le⟩ : AnalyticLift.Time p.T)
  simpa only [AnalyticClassical.Hx, hc] using hd

/-- The PDE concerns the same scalar fields as the L2 restoration below. -/
theorem maxwell_equations (p : Input) (t x : ℝ) (ht : t ∈ Ioo 0 p.T) :
    deriv (fun s => displacement p s x) t = -deriv (magnetic p t) x ∧
    deriv (fun s => magnetic p s x) t = -deriv (electric p t) x := by
  constructor
  · change deriv (fun s => displacement p s x) t = -deriv (AnalyticClassical.H p t) x
    rw [(displacement_time_derivative p t x ht).deriv, (AnalyticClassical.H_space p t x).deriv]
  · change deriv (fun s => AnalyticClassical.H p s x) t = -deriv (AnalyticClassical.E p t) x
    rw [(AnalyticClassical.H_time p t x ht).deriv, (AnalyticClassical.E_space p t x).deriv]

theorem fields_periodic (p : Input) (t : ℝ) :
    Function.Periodic (electric p t) (2 * Real.pi) ∧
    Function.Periodic (displacement p t) (2 * Real.pi) ∧
    Function.Periodic (magnetic p t) (2 * Real.pi) :=
  AnalyticFields.fields_periodic p (AnalyticClassical.timeAt p t)

/-- The normed target is the actual real L2 synthesis of these electric/magnetic fields. -/
theorem solution_restoration (p : Input) (t : ℝ) :
    solution p t = GalerkinClassical.initialFields
      (AnalyticFieldTails.electricCircle p (AnalyticClassical.timeAt p t))
      (AnalyticFieldTails.magneticCircle p (AnalyticClassical.timeAt p t)) := rfl

theorem scalar_restoration (p : Input) (t x : ℝ) :
    AnalyticFieldTails.electricCircle p (AnalyticClassical.timeAt p t)
      (x : AnalyticTails.Circle) = electric p t x ∧
    AnalyticFieldTails.magneticCircle p (AnalyticClassical.timeAt p t)
      (x : AnalyticTails.Circle) = magnetic p t x :=
  ⟨AnalyticFieldTails.electricCircle_coe p (AnalyticClassical.timeAt p t) x,
    AnalyticFieldTails.magneticCircle_coe p (AnalyticClassical.timeAt p t) x⟩

theorem steps_pos (p : Input) (N : ℕ) : 0 < steps p N :=
  GalerkinClassical.jointSteps_pos N p.T ‖initialState p‖

theorem steps_tendsto (p : Input) : Tendsto (steps p) atTop atTop :=
  GalerkinClassical.jointSteps_tendsto p.T ‖initialState p‖

/-- This is the actual projected material map and the actual two-shear update. -/
theorem approximation_eq_iterate (p : Input) (N : ℕ) (t : ℝ) :
    approximation p N t = GalerkinFlow.decode N
      ((GalerkinFlow.step N (t / steps p N))^[steps p N]
        (GalerkinFlow.encode N (initialState p))) := rfl

theorem spatial_error (p : Input) (N : ℕ) (t : ℝ) (ht : t ∈ Icc 0 p.T) :
    ‖spatialApproximation p N t - solution p t‖ ≤ spatialBudget N := by
  exact AnalyticGalerkinCertificate.actual_spatial_error p N t ht

theorem approximation_error (p : Input) (N : ℕ) (t : ℝ) (ht : t ∈ Icc 0 p.T) :
    ‖approximation p N t - solution p t‖ ≤ totalBudget N := by
  exact AnalyticGalerkinCertificate.uniform_error p N t ht

theorem spatialBudget_tendsto : Tendsto spatialBudget atTop (𝓝 0) := by
  simpa only [mul_zero] using! GalerkinClassical.cutoffDecay_tendsto.const_mul 2

theorem totalBudget_tendsto : Tendsto totalBudget atTop (𝓝 0) := by
  simpa only [zero_add] using!
    spatialBudget_tendsto.add tendsto_one_div_add_atTop_nhds_zero_nat

/-- The full spatial Galerkin sequence converges uniformly on the closed time interval. -/
theorem spatial_tendsto_uniformly (p : Input) :
    TendstoUniformlyOn (spatialApproximation p) (solution p) atTop (Icc 0 p.T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [spatialBudget_tendsto.eventually (gt_mem_nhds hε)] with N hN
  intro t ht
  rw [dist_eq_norm, norm_sub_rev]
  exact (spatial_error p N t ht).trans_lt hN

/-- Both the cutoff and the initial-only time count tend to infinity. -/
theorem approximation_tendsto_uniformly (p : Input) :
    TendstoUniformlyOn (approximation p) (solution p) atTop (Icc 0 p.T) :=
  AnalyticGalerkinCertificate.finiteFormula_tendstoUniformlyOn p

/-- No solution, tail estimate, or convergence assumption is an input to this package. -/
structure Certificate (p : Input) : Prop where
  constitutive : ∀ t x, displacement p t x = electric p t x + electric p t x ^ 3 / 3
  initial_displacement : ∀ x, displacement p 0 x = AnalyticInitial.initialDisplacement p x
  initial_magnetic : ∀ x, magnetic p 0 x = AnalyticInitial.initialMagnetic p x
  pde : ∀ t x, t ∈ Ioo 0 p.T →
    deriv (fun s => displacement p s x) t = -deriv (magnetic p t) x ∧
    deriv (fun s => magnetic p s x) t = -deriv (electric p t) x
  spatial_bound : ∀ N t, t ∈ Icc 0 p.T →
    ‖spatialApproximation p N t - solution p t‖ ≤ spatialBudget N
  formula_bound : ∀ N t, t ∈ Icc 0 p.T →
    ‖approximation p N t - solution p t‖ ≤ totalBudget N
  joint_limit : TendstoUniformlyOn (approximation p) (solution p) atTop (Icc 0 p.T)

theorem certificate (p : Input) : Certificate p where
  constitutive := material_identity p
  initial_displacement := displacement_initial p
  initial_magnetic := magnetic_initial p
  pde := maxwell_equations p
  spatial_bound := spatial_error p
  formula_bound := approximation_error p
  joint_limit := approximation_tendsto_uniformly p

/-- A proved nonconstant mixed-wave datum, at the full allowed physical time. -/
def mixedInput : Input := AnalyticExample.data (1 / 5) (by norm_num) le_rfl

theorem mixed_initial_displacement (x : ℝ) :
    displacement mixedInput 0 x = 4 / 3 + (1 / 25) * Real.cos x := by
  exact (AnalyticClassical.D_eq mixedInput (AnalyticInitial.zeroTime mixedInput) x).trans
    (AnalyticExample.displacement_initial_wave (1 / 5) (by norm_num) le_rfl x)

theorem mixed_initial_magnetic (x : ℝ) :
    magnetic mixedInput 0 x = 3 / 10 + (3 / 100) * Real.sin x := by
  exact (AnalyticClassical.H_eq mixedInput (AnalyticInitial.zeroTime mixedInput) x).trans
    (AnalyticExample.magnetic_initial_wave (1 / 5) (by norm_num) le_rfl x)

theorem mixed_initial_nonconstant :
    displacement mixedInput 0 0 ≠ displacement mixedInput 0 Real.pi := by
  rw [mixed_initial_displacement, mixed_initial_displacement]
  norm_num

theorem mixed_certificate : Certificate mixedInput := certificate mixedInput

end
end KerrKoopman.ContinuumLimit
