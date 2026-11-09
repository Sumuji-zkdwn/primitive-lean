
/-! Concrete circle fields and actual exponential projection budgets for the
constructed initial-data-only nonlinear Maxwell solution. -/

namespace KerrKoopman.AnalyticFieldTails
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory AnalyticFields AnalyticLift AnalyticAssembly AnalyticTails AnalyticTraceTails
open Phase3WeightedRealDecode GalerkinClassical FiniteRepresentatives

def electricCircle (p : Data) (t : Time p.T) : C(AnalyticTails.Circle, ℝ) :=
  ContinuousMap.const _ 1 + realCircleSum (traceCoeff (width p.T t) (eTrace p) t)

def magneticCircle (p : Data) (t : Time p.T) : C(AnalyticTails.Circle, ℝ) :=
  ContinuousMap.const _ (3/10) + realCircleSum (traceCoeff (width p.T t) (hTrace p) t)

def magneticDerivativeCircle (p : Data) (t : Time p.T) : C(AnalyticTails.Circle, ℝ) :=
  realCircleSum (derivativeCoeff (width p.T t) (hTrace p) t)

theorem electricCircle_coe (p : Data) (t : Time p.T) (x : ℝ) :
    electricCircle p t (x : AnalyticTails.Circle) = electric p t x := by
  simp only [electricCircle, ContinuousMap.add_apply, ContinuousMap.const_apply,
    realCircleSum, ContinuousMap.coe_mk, AnalyticFields.electric, decode_eq, realDecode]
  rw [circleSum_trace_apply (width p.T) (width_nonneg p.T p.time_le)]

theorem magneticCircle_coe (p : Data) (t : Time p.T) (x : ℝ) :
    magneticCircle p t (x : AnalyticTails.Circle) = magnetic p t x := by
  simp only [magneticCircle, ContinuousMap.add_apply, ContinuousMap.const_apply,
    realCircleSum, ContinuousMap.coe_mk, AnalyticFields.magnetic, decode_eq, realDecode]
  rw [circleSum_trace_apply (width p.T) (width_nonneg p.T p.time_le)]

theorem magneticDerivativeCircle_coe (p : Data) (t : Time p.T) (x : ℝ) :
    magneticDerivativeCircle p t (x : AnalyticTails.Circle) =
      realDerivative (width p.T) (hTrace p) t x := by
  change (circleSum (derivativeCoeff (width p.T t) (hTrace p) t) (x : AnalyticTails.Circle)).re = _
  rw [circleSum_derivative_apply (width p.T)
    (fun s => (by norm_num : (0 : ℝ) < 3/10).trans_le (width_lower_bound p.T p.time_le s))]
  rfl

theorem decay_square (N : ℕ) : Real.exp (-(3/10 : ℝ)*((N : ℝ)+1)) = (cutoffDecay N)^2 := by
  unfold cutoffDecay
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem electric_projection_tail (p : Data) (t : Time p.T) (N : ℕ) :
    ‖toL2 (electricCircle p t) - RealGalerkin.projection N (toL2 (electricCircle p t))‖ ≤
      (cutoffDecay N)^2/5 := by
  have h := trace_projection_error_offset N 1 (width p.T t) (3/10) (by norm_num)
    (width_lower_bound p.T p.time_le t) (eTrace p) t
  calc
    _ ≤ Real.exp (-(3/10 : ℝ)*(N+1))*‖eTrace p‖ := h
    _ ≤ Real.exp (-(3/10 : ℝ)*(N+1))*(1/5) :=
      mul_le_mul_of_nonneg_left (eTrace_bound p) (Real.exp_nonneg _)
    _ = _ := by rw [decay_square]; ring

theorem magnetic_derivative_projection_tail (p : Data) (t : Time p.T) (N : ℕ) :
    ‖toL2 (magneticDerivativeCircle p t) -
      RealGalerkin.projection N (toL2 (magneticDerivativeCircle p t))‖ ≤ (5/3)*cutoffDecay N := by
  change ‖ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ
    (realCircleSum (derivativeCoeff (width p.T t) (hTrace p) t)) - _‖ ≤ _
  rw [realCircleSum_toLp]
  have h := derivative_projection_error N (width p.T t) (3/10) (3/20) (by norm_num)
    (by norm_num) (width_lower_bound p.T p.time_le t) (hTrace p) t
  calc
    _ ≤ (Real.exp (-(3/20 : ℝ)*(N+1)) / (3/10-3/20))*‖hTrace p‖ := h
    _ ≤ (Real.exp (-(3/20 : ℝ)*(N+1)) / (3/10-3/20))*(1/4) :=
      mul_le_mul_of_nonneg_left (hTrace_bound p) (by positivity)
    _ = _ := by unfold cutoffDecay; ring

theorem magnetic_derivative_projection_tail_two (p : Data) (t : Time p.T) (N : ℕ) :
    ‖toL2 (magneticDerivativeCircle p t) -
      RealGalerkin.projection N (toL2 (magneticDerivativeCircle p t))‖ ≤ 2*cutoffDecay N := by
  apply (magnetic_derivative_projection_tail p t N).trans
  apply mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_nonneg _)

end
end KerrKoopman.AnalyticFieldTails
