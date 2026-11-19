
/-! Actual real material fields of the common all-mode analytic fixed point.
The input hypotheses concern only the initial weighted Fourier coefficients. -/

namespace KerrKoopman.AnalyticFields
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AnalyticLift AnalyticAssembly AnalyticReality AnalyticFixedPoint
open Phase3PolynomialInverse Phase3WeightedReality Phase3WeightedRealDecode
open Phase3WeightedDerivative
open scoped Topology

/-- The same coordinate construction is used for every initial state in this ball. -/
structure Data where
  T : ℝ
  time_nonneg : 0 ≤ T
  time_le : T ≤ 1 / 5
  initial : Initial
  initial_bound : ‖initial‖ ≤ 57 / 250
  initial_real : HermitianInitial initial

def branches (p : Data) : Branches p.T :=
  (mildSolution p.T p.time_nonneg p.time_le p.initial p.initial_bound).val

theorem branches_bound (p : Data) : ‖branches p‖ ≤ 1 / 4 :=
  mildSolution_norm_le p.T p.time_nonneg p.time_le p.initial p.initial_bound

theorem branches_real (p : Data) : HermitianPair p.T (branches p) :=
  mildSolution_hermitian p.T p.time_nonneg p.time_le p.initial p.initial_bound p.initial_real

def component (b : Bool) : (ℂ × ℂ) →L[ℝ] ℂ :=
  if b then ContinuousLinearMap.fst ℝ ℂ ℂ else ContinuousLinearMap.snd ℝ ℂ ℂ

theorem component_norm_le (b : Bool) : ‖component b‖ ≤ 1 := by
  cases b
  · exact ContinuousLinearMap.norm_snd_le ℝ ℂ ℂ
  · exact ContinuousLinearMap.norm_fst_le ℝ ℂ ℂ

def componentTrace (T : ℝ) (b : Bool) : C(Time T, ℂ × ℂ) →L[ℝ] C(Time T, ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℝ (Time T) (component b)

theorem componentTrace_norm_le (T : ℝ) (b : Bool) : ‖componentTrace T b‖ ≤ 1 := by
  apply (componentTrace T b).opNorm_le_bound (by norm_num)
  intro z
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖component b (z t)‖ ≤ 1 * ‖z‖
  exact ((component b).le_opNorm _).trans
    (mul_le_mul (component_norm_le b) (z.norm_coe_le_norm t) (norm_nonneg _) (by norm_num))

def branch (T : ℝ) (b : Bool) : Branches T →L[ℝ] Scalar T :=
  AnalyticLpMap.diagonal (fun _ : ℤ => componentTrace T b) 1
    (fun _ => componentTrace_norm_le T b)

theorem branch_apply (T : ℝ) (b : Bool) (z : Branches T) (k : ℤ) (t : Time T) :
    branch T b z k t = component b (z k t) := rfl

theorem branch_norm_le (T : ℝ) (b : Bool) (z : Branches T) : ‖branch T b z‖ ≤ ‖z‖ := by
  unfold branch
  simpa only [one_mul] using AnalyticLpMap.diagonal_norm_le
    (fun _ : ℤ => componentTrace T b) 1 (fun _ => componentTrace_norm_le T b) z

theorem branch_real (T : ℝ) (b : Bool) (z : Branches T) (hz : HermitianPair T z) :
    Hermitian (branch T b z) := by
  intro k t
  simp only [branch_apply, hz k t]
  cases b <;> rfl

def dTrace (p : Data) : Scalar p.T := displacement p.T (branches p)

theorem dTrace_bound (p : Data) : ‖dTrace p‖ ≤ 134 / 375 :=
  displacement_norm_le (displacement p.T) (displacement_opNorm_le p.T)
    (mildSolution p.T p.time_nonneg p.time_le p.initial p.initial_bound)

theorem dTrace_bound_sharp (p : Data) : ‖dTrace p‖ ≤ 5 / 14 := by
  calc
    _ ≤ ‖displacement p.T‖ * ‖branches p‖ := (displacement p.T).le_opNorm _
    _ ≤ (10 / 7 : ℝ) * (1 / 4) := mul_le_mul (displacement_opNorm_le p.T)
      (branches_bound p) (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem dTrace_real (p : Data) : Hermitian (dTrace p) :=
  displacement_hermitian p.T (branches p) (branches_real p)

def eTrace (p : Data) : Scalar p.T :=
  inverse (product p.T p.time_le) (product_norm_le p.T p.time_le) (dTrace p) (dTrace_bound p)

def nTrace (p : Data) : Scalar p.T :=
  nonlinear (product p.T p.time_le) (product_norm_le p.T p.time_le) (dTrace p) (dTrace_bound p)

def hTrace (p : Data) : Scalar p.T :=
  (1 / 2 : ℝ) • (branch p.T true (branches p) + branch p.T false (branches p))

theorem eTrace_bound (p : Data) : ‖eTrace p‖ ≤ 1 / 5 := inverse_norm_le _ _ _ _
theorem nTrace_bound (p : Data) : ‖nTrace p‖ ≤ 8 / 375 := nonlinear_norm_le _ _ _ _

theorem eTrace_real (p : Data) : Hermitian (eTrace p) :=
  inverse_hermitian (width p.T) (width_nonneg p.T p.time_le) (dTrace p) _ (dTrace_real p)

theorem nTrace_real (p : Data) : Hermitian (nTrace p) :=
  nonlinear_hermitian (width p.T) (width_nonneg p.T p.time_le) (dTrace p) _ (dTrace_real p)

theorem hTrace_real (p : Data) : Hermitian (hTrace p) :=
  ((branch_real p.T true _ (branches_real p)).add
    (branch_real p.T false _ (branches_real p))).smul (1 / 2)

theorem hTrace_bound (p : Data) : ‖hTrace p‖ ≤ 1 / 4 := by
  unfold hTrace
  rw [norm_smul, Real.norm_eq_abs]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hn := norm_add_le (branch p.T true (branches p)) (branch p.T false (branches p))
  have hp := branch_norm_le p.T true (branches p)
  have hm := branch_norm_le p.T false (branches p)
  have hz := branches_bound p
  linarith

def decode (p : Data) (u : Scalar p.T) (t : Time p.T) (x : ℝ) : ℝ :=
  realEvalCLM (width p.T) (width_nonneg p.T p.time_le) t x u

theorem decode_eq (p : Data) (u : Scalar p.T) (t : Time p.T) (x : ℝ) :
    decode p u t x = realDecode (width p.T) u t x := realEvalCLM_apply _ _ _ _ _

theorem decode_product (p : Data) (u v : Scalar p.T) (hu : Hermitian u) (hv : Hermitian v)
    (t : Time p.T) (x : ℝ) :
    decode p (product p.T p.time_le u v) t x = decode p u t x * decode p v t x := by
  simp only [decode_eq]
  exact realDecode_product _ _ hu hv t x

def electric (p : Data) (t : Time p.T) (x : ℝ) : ℝ := 1 + decode p (eTrace p) t x
def displacementField (p : Data) (t : Time p.T) (x : ℝ) : ℝ := 4 / 3 + decode p (dTrace p) t x
def magnetic (p : Data) (t : Time p.T) (x : ℝ) : ℝ := 3 / 10 + decode p (hTrace p) t x

theorem material_identity (p : Data) (t : Time p.T) (x : ℝ) :
    displacementField p t x = electric p t x + (electric p t x) ^ 3 / 3 := by
  have h := congrArg (realEvalCLM (width p.T) (width_nonneg p.T p.time_le) t x)
    (inverse_constitutive (product p.T p.time_le) (product_norm_le p.T p.time_le)
      (dTrace p) (dTrace_bound p))
  change decode p ((2 : ℝ) • eTrace p + square (product p.T p.time_le) (eTrace p) +
    (1 / 3 : ℝ) • cube (product p.T p.time_le) (eTrace p)) t x = decode p (dTrace p) t x at h
  simp only [decode, map_add, map_smul, smul_eq_mul] at h
  change 2 * decode p (eTrace p) t x +
      decode p (product p.T p.time_le (eTrace p) (eTrace p)) t x +
      (1 / 3) * decode p (product p.T p.time_le (eTrace p)
        (product p.T p.time_le (eTrace p) (eTrace p))) t x = decode p (dTrace p) t x at h
  have hs : Hermitian (product p.T p.time_le (eTrace p) (eTrace p)) :=
    Hermitian.product (width p.T) (width_nonneg p.T p.time_le) (eTrace_real p) (eTrace_real p)
  rw [decode_product p _ _ (eTrace_real p) (eTrace_real p),
    decode_product p _ _ (eTrace_real p) hs,
    decode_product p _ _ (eTrace_real p) (eTrace_real p)] at h
  unfold displacementField electric
  nlinarith [h]

theorem nonlinear_identity (p : Data) (t : Time p.T) (x : ℝ) :
    decode p (nTrace p) t x = decode p (eTrace p) t x - (1 / 2) * decode p (dTrace p) t x := by
  have h := nonlinear_eq (product p.T p.time_le) (product_norm_le p.T p.time_le)
    (dTrace p) (dTrace_bound p)
  change nTrace p = eTrace p - (1 / 2 : ℝ) • dTrace p at h
  unfold decode
  rw [h, map_sub, map_smul, smul_eq_mul]

theorem electric_bound (p : Data) (t : Time p.T) (x : ℝ) : |electric p t x - 1| ≤ 1 / 5 := by
  simpa only [electric, add_sub_cancel_left, decode_eq, Real.norm_eq_abs] using
    (realDecode_norm_le (width p.T) (width_nonneg p.T p.time_le) (eTrace p) t x).trans
      (eTrace_bound p)

theorem displacement_bound (p : Data) (t : Time p.T) (x : ℝ) :
    |displacementField p t x - 4 / 3| ≤ 5 / 14 := by
  simpa only [displacementField, add_sub_cancel_left, decode_eq, Real.norm_eq_abs] using
    (realDecode_norm_le (width p.T) (width_nonneg p.T p.time_le) (dTrace p) t x).trans
      (dTrace_bound_sharp p)

theorem magnetic_bound (p : Data) (t : Time p.T) (x : ℝ) : |magnetic p t x - 3 / 10| ≤ 1 / 4 := by
  simpa only [magnetic, add_sub_cancel_left, decode_eq, Real.norm_eq_abs] using
    (realDecode_norm_le (width p.T) (width_nonneg p.T p.time_le) (hTrace p) t x).trans
      (hTrace_bound p)

theorem fields_continuous (p : Data) :
    Continuous (fun q : Time p.T × ℝ => electric p q.1 q.2) ∧
    Continuous (fun q : Time p.T × ℝ => displacementField p q.1 q.2) ∧
    Continuous (fun q : Time p.T × ℝ => magnetic p q.1 q.2) := by
  simp only [electric, displacementField, magnetic, decode_eq]
  exact ⟨continuous_const.add (continuous_realDecode _ (width_nonneg p.T p.time_le) _),
    continuous_const.add (continuous_realDecode _ (width_nonneg p.T p.time_le) _),
    continuous_const.add (continuous_realDecode _ (width_nonneg p.T p.time_le) _)⟩

theorem fields_periodic (p : Data) (t : Time p.T) :
    Function.Periodic (electric p t) (2 * Real.pi) ∧
    Function.Periodic (displacementField p t) (2 * Real.pi) ∧
    Function.Periodic (magnetic p t) (2 * Real.pi) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro x
  · simpa only [electric, decode_eq] using congrArg (fun y : ℝ => 1 + y) (realDecode_periodic (width p.T) (eTrace p) t x)
  · simpa only [displacementField, decode_eq] using congrArg (fun y : ℝ => 4 / 3 + y) (realDecode_periodic (width p.T) (dTrace p) t x)
  · simpa only [magnetic, decode_eq] using congrArg (fun y : ℝ => 3 / 10 + y) (realDecode_periodic (width p.T) (hTrace p) t x)

theorem fields_spatial_derivatives (p : Data) (t : Time p.T) (x : ℝ) :
    HasDerivAt (electric p t) (realDerivative (width p.T) (eTrace p) t x) x ∧
    HasDerivAt (displacementField p t) (realDerivative (width p.T) (dTrace p) t x) x ∧
    HasDerivAt (magnetic p t) (realDerivative (width p.T) (hTrace p) t x) x := by
  refine ⟨?_, ?_, ?_⟩
  · have he : electric p t = fun y => 1 + realDecode (width p.T) (eTrace p) t y := by
      funext y
      rw [electric, decode_eq]
    rw [he]
    exact (hasDerivAt_realDecode (width p.T) (3 / 10) (by norm_num)
        (width_lower_bound p.T p.time_le) (eTrace p) t x).const_add 1
  · have he : displacementField p t = fun y => 4 / 3 + realDecode (width p.T) (dTrace p) t y := by
      funext y
      rw [displacementField, decode_eq]
    rw [he]
    exact (hasDerivAt_realDecode (width p.T) (3 / 10) (by norm_num)
        (width_lower_bound p.T p.time_le) (dTrace p) t x).const_add (4 / 3)
  · have he : magnetic p t = fun y => 3 / 10 + realDecode (width p.T) (hTrace p) t y := by
      funext y
      rw [magnetic, decode_eq]
    rw [he]
    exact (hasDerivAt_realDecode (width p.T) (3 / 10) (by norm_num)
        (width_lower_bound p.T p.time_le) (hTrace p) t x).const_add (3 / 10)


end
end KerrKoopman.AnalyticFields
