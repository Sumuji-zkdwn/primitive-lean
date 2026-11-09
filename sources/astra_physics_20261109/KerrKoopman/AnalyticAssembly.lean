import KerrKoopman.AnalyticFixedPoint
import KerrKoopman.AnalyticLift
import KerrKoopman.WeightedConvolution
import KerrKoopman.AnalyticFourierDuhamel

/-!
Analytic construction: the all-mode mild fixed point with every operator instantiated.
No product, Duhamel map, or initial lift is assumed. Differentiable Fourier
restoration and Hermitian symmetry are separate subsequent construction steps.
-/

namespace KerrKoopman.AnalyticAssembly

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AnalyticLift AnalyticFixedPoint Phase3PolynomialInverse Phase3WeightedConvolution
open scoped Topology

def width (T : ℝ) : C(Time T, ℝ) := ⟨fun t => 1 / 2 - (t : ℝ), by fun_prop⟩

theorem width_lower_bound (T : ℝ) (hT : T ≤ 1 / 5) (t : Time T) :
    (3 / 10 : ℝ) ≤ width T t := by
  change 3 / 10 ≤ 1 / 2 - (t : ℝ)
  linarith [t.property.2]

theorem width_nonneg (T : ℝ) (hT : T ≤ 1 / 5) (t : Time T) :
    0 ≤ width T t := le_trans (by norm_num) (width_lower_bound T hT t)

def product (T : ℝ) (hT : T ≤ 1 / 5) : Scalar T →L[ℝ] Scalar T →L[ℝ] Scalar T :=
  twistedProductReal (width T) (width_nonneg T hT)

theorem product_norm_le (T : ℝ) (hT : T ≤ 1 / 5) (u v : Scalar T) :
    ‖product T hT u v‖ ≤ ‖u‖ * ‖v‖ :=
  twistedProductReal_norm_le (width T) (width_nonneg T hT) u v

def kernel (T : ℝ) (hT : 0 ≤ T) : Scalar T →L[ℝ] Branches T :=
  AnalyticFourierDuhamel.duhamel T hT 1 (1 / Real.sqrt 2) (by norm_num)

theorem kernel_opNorm_le (T : ℝ) (hT : 0 ≤ T) : ‖kernel T hT‖ ≤ 1 := by
  simpa only [inv_one] using
    AnalyticFourierDuhamel.duhamel_opNorm_le T hT 1 (1 / Real.sqrt 2) (by norm_num)

def linearEvolution (T : ℝ) (a : Initial) : Branches T :=
  freeLift T 1 (1 / Real.sqrt 2) (by norm_num) a

theorem linearEvolution_norm_le (T : ℝ) (a : Initial) (ha : ‖a‖ ≤ 57 / 250) :
    ‖linearEvolution T a‖ ≤ 57 / 250 :=
  (freeLift_norm_le T 1 (1 / Real.sqrt 2) (by norm_num) a).trans ha

def iterateMap (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5)
    (a : Initial) (ha : ‖a‖ ≤ 57 / 250) : Ball (Branches T) → Ball (Branches T) :=
  outerMap (product T hT1) (product_norm_le T hT1)
    (displacement T) (displacement_opNorm_le T) (kernel T hT0) (kernel_opNorm_le T hT0)
    (linearEvolution T a) (linearEvolution_norm_le T a ha)

theorem iterateMap_contracting (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5)
    (a : Initial) (ha : ‖a‖ ≤ 57 / 250) :
    ContractingWith (55 / 273 : NNReal) (iterateMap T hT0 hT1 a ha) :=
  outerMap_contracting _ _ _ _ _ _ _ _

/-- An actual all-mode weighted trace solving the explicit Duhamel fixed-point
equation, constructed by convergent iteration from zero. -/
theorem exists_mild_solution (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5)
    (a : Initial) (ha : ‖a‖ ≤ 57 / 250) :
    ∃ z : Ball (Branches T),
      linearEvolution T a + kernel T hT0
        (nonlinear (product T hT1) (product_norm_le T hT1) (displacement T z.val)
          (displacement_norm_le (displacement T) (displacement_opNorm_le T) z)) = z.val ∧
      Filter.Tendsto (fun n : ℕ => ((iterateMap T hT0 hT1 a ha)^[n]
        ⟨0, Metric.mem_closedBall_self (by norm_num)⟩).val) Filter.atTop (𝓝 z.val) :=
  exists_outer_fixedpoint _ _ _ _ _ _ _ _

def mildSolution (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5)
    (a : Initial) (ha : ‖a‖ ≤ 57 / 250) : Ball (Branches T) :=
  (exists_mild_solution T hT0 hT1 a ha).choose

theorem mildSolution_equation (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5)
    (a : Initial) (ha : ‖a‖ ≤ 57 / 250) :
    linearEvolution T a + kernel T hT0
      (nonlinear (product T hT1) (product_norm_le T hT1)
        (displacement T (mildSolution T hT0 hT1 a ha).val)
        (displacement_norm_le (displacement T) (displacement_opNorm_le T)
          (mildSolution T hT0 hT1 a ha))) = (mildSolution T hT0 hT1 a ha).val :=
  (exists_mild_solution T hT0 hT1 a ha).choose_spec.1

theorem iterates_tendsto_mildSolution (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5)
    (a : Initial) (ha : ‖a‖ ≤ 57 / 250) :
    Filter.Tendsto (fun n : ℕ => ((iterateMap T hT0 hT1 a ha)^[n]
      ⟨0, Metric.mem_closedBall_self (by norm_num)⟩).val)
      Filter.atTop (𝓝 (mildSolution T hT0 hT1 a ha).val) :=
  (exists_mild_solution T hT0 hT1 a ha).choose_spec.2

theorem mildSolution_norm_le (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5)
    (a : Initial) (ha : ‖a‖ ≤ 57 / 250) :
    ‖(mildSolution T hT0 hT1 a ha).val‖ ≤ 1 / 4 :=
  mem_closedBall_zero_iff.mp (mildSolution T hT0 hT1 a ha).property

theorem mildSolution_fixedpoint (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5)
    (a : Initial) (ha : ‖a‖ ≤ 57 / 250) :
    Function.IsFixedPt (iterateMap T hT0 hT1 a ha) (mildSolution T hT0 hT1 a ha) :=
  Subtype.ext (mildSolution_equation T hT0 hT1 a ha)

/-- A common, initial-only finite outer-iteration stopping bound. -/
theorem iteration_error_le (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5)
    (a : Initial) (ha : ‖a‖ ≤ 57 / 250) (n : ℕ) :
    ‖((iterateMap T hT0 hT1 a ha)^[n]
      ⟨0, Metric.mem_closedBall_self (by norm_num)⟩).val -
        (mildSolution T hT0 hT1 a ha).val‖ ≤ (1 / 4 : ℝ) * (55 / 273 : ℝ) ^ n := by
  let z₀ : Ball (Branches T) := ⟨0, Metric.mem_closedBall_self (by norm_num)⟩
  let z := mildSolution T hT0 hT1 a ha
  have hf : (iterateMap T hT0 hT1 a ha)^[n] z = z :=
    (mildSolution_fixedpoint T hT0 hT1 a ha).iterate n
  have hl := ((iterateMap_contracting T hT0 hT1 a ha).toLipschitzWith.iterate n).dist_le_mul z₀ z
  rw [hf] at hl
  change ‖((iterateMap T hT0 hT1 a ha)^[n] z₀).val - z.val‖ ≤ _
  have hl' : ‖((iterateMap T hT0 hT1 a ha)^[n] z₀).val - z.val‖ ≤
      (55 / 273 : ℝ) ^ n * ‖z.val‖ := by
    simpa only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_pow, NNReal.coe_div,
      NNReal.coe_ofNat, z₀, zero_sub, norm_neg] using hl
  exact hl'.trans (by
    have h := mul_le_mul_of_nonneg_left (mildSolution_norm_le T hT0 hT1 a ha)
      (show 0 ≤ (55 / 273 : ℝ) ^ n by positivity)
    simpa only [mul_comm] using h)

end

end KerrKoopman.AnalyticAssembly
