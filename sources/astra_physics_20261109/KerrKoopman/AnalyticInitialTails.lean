import KerrKoopman.AnalyticTraceTails
import KerrKoopman.AnalyticInitial
import KerrKoopman.FiniteRepresentatives

/-! Actual initial circle fields and projection tails from the supplied
weighted coefficient norm; no later solution norm is used. -/

namespace KerrKoopman.AnalyticInitialTails
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory AnalyticFields AnalyticLift AnalyticPDE AnalyticInitial
open AnalyticTails AnalyticTraceTails Phase3WeightedConvolution Phase3WeightedDerivative
open FiniteRepresentatives

def initialCoeff (p : Data) (b : Bool) (k : ℤ) : ℂ :=
  modeValue (1/2) k (component b (p.initial k)) 0

def initialCircleBranch (p : Data) (b : Bool) : C(AnalyticTails.Circle, ℝ) :=
  realCircleSum (initialCoeff p b)

def initialCircleD (p : Data) : C(AnalyticTails.Circle, ℝ) :=
  ContinuousMap.const _ (4/3) + speed • (initialCircleBranch p true - initialCircleBranch p false)

def initialCircleH (p : Data) : C(AnalyticTails.Circle, ℝ) :=
  ContinuousMap.const _ (3/10) + (1/2 : ℝ) • (initialCircleBranch p true + initialCircleBranch p false)

theorem component_value_norm_le (p : Data) (b : Bool) (k : ℤ) :
    ‖component b (p.initial k)‖ ≤ ‖p.initial k‖ := by
  apply ((component b).le_opNorm _).trans
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (component_norm_le b) (norm_nonneg (p.initial k))

theorem initialCoeff_norm_le (p : Data) (b : Bool) (k : ℤ) :
    ‖initialCoeff p b k‖ ≤ ‖p.initial k‖ := by
  rw [initialCoeff, modeValue_norm]
  have he : Real.exp (-(1/2 : ℝ)*|(k : ℝ)|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (k : ℝ)])
  exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans (by
    simpa only [one_mul] using component_value_norm_le p b k)

theorem initialCoeff_summable (p : Data) (b : Bool) : Summable (fun k => ‖initialCoeff p b k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (initialCoeff_norm_le p b) (l1_summable_norm p.initial)

theorem initialCircleBranch_coe (p : Data) (b : Bool) (x : ℝ) :
    initialCircleBranch p b (x : AnalyticTails.Circle) = initialBranch p b x := by
  change (circleSum (initialCoeff p b) (x : AnalyticTails.Circle)).re = _
  rw [circleSum_apply _ (initialCoeff_summable p b)]
  apply congrArg Complex.re
  apply tsum_congr
  intro k
  exact modeValue_mul_character (1/2) k (component b (p.initial k)) x

theorem initialCircleD_coe (p : Data) (x : ℝ) :
    initialCircleD p (x : AnalyticTails.Circle) = initialDisplacement p x := by
  simp only [initialCircleD, ContinuousMap.add_apply, ContinuousMap.const_apply,
    ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul, initialCircleBranch_coe]
  rfl

theorem initialCircleH_coe (p : Data) (x : ℝ) :
    initialCircleH p (x : AnalyticTails.Circle) = initialMagnetic p x := by
  simp only [initialCircleH, ContinuousMap.add_apply, ContinuousMap.const_apply,
    ContinuousMap.smul_apply, smul_eq_mul, initialCircleBranch_coe]
  rfl

theorem initialCoeff_tail (p : Data) (b : Bool) (N : ℕ) (k : ℤ)
    (hk : k ∉ FourierProjection.frequencies N) :
    ‖initialCoeff p b k‖ ≤ Real.exp (-((N : ℝ)+1)/2) * ‖p.initial k‖ := by
  rw [initialCoeff, modeValue_norm]
  have he : Real.exp (-(1/2 : ℝ)*|(k : ℝ)|) ≤ Real.exp (-((N : ℝ)+1)/2) := by
    apply Real.exp_le_exp.mpr
    linarith [frequency_outside_lower N k hk]
  exact mul_le_mul he (component_value_norm_le p b k) (norm_nonneg _) (Real.exp_nonneg _)

theorem initialCircleBranch_tail (p : Data) (b : Bool) (N : ℕ) :
    ‖toL2 (initialCircleBranch p b) - RealGalerkin.projection N (toL2 (initialCircleBranch p b))‖ ≤
      (57/250 : ℝ)*Real.exp (-((N : ℝ)+1)/2) := by
  change ‖ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ
    (realCircleSum (initialCoeff p b)) - _‖ ≤ _
  rw [realCircleSum_toLp]
  have h := projection_tail_bound N (initialCoeff p b) (initialCoeff_summable p b)
    (fun k => ‖p.initial k‖) (l1_summable_norm p.initial) (fun _ => norm_nonneg _)
    (Real.exp (-((N : ℝ)+1)/2)) (Real.exp_nonneg _) (initialCoeff_tail p b N)
  rw [← l1_norm_eq_tsum] at h
  calc
    _ ≤ Real.exp (-((N : ℝ)+1)/2)*‖p.initial‖ := h
    _ ≤ Real.exp (-((N : ℝ)+1)/2)*(57/250) :=
      mul_le_mul_of_nonneg_left p.initial_bound (Real.exp_nonneg _)
    _ = _ := by ring

def residual (N : ℕ) : MaterialL2.RealCircleL2 →L[ℝ] MaterialL2.RealCircleL2 :=
  ContinuousLinearMap.id ℝ _ - RealGalerkin.projection N

theorem residual_const (N : ℕ) (a : ℝ) :
    residual N (toL2 (ContinuousMap.const AnalyticTails.Circle a)) = 0 := by
  change toL2 (ContinuousMap.const AnalyticTails.Circle a) -
    RealGalerkin.projection N (toL2 (ContinuousMap.const AnalyticTails.Circle a)) = 0
  unfold toL2
  rw [RealGalerkin.projection_eq_self N (constant_toLp_mem N a), sub_self]

theorem initialCircleD_tail (p : Data) (N : ℕ) :
    ‖RealGalerkin.projection N (toL2 (initialCircleD p)) - toL2 (initialCircleD p)‖ ≤
      (10/7 : ℝ)*(57/250)*Real.exp (-((N : ℝ)+1)/2) := by
  rw [norm_sub_rev]
  change ‖residual N (toL2 (initialCircleD p))‖ ≤ _
  simp only [initialCircleD, map_add, map_smul, map_sub, residual_const, zero_add, norm_smul]
  have hp := initialCircleBranch_tail p true N
  have hm := initialCircleBranch_tail p false N
  change ‖residual N (toL2 (initialCircleBranch p true))‖ ≤ _ at hp
  change ‖residual N (toL2 (initialCircleBranch p false))‖ ≤ _ at hm
  have hs : ‖speed‖ ≤ (5/7 : ℝ) := by
    simpa only [speed, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/Real.sqrt 2)]
      using inverse_sqrt_two_le
  have hsum := (norm_sub_le (residual N (toL2 (initialCircleBranch p true)))
    (residual N (toL2 (initialCircleBranch p false)))).trans (add_le_add hp hm)
  exact (mul_le_mul hs hsum (norm_nonneg _) (by norm_num)).trans_eq (by ring)

theorem initialCircleH_tail (p : Data) (N : ℕ) :
    ‖RealGalerkin.projection N (toL2 (initialCircleH p)) - toL2 (initialCircleH p)‖ ≤
      (57/250 : ℝ)*Real.exp (-((N : ℝ)+1)/2) := by
  rw [norm_sub_rev]
  change ‖residual N (toL2 (initialCircleH p))‖ ≤ _
  simp only [initialCircleH, map_add, map_smul, residual_const, zero_add, norm_smul]
  have hp := initialCircleBranch_tail p true N
  have hm := initialCircleBranch_tail p false N
  change ‖residual N (toL2 (initialCircleBranch p true))‖ ≤ _ at hp
  change ‖residual N (toL2 (initialCircleBranch p false))‖ ≤ _ at hm
  have hsum := (norm_add_le (residual N (toL2 (initialCircleBranch p true)))
    (residual N (toL2 (initialCircleBranch p false)))).trans (add_le_add hp hm)
  exact (mul_le_mul_of_nonneg_left hsum (norm_nonneg (1/2 : ℝ))).trans_eq (by norm_num; ring)

end
end KerrKoopman.AnalyticInitialTails
