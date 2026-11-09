import KerrKoopman.GalerkinGronwall
import KerrKoopman.GalerkinRegularity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual joint spatial/time approximation of a classical analytic-class field

The control structure contains classical regularity and Fourier-tail data,
not a Galerkin error estimate. The spatial error, splitting error and joint
limit are derived from the actual PDE, actual projected initial state, and
the actual explicit shear iteration. The diagonal step count depends only
on the cutoff, physical time and initial norm.
-/

namespace KerrKoopman.GalerkinClassical

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter FiniteRepresentatives
open scoped Topology Interval

structure ClassicalTailControl (T : ℝ)
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period (Ioo 0 T))
    (D H : C(Circle, ℝ)) where
  initial_D : ∀ x, Riccati.constitutive (base.E 0 x)=realLift D x
  initial_H : base.H 0=realLift H
  continuous_E : Continuous (fun p : ℝ × ℝ => base.E p.1 p.2)
  continuous_H : Continuous (fun p : ℝ × ℝ => base.H p.1 p.2)
  continuous_Ex : Continuous (fun p : ℝ × ℝ => base.Ex p.1 p.2)
  continuous_Hx : Continuous (fun p : ℝ × ℝ => base.Hx p.1 p.2)
  bound_Hx : ∀ t ∈ Ioo 0 T, ∀ x ∈ Icc 0 IntervalFourier.period, |base.Hx t x| ≤ 1
  tail_Hx : ∀ N t, t ∈ Ioo 0 T →
    (∫ x in 0..IntervalFourier.period,
      (base.Hx t x-IntervalFourier.projection N (base.Hx t) x)^2)/IntervalFourier.period ≤
        (2*cutoffDecay N)^2
  tail_E : ∀ N t, t ∈ Ioo 0 T →
    (∫ x in 0..IntervalFourier.period,
      (base.E t x-IntervalFourier.projection N (base.E t) x)^2)/IntervalFourier.period ≤
        ((cutoffDecay N)^2/5)^2
  initial_tail_D : ∀ N, ‖RealGalerkin.projection N (toL2 D)-toL2 D‖ ≤
    (10/7 : ℝ)*(57/250)*Real.exp (-((N : ℝ)+1)/2)
  initial_tail_H : ∀ N, ‖RealGalerkin.projection N (toL2 H)-toL2 H‖ ≤
    (57/250 : ℝ)*Real.exp (-((N : ℝ)+1)/2)

/-- Closed-interval continuity and local domination are now discharged by actual joint continuity. -/
theorem spatial_error_from_control (T : ℝ) (hT : T ≤ 1/5)
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period (Ioo 0 T))
    (D H : C(Circle, ℝ)) (control : ClassicalTailControl T base D H)
    (N : ℕ) (t : ℝ) (Efinal Hfinal : C(Circle, ℝ))
    (hEt : base.E t=realLift Efinal) (hHt : base.H t=realLift Hfinal) (ht : t ∈ Icc 0 T) :
    ‖GalerkinFlow.decode N (GalerkinFlow.flow N t (projectedInitial N D H)) -
      initialFields Efinal Hfinal‖ ≤ 2*cutoffDecay N := by
  have hc : ContinuousOn (normalizedRelative base N (projectedInitial N D H)) (Icc 0 T) :=
    (normalized_energy_continuous base N (projectedInitial N D H)
      control.continuous_E control.continuous_H).continuousOn
  obtain ⟨bound,hb,hbound⟩ := exists_rate_bound base N (projectedInitial N D H) T
    control.continuous_E control.continuous_H control.continuous_Ex control.continuous_Hx
  exact actual_spatial_error_le T hT base N D H Efinal Hfinal t control.initial_D control.initial_H
    hEt hHt hc bound hb hbound control.bound_Hx (control.tail_Hx N) (control.tail_E N)
    (control.initial_tail_D N) (control.initial_tail_H N) ht

def approximation (N n : ℕ) (t : ℝ) (D H : C(Circle, ℝ)) : GalerkinFlow.Fields :=
  GalerkinFlow.decode N ((GalerkinFlow.step N (t/n))^[n] (projectedInitial N D H))

def splittingNumerator (N : ℕ) (t r : ℝ) : ℝ :=
  (3/2 : ℝ)*(N : ℝ)^2*t^2*r*Real.exp ((N : ℝ)*t)

theorem approximation_error_le (T : ℝ) (hT : T ≤ 1/5)
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period (Ioo 0 T))
    (D H : C(Circle, ℝ)) (control : ClassicalTailControl T base D H)
    (N n : ℕ) (hn : 0<n) (t : ℝ) (Efinal Hfinal : C(Circle, ℝ))
    (hEt : base.E t=realLift Efinal) (hHt : base.H t=realLift Hfinal) (ht : t ∈ Icc 0 T) :
    ‖approximation N n t D H-initialFields Efinal Hfinal‖ ≤
      2*cutoffDecay N+splittingNumerator N t ‖initialFields D H‖/n := by
  have hs := spatial_error_from_control T hT base D H control N t Efinal Hfinal hEt hHt ht
  have htstep := GalerkinFlow.initial_only_restored_error_le N t ht.1 (initialFields D H) n hn
  have hi := norm_sub_le_norm_sub_add_norm_sub (approximation N n t D H)
    (GalerkinFlow.decode N (GalerkinFlow.flow N t (projectedInitial N D H)))
    (initialFields Efinal Hfinal)
  have hsum := add_le_add htstep hs
  apply hi.trans
  convert hsum using 1
  unfold splittingNumerator
  ring

/-- Both indices grow; the time count uses only the initial norm and physical time. -/
def jointSteps (N : ℕ) (t r : ℝ) : ℕ :=
  max (N+1) (Nat.ceil (splittingNumerator N t r*((N : ℝ)+1)))

theorem jointSteps_pos (N : ℕ) (t r : ℝ) : 0<jointSteps N t r :=
  (Nat.succ_pos N).trans_le (le_max_left _ _)

theorem jointSteps_tendsto (t r : ℝ) : Tendsto (fun N => jointSteps N t r) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  exact eventually_atTop.mpr ⟨b, fun N hN =>
    hN.trans ((Nat.le_succ N).trans (le_max_left _ _))⟩

theorem jointSteps_budget (N : ℕ) (t r : ℝ) :
    splittingNumerator N t r/(jointSteps N t r : ℝ) ≤ 1/((N : ℝ)+1) := by
  have hn : 0<(jointSteps N t r : ℝ) := Nat.cast_pos.mpr (jointSteps_pos N t r)
  have hN : 0<(N : ℝ)+1 := by positivity
  have hc := Nat.le_ceil (splittingNumerator N t r*((N : ℝ)+1))
  have hm : (Nat.ceil (splittingNumerator N t r*((N : ℝ)+1)) : ℝ) ≤
      (jointSteps N t r : ℝ) := Nat.cast_le.mpr (le_max_right _ _)
  apply (div_le_div_iff₀ hn hN).mpr
  simpa only [one_mul] using hc.trans hm

theorem cutoffDecay_tendsto : Tendsto cutoffDecay atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (Real.exp_nonneg (-(3/20 : ℝ)))
    (Real.exp_lt_one_iff.mpr (by norm_num : -(3/20 : ℝ)<0))
  have h := (tendsto_const_nhds (x := Real.exp (-(3/20 : ℝ)))).mul hp
  have he : (fun N : ℕ => Real.exp (-(3/20 : ℝ))*Real.exp (-(3/20 : ℝ))^N) = cutoffDecay := by
    funext N
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    unfold cutoffDecay
    congr 1
    ring
  rw [he, mul_zero] at h
  exact h

theorem joint_error_le (T : ℝ) (hT : T ≤ 1/5)
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period (Ioo 0 T))
    (D H : C(Circle, ℝ)) (control : ClassicalTailControl T base D H)
    (N : ℕ) (t : ℝ) (Efinal Hfinal : C(Circle, ℝ))
    (hEt : base.E t=realLift Efinal) (hHt : base.H t=realLift Hfinal) (ht : t ∈ Icc 0 T) :
    ‖approximation N (jointSteps N t ‖initialFields D H‖) t D H-initialFields Efinal Hfinal‖ ≤
      2*cutoffDecay N+1/((N : ℝ)+1) :=
  (approximation_error_le T hT base D H control N _ (jointSteps_pos N t _) t
    Efinal Hfinal hEt hHt ht).trans (add_le_add le_rfl (jointSteps_budget N t _))

/-- A joint N,n limit of the actual explicit formula to the supplied classical PDE field. -/
theorem joint_approximation_tendsto (T : ℝ) (hT : T ≤ 1/5)
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period (Ioo 0 T))
    (D H : C(Circle, ℝ)) (control : ClassicalTailControl T base D H)
    (t : ℝ) (Efinal Hfinal : C(Circle, ℝ))
    (hEt : base.E t=realLift Efinal) (hHt : base.H t=realLift Hfinal) (ht : t ∈ Icc 0 T) :
    Tendsto (fun N => approximation N (jointSteps N t ‖initialFields D H‖) t D H)
      atTop (𝓝 (initialFields Efinal Hfinal)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun N : ℕ => 2*cutoffDecay N+1/((N : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      (cutoffDecay_tendsto.const_mul 2).add tendsto_one_div_add_atTop_nhds_zero_nat
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun N => joint_error_le T hT base D H control N t Efinal Hfinal hEt hHt ht) hlim

end
end KerrKoopman.GalerkinClassical
