import KerrKoopman.GalerkinRestoration

/-! Actual initial relative-energy upper bound from the projected displacement and magnetic data. -/

namespace KerrKoopman.GalerkinClassical

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory FiniteRepresentatives RelativeEnergy Riccati
open scoped Interval

theorem electricGap_upper_identity (e v : ℝ) :
    (constitutive v-constitutive e)^2/2-electricGap e v =
      (v-e)^2/2*((e+(v-e)/3)^2+(v-e)^2/18+
        (e^2+e*(v-e)+(v-e)^2/3)^2) := by
  unfold electricGap FiniteEnergy.density constitutive
  ring

/-- Global upper bound in displacement coordinates, with no amplitude restriction. -/
theorem electricGap_le_displacement_sq (e v : ℝ) :
    electricGap e v ≤ (constitutive v-constitutive e)^2/2 := by
  have h := electricGap_upper_identity e v
  have hn : 0 ≤ (v-e)^2/2*((e+(v-e)/3)^2+(v-e)^2/18+
      (e^2+e*(v-e)+(v-e)^2/3)^2) := by positivity
  linarith

def initialFields (D H : C(Circle, ℝ)) : GalerkinFlow.Fields :=
  WithLp.toLp 2 (toL2 D, toL2 H)

def projectedInitial (N : ℕ) (D H : C(Circle, ℝ)) : GalerkinFlow.State N :=
  GalerkinFlow.encode N (initialFields D H)

theorem displacement_initial (N : ℕ) (D H : C(Circle, ℝ)) :
    displacement N (projectedInitial N D H) 0 = IntervalFourier.projection N (realLift D) := by
  unfold displacement
  rw [GalerkinFlow.flow_zero]
  change realLift (representative N
    ⟨RealGalerkin.projection N (toL2 D), RealGalerkin.projection_mem N _⟩) = _
  rw [representative_projection_eq, realLift_circleProjection]

theorem magnetic_initial (N : ℕ) (D H : C(Circle, ℝ)) :
    magnetic N (projectedInitial N D H) 0 = IntervalFourier.projection N (realLift H) := by
  unfold magnetic
  rw [GalerkinFlow.flow_zero]
  change realLift (representative N
    ⟨RealGalerkin.projection N (toL2 H), RealGalerkin.projection_mem N _⟩) = _
  rw [representative_projection_eq, realLift_circleProjection]

theorem projection_error_sq_eq_interval (N : ℕ) (f : C(Circle, ℝ)) :
    ‖RealGalerkin.projection N (toL2 f)-toL2 f‖^2 =
      (∫ x in 0..IntervalFourier.period,
        (IntervalFourier.projection N (realLift f) x-realLift f x)^2)/IntervalFourier.period := by
  rw [← toL2_circleProjection, ← map_sub, norm_toL2_sq_interval]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  change (realLift (circleProjection N f) x-realLift f x)^2 = _
  rw [realLift_circleProjection]

/-- The initial energy estimate is derived for the actual projected initial state. -/
theorem normalized_initial_energy_le {s : Set ℝ}
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period s)
    (N : ℕ) (D H : C(Circle, ℝ))
    (hD : ∀ x, constitutive (base.E 0 x) = realLift D x)
    (hH : base.H 0 = realLift H) :
    ContinuumGalerkin.ClassicalKerrPair.normalizedEnergy
      (withGalerkin base N (projectedInitial N D H)) 0 ≤
      ‖RealGalerkin.projection N (toL2 D)-toL2 D‖^2/2 +
      ‖RealGalerkin.projection N (toL2 H)-toL2 H‖^2/2 := by
  let u := withGalerkin base N (projectedInitial N D H)
  have cd := IntervalFourier.projection_continuous N (realLift D)
  have ch := IntervalFourier.projection_continuous N (realLift H)
  have cD := realLift_continuous D
  have cH := realLift_continuous H
  have c1 : Continuous (fun x => (IntervalFourier.projection N (realLift D) x-realLift D x)^2) := by
    fun_prop
  have c2 : Continuous (fun x => (IntervalFourier.projection N (realLift H) x-realLift H x)^2) := by
    fun_prop
  have csum : Continuous (fun x =>
      (IntervalFourier.projection N (realLift D) x-realLift D x)^2/2 +
      (IntervalFourier.projection N (realLift H) x-realLift H x)^2/2) := by fun_prop
  have hp : (0 : ℝ) < IntervalFourier.period := by unfold IntervalFourier.period; positivity
  have hi := intervalIntegral.integral_mono_on (μ := volume) hp.le
    ((u.density_continuous 0).intervalIntegrable _ _) (csum.intervalIntegrable _ _)
    (fun x _ => show u.density 0 x ≤
      (IntervalFourier.projection N (realLift D) x-realLift D x)^2/2 +
      (IntervalFourier.projection N (realLift H) x-realLift H x)^2/2 from by
      change electricGap (base.E 0 x) (electric N (projectedInitial N D H) 0 x) +
        (magnetic N (projectedInitial N D H) 0 x-base.H 0 x)^2/2 ≤ _
      have hv : constitutive (electric N (projectedInitial N D H) 0 x) =
          IntervalFourier.projection N (realLift D) x := by
        unfold electric
        rw [ExplicitMaterial.constitutive_electricOfDisplacement, displacement_initial]
      have he := electricGap_le_displacement_sq (base.E 0 x)
        (electric N (projectedInitial N D H) 0 x)
      rw [hv, hD x] at he
      rw [magnetic_initial, hH]
      linarith)
  have hadd : (∫ x in 0..IntervalFourier.period,
      (IntervalFourier.projection N (realLift D) x-realLift D x)^2/2 +
      (IntervalFourier.projection N (realLift H) x-realLift H x)^2/2) =
      (∫ x in 0..IntervalFourier.period,
        (IntervalFourier.projection N (realLift D) x-realLift D x)^2)/2 +
      (∫ x in 0..IntervalFourier.period,
        (IntervalFourier.projection N (realLift H) x-realLift H x)^2)/2 := by
    rw [intervalIntegral.integral_add ((c1.div_const 2).intervalIntegrable _ _)
      ((c2.div_const 2).intervalIntegrable _ _), intervalIntegral.integral_div,
      intervalIntegral.integral_div]
  rw [hadd] at hi
  have hn := div_le_div_of_nonneg_right hi hp.le
  change (∫ x in 0..IntervalFourier.period, u.density 0 x)/(IntervalFourier.period-0) ≤ _
  rw [sub_zero]
  rw [projection_error_sq_eq_interval, projection_error_sq_eq_interval]
  convert hn using 1
  ring

end
end KerrKoopman.GalerkinClassical
