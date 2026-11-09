
/-! The actual Hilbert decoder error equals the normalized physical real-field error integral. -/

namespace KerrKoopman.GalerkinClassical

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory FiniteRepresentatives
open scoped Interval

theorem decoded_fst_toL2 (N : ℕ) (z : GalerkinFlow.State N) (t : ℝ) :
    (GalerkinFlow.decode N (GalerkinFlow.flow N t z)).fst =
      toL2 (continuousMaterial (representative N (GalerkinFlow.flow N t z).fst)) := by
  rw [toL2_continuousMaterial, toL2_representative]
  rfl

theorem decoded_snd_toL2 (N : ℕ) (z : GalerkinFlow.State N) (t : ℝ) :
    (GalerkinFlow.decode N (GalerkinFlow.flow N t z)).snd =
      toL2 (representative N (GalerkinFlow.flow N t z).snd) := by
  rw [toL2_representative]
  rfl

theorem decoded_error_sq_eq_integral (N : ℕ) (z : GalerkinFlow.State N) (t : ℝ)
    (E H : C(Circle, ℝ)) :
    ‖GalerkinFlow.decode N (GalerkinFlow.flow N t z) -
      WithLp.toLp 2 (toL2 E, toL2 H)‖^2 =
      (∫ x in 0..(2*Real.pi), (electric N z t x-realLift E x)^2 +
        (magnetic N z t x-realLift H x)^2)/(2*Real.pi) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖(GalerkinFlow.decode N (GalerkinFlow.flow N t z)).fst-toL2 E‖^2 +
    ‖(GalerkinFlow.decode N (GalerkinFlow.flow N t z)).snd-toL2 H‖^2 = _
  rw [decoded_fst_toL2, decoded_snd_toL2, ← map_sub, ← map_sub,
    norm_toL2_sq_interval, norm_toL2_sq_interval]
  have hE := (electric_contDiff N z t).continuous
  have hH := (magnetic_contDiff N z t).continuous
  have cE := realLift_continuous E
  have cH := realLift_continuous H
  have h1 : Continuous (fun x => (electric N z t x-realLift E x)^2) := by fun_prop
  have h2 : Continuous (fun x => (magnetic N z t x-realLift H x)^2) := by fun_prop
  have hi : (∫ x in 0..(2*Real.pi), (electric N z t x-realLift E x)^2 +
      (magnetic N z t x-realLift H x)^2) =
      (∫ x in 0..(2*Real.pi), (electric N z t x-realLift E x)^2) +
      ∫ x in 0..(2*Real.pi), (magnetic N z t x-realLift H x)^2 :=
    intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)
  rw [hi, add_div]
  rfl

/-- The normalized relative energy controls the existing actual L2 decoder, with its Hilbert norm. -/
theorem decoded_error_sq_le_relative {s : Set ℝ}
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period s)
    (N : ℕ) (z : GalerkinFlow.State N) (t : ℝ) (E H : C(Circle, ℝ))
    (hE : base.E t = realLift E) (hH : base.H t = realLift H) :
    ‖GalerkinFlow.decode N (GalerkinFlow.flow N t z) - WithLp.toLp 2 (toL2 E, toL2 H)‖^2 ≤
      2*ContinuumGalerkin.ClassicalKerrPair.normalizedEnergy (withGalerkin base N z) t := by
  rw [decoded_error_sq_eq_integral]
  have hp : (0 : ℝ) < IntervalFourier.period := by unfold IntervalFourier.period; positivity
  have hi := ContinuumGalerkin.ClassicalKerrPair.normalized_squared_error_le
    (withGalerkin base N z) t hp
  change (∫ x in 0..IntervalFourier.period, (electric N z t x-base.E t x)^2 +
      (magnetic N z t x-base.H t x)^2)/(IntervalFourier.period-0) ≤ _ at hi
  rw [hE, hH, sub_zero] at hi
  exact hi

end
end KerrKoopman.GalerkinClassical
