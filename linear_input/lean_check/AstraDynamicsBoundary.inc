
/-!
# Static primitive certificates do not choose the Maxwell evolution

The input in `GlobalMin (1/3) 1 a` is the primitive's designed input
`a + a^3/3`. It may vary with the parameter `a`. The ramp below is a
minimum for this corresponding input at every time, yet it fails even
the displacement equation of spatially homogeneous source-free Maxwell.

The last results concern energy derivatives at one instant only; they
do not assert that the displayed affine curves conserve energy for all time.
-/

namespace KerrKoopman.PrimitiveDynamicsBoundary

noncomputable section

/-- Every point of the ramp has an actual primitive global-minimum
certificate for its own designed constitutive input. -/
theorem ramp_static_globalMin (t : ℝ) :
    LinearInputDesign.GlobalMin (1 / 3) 1 t := by
  apply LinearInputDesign.globalMin_of_margin
  · norm_num
  · positivity

/-- The matching input is exactly the physical Kerr constitutive value. -/
theorem ramp_designed_input (t : ℝ) :
    LinearInputDesign.input (1 / 3) 1 t = t + t ^ 3 / 3 := by
  unfold LinearInputDesign.input
  ring

/-- The same static statement also gives an actual zero derivative of
the input-tilted potential with respect to its state coordinate. -/
theorem ramp_static_stationary (t : ℝ) :
    deriv (LinearInputCalculus.potential (1 / 3) 1 (t + t ^ 3 / 3)) t = 0 := by
  apply (LinearInputCalculus.stationary_iff_input _ _ _ _).2
  ring

/-- In contrast, its displacement has nonzero physical-time derivative
at the common zero initial state. -/
theorem ramp_displacement_derivative :
    HasDerivAt (fun t : ℝ => t + t ^ 3 / 3) 1 0 := by
  simpa using FiniteEnergy.constitutive_hasDerivAt (fun t : ℝ => t) 1 0
    (hasDerivAt_id 0)

/-- For a spatially homogeneous source-free Maxwell field, `Ddot=0`.
The ramp violates that necessary equation despite its static certificates. -/
theorem ramp_not_homogeneous_maxwell :
    ¬ HasDerivAt (fun t : ℝ => t + t ^ 3 / 3) 0 0 := by
  intro h
  have hn : (1 : ℝ) = 0 := ramp_displacement_derivative.unique h
  norm_num at hn

/-- Concrete countermodel to deriving physical time evolution from
pointwise primitive minimum, stationarity and constitutive law alone. -/
theorem static_certificates_do_not_imply_homogeneous_maxwell :
    ∃ E H D : ℝ → ℝ,
      (∀ t, LinearInputDesign.GlobalMin (1 / 3) 1 (E t)) ∧
      (∀ t, D t = LinearInputDesign.input (1 / 3) 1 (E t)) ∧
      (∀ t, D t = E t + (E t) ^ 3 / 3) ∧
      (∀ t, deriv (LinearInputCalculus.potential (1 / 3) 1 (D t)) (E t) = 0) ∧
      (∀ t, H t = 0) ∧ E 0 = 0 ∧ D 0 = 0 ∧ ¬ HasDerivAt D 0 0 := by
  refine ⟨(fun t => t), (fun _ => 0), (fun t => t + t ^ 3 / 3),
    ramp_static_globalMin, ?_, (fun _ => rfl), ramp_static_stationary,
    (fun _ => rfl), rfl, ?_, ramp_not_homogeneous_maxwell⟩
  · intro t
    exact (ramp_designed_input t).symm
  · norm_num

/-- Two different magnetic velocities have the same zero instantaneous
energy rate at `(E,H)=(1,0)`. This is not conservation along the affine curve. -/
theorem distinct_velocities_same_instantaneous_energy_rate :
    HasDerivAt (fun _ : ℝ => FiniteEnergy.density 1 0) 0 0 ∧
    HasDerivAt (fun t : ℝ => FiniteEnergy.density 1 (2 * t)) 0 0 ∧
    (0 : ℝ) ≠ 2 := by
  refine ⟨hasDerivAt_const 0 _, ?_, by norm_num⟩
  have hh : HasDerivAt (fun t : ℝ => 2 * t) 2 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2
  simpa using FiniteEnergy.density_hasDerivAt
    (fun _ : ℝ => 1) (fun t : ℝ => 2 * t) 0 2 0
    (hasDerivAt_const 0 1) hh

/-- In the actual zero-differentiation Kerr model the magnetic rate is
zero, so the second energy-compatible velocity is not a Maxwell velocity. -/
theorem zero_spatial_operator_rejects_second_velocity :
    FiniteEnergy.magneticRate (fun _ _ : Unit => (0 : ℝ))
      (fun _ : Unit => (1 : ℝ)) () = 0 ∧
    FiniteEnergy.magneticRate (fun _ _ : Unit => (0 : ℝ))
      (fun _ : Unit => (1 : ℝ)) () ≠ 2 := by
  norm_num [FiniteEnergy.magneticRate, FiniteEnergy.applyQ]

end

end KerrKoopman.PrimitiveDynamicsBoundary
