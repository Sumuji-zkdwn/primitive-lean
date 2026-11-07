/- Compiled after the unchanged original linear_input/lean_check/Observation.lean. -/
namespace TwoMotionEmission

/-- This is an equality to the actual retained linear-input definition. -/
theorem native_coupling_as_linear_input (κ g x₁ x₂ y : ℝ) :
    coupling κ g x₁ x₂ y =
      LinearInputObservation.energy
        (fun z : ℝ => κ*z^2/2 + κ*g^2*x₁^2*x₂^2/2)
        (fun z : ℝ => z) (κ*g*x₁*x₂) y := by
  unfold coupling LinearInputObservation.energy
  ring

/-- A fixed-pair energy probe recovers the outgoing coordinate by the old theorem.
Here the two inputs are probe settings, not the coupled system's autonomous law. -/
theorem native_energy_probe_recovers_boundary (κ g x₁ x₂ u v y : ℝ)
    (huv : u ≠ v) :
    (LinearInputObservation.energy
        (fun z : ℝ => κ*z^2/2 + κ*g^2*x₁^2*x₂^2/2) (fun z : ℝ => z) u y -
      LinearInputObservation.energy
        (fun z : ℝ => κ*z^2/2 + κ*g^2*x₁^2*x₂^2/2) (fun z : ℝ => z) v y) /
      (v-u) = y := by
  exact LinearInputObservation.recover_coordinate _ _ u v huv y

end TwoMotionEmission
