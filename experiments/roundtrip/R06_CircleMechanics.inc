/-!
# Round trip 6: cusp potential → Newtonian mechanics in arclength → elastica circles

Input: rounds 3–5 used the scalar quartic `f λ r u`. The baseline `CurvatureBridge`
shows the quadratic-density curvature equation is a phase flow for the same family.
Translation: `κ(s)` is a particle in the potential `potential (1/2) (-σ/k) u`, arclength
is time, `κ'` is momentum. Back-translation: constant-curvature arcs are exactly the
equilibria `u = input`, the pressure equation fixes `u = p / k`, and the exact
linearization coefficient is the cusp second derivative `3λa² + r` from round 3.
-/

noncomputable section
namespace RoundTrip06
open LinearInputDesign LinearInputCalculus

/-- The phase energy splits as kinetic energy plus the cusp potential. -/
theorem phase_energy_split (k σ u κ p : ℝ) :
    E (1 / 2) (-σ / k) u κ (p + Real.sqrt 2 * κ) =
      p ^ 2 / 2 + potential (1 / 2) (-σ / k) u κ := by
  rw [LinearInputCurvatureBridge.energy_shear]
  unfold potential
  ring

/-- Circles: constant curvature solves the forced curvature equation iff it lies on the
cusp equilibrium surface. -/
theorem circle_iff_input {k σ u a : ℝ} (hk : k ≠ 0) :
    (∀ s : ℝ, k * deriv (deriv (fun _ : ℝ => a)) s + k * a ^ 3 / 2 - σ * a = k * u) ↔
      u = input (1 / 2) (-σ / k) a := by
  simp only [deriv_const', mul_zero, zero_add]
  unfold input
  constructor
  · intro h
    have := h 0
    field_simp
    linarith
  · intro h s
    rw [h]
    field_simp
    ring

/-- With the baseline pressure equation (right-hand side `p`), circles satisfy
`p / k = input`, so pressure is the cusp input. -/
theorem pressure_circle_iff {k σ p a : ℝ} (hk : k ≠ 0) :
    k * a ^ 3 / 2 - σ * a = p ↔ p / k = input (1 / 2) (-σ / k) a := by
  unfold input
  constructor
  · intro h; rw [← h]; field_simp; ring
  · intro h
    have := congrArg (· * k) h
    simp only at this
    field_simp at this
    linarith

/-- Exact (not truncated) expansion of the curvature equation around a circle. -/
theorem expansion_around_circle (k σ a δ δ'' : ℝ) (hk : k ≠ 0) :
    k * δ'' + k * (a + δ) ^ 3 / 2 - σ * (a + δ) - k * input (1 / 2) (-σ / k) a =
      k * (δ'' + (3 * (1 / 2) * a ^ 2 + (-σ / k)) * δ + 3 * a / 2 * δ ^ 2 + δ ^ 3 / 2) := by
  unfold input
  field_simp
  ring

/-- Metastable circles: linearly oscillatory (positive cusp second derivative) yet not a
global minimum of the phase potential — the round-3 band in elastica language. -/
theorem metastable_circle {k σ a : ℝ} (hloc : 0 < 3 * (1 / 2) * a ^ 2 + (-σ / k))
    (hglob : (1 / 2) * a ^ 2 + (-σ / k) < 0) :
    IsLocalMin (potential (1 / 2) (-σ / k) (input (1 / 2) (-σ / k) a)) a ∧
      ¬ GlobalMin (1 / 2) (-σ / k) a := by
  have := RoundTrip03.metastable_local_not_global (by norm_num : (0 : ℝ) < 1 / 2) hloc hglob
  exact this

/-- A concrete metastable circle: `k = 1`, `σ = 1`, `a = 1` (`3/2 - 1 > 0 > 1/2 - 1`). -/
theorem metastable_circle_example :
    IsLocalMin (potential (1 / 2) (-1 / 1) (input (1 / 2) (-1 / 1) 1)) 1 ∧
      ¬ GlobalMin (1 / 2) (-1 / 1) 1 :=
  metastable_circle (by norm_num) (by norm_num)

end RoundTrip06
