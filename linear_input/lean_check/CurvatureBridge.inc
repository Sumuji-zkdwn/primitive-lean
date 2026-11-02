import Elastica.Equations

/-!
The classical curvature ODE and its actual arclength phase curve.
The optional nonzero input is an explicit forcing assumption, not a consequence
of adding a linear curvature density to the original variational problem.
-/
noncomputable section
namespace LinearInputCurvatureBridge

open LinearInputDesign LinearInputGradient Set

/-- The shear identifies the explicit energy with the classical quartic first integral. -/
theorem energy_shear (k sigma u x p : ℝ) :
    E (1 / 2) (-sigma / k) u x (p + Real.sqrt 2 * x) =
      p ^ 2 / 2 + x ^ 4 / 8 - sigma * x ^ 2 / (2 * k) - u * x := by
  unfold E f
  ring

theorem gy_shear (x p : ℝ) : gy x (p + Real.sqrt 2 * x) = p := by
  unfold gy
  ring

theorem gx_shear (k sigma u x p : ℝ) :
    gx (1 / 2) (-sigma / k) u x (p + Real.sqrt 2 * x) =
      x ^ 3 / 2 - sigma / k * x - Real.sqrt 2 * p - u := by
  unfold gx
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- A forced curvature equation gives the actual phase velocities `(gy, -gx)`.
The variable is arclength; no time evolution or solution existence is asserted. -/
theorem forced_phase_hasDerivAt {k sigma u s : ℝ} {kappa : ℝ → ℝ}
    (hk : k ≠ 0) (hκ : ContDiff ℝ 2 kappa)
    (heq : k * deriv (deriv kappa) s + k * (kappa s) ^ 3 / 2 - sigma * kappa s = k * u) :
    HasDerivAt kappa (gy (kappa s) (deriv kappa s + Real.sqrt 2 * kappa s)) s ∧
    HasDerivAt (fun t => deriv kappa t + Real.sqrt 2 * kappa t)
      (-gx (1 / 2) (-sigma / k) u (kappa s)
        (deriv kappa s + Real.sqrt 2 * kappa s)) s := by
  have hx := (hκ.differentiable (by norm_num) s).hasDerivAt
  have hp := (hκ.differentiable_deriv_two s).hasDerivAt
  have hacc : deriv (deriv kappa) s = sigma / k * kappa s - (kappa s) ^ 3 / 2 + u := by
    apply (mul_left_cancel₀ hk)
    field_simp
    nlinarith [heq]
  constructor
  · simpa only [gy_shear] using hx
  · convert hp.add (hx.const_mul (Real.sqrt 2)) using 1
    rw [gx_shear, hacc]
    ring

/-- The unforced classical elastica curvature equation gives the zero-input phase system. -/
theorem phase_hasDerivAt {k sigma s : ℝ} {kappa : ℝ → ℝ}
    (hk : k ≠ 0) (hκ : ContDiff ℝ 2 kappa)
    (heq : k * deriv (deriv kappa) s + k * (kappa s) ^ 3 / 2 - sigma * kappa s = 0) :
    HasDerivAt kappa (gy (kappa s) (deriv kappa s + Real.sqrt 2 * kappa s)) s ∧
    HasDerivAt (fun t => deriv kappa t + Real.sqrt 2 * kappa t)
      (-gx (1 / 2) (-sigma / k) 0 (kappa s)
        (deriv kappa s + Real.sqrt 2 * kappa s)) s := by
  exact forced_phase_hasDerivAt hk hκ (by simpa only [mul_zero] using heq)

/-- Conversely the phase velocities imply the same forced curvature equation.
The derivative here is the actual derivative of the sheared curvature curve. -/
theorem forced_curvature_of_phase {k sigma u s : ℝ} {kappa : ℝ → ℝ}
    (hk : k ≠ 0) (hκ : ContDiff ℝ 2 kappa)
    (hy : HasDerivAt (fun t => deriv kappa t + Real.sqrt 2 * kappa t)
      (-gx (1 / 2) (-sigma / k) u (kappa s)
        (deriv kappa s + Real.sqrt 2 * kappa s)) s) :
    k * deriv (deriv kappa) s + k * (kappa s) ^ 3 / 2 - sigma * kappa s = k * u := by
  have hx := (hκ.differentiable (by norm_num) s).hasDerivAt
  have hp := (hκ.differentiable_deriv_two s).hasDerivAt
  have h := hy.unique (hp.add (hx.const_mul (Real.sqrt 2)))
  rw [gx_shear] at h
  have hmul := congrArg (fun q : ℝ => k * q) h
  field_simp at hmul
  nlinarith [hmul]

/-- The actual derivative of the energy vanishes along a fixed-input phase curve. -/
theorem forced_energy_hasDerivAt_zero {k sigma u s : ℝ} {kappa : ℝ → ℝ}
    (hk : k ≠ 0) (hκ : ContDiff ℝ 2 kappa)
    (heq : k * deriv (deriv kappa) s + k * (kappa s) ^ 3 / 2 - sigma * kappa s = k * u) :
    HasDerivAt (fun t => E (1 / 2) (-sigma / k) u (kappa t)
      (deriv kappa t + Real.sqrt 2 * kappa t)) 0 s := by
  obtain ⟨hx, hy⟩ := forced_phase_hasDerivAt hk hκ heq
  convert hasDerivAt_energy_curve (1 / 2) (-sigma / k) hx hy (hasDerivAt_const s u) using 1
  ring

theorem energy_hasDerivAt_zero {k sigma s : ℝ} {kappa : ℝ → ℝ}
    (hk : k ≠ 0) (hκ : ContDiff ℝ 2 kappa)
    (heq : k * deriv (deriv kappa) s + k * (kappa s) ^ 3 / 2 - sigma * kappa s = 0) :
    HasDerivAt (fun t => E (1 / 2) (-sigma / k) 0 (kappa t)
      (deriv kappa t + Real.sqrt 2 * kappa t)) 0 s := by
  exact forced_energy_hasDerivAt_zero hk hκ (by simpa only [mul_zero] using heq)

/-- A connected open interval turns the actual vanishing derivative into a conserved value. -/
theorem forced_energy_constant {k sigma u a b : ℝ} {kappa : ℝ → ℝ}
    (hk : k ≠ 0) (hκ : ContDiff ℝ 2 kappa)
    (heq : ∀ s ∈ Ioo a b,
      k * deriv (deriv kappa) s + k * (kappa s) ^ 3 / 2 - sigma * kappa s = k * u) :
    ∃ c : ℝ, ∀ s ∈ Ioo a b,
      E (1 / 2) (-sigma / k) u (kappa s)
        (deriv kappa s + Real.sqrt 2 * kappa s) = c := by
  apply isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
  · intro s hs
    exact (forced_energy_hasDerivAt_zero hk hκ (heq s hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    exact (forced_energy_hasDerivAt_zero hk hκ (heq s hs)).deriv

theorem energy_constant {k sigma a b : ℝ} {kappa : ℝ → ℝ}
    (hk : k ≠ 0) (hκ : ContDiff ℝ 2 kappa)
    (heq : ∀ s ∈ Ioo a b,
      k * deriv (deriv kappa) s + k * (kappa s) ^ 3 / 2 - sigma * kappa s = 0) :
    ∃ c : ℝ, ∀ s ∈ Ioo a b,
      E (1 / 2) (-sigma / k) 0 (kappa s)
        (deriv kappa s + Real.sqrt 2 * kappa s) = c := by
  exact forced_energy_constant hk hκ (fun s hs => by simpa only [mul_zero] using heq s hs)

end LinearInputCurvatureBridge
