import Mathlib.Tactic

/-!
# General-time 5D Ricci-flat circle cosmology: algebraic certificates

For the proper-time homogeneous metric
  ds5² = -dt² + a(t)² (dx₁²+dx₂²+dx₃²) + b(t)² dχ²
with positive C² a,b, let h=a'/a, f=b'/b, hp=h', fp=f'.
The *independent SymPy oracle*, not this Lean module, differentiates
the five-dimensional metric and confirms the Ricci component formulas.

Only algebraic consequences of those externally established formulas
are formalized here; none of the 5D tensor geometry, smooth global ODE
uniqueness, topological/physical KK statements are kernel-proved.
-/

namespace General5DVacuumRadion

def timeResidual (h f hp fp : ℝ) : ℝ :=
  -(3 * (hp + h ^ 2) + (fp + f ^ 2))

def externalResidual (h f hp : ℝ) : ℝ :=
  hp + h * (3 * h + f)

def circleResidual (h f fp : ℝ) : ℝ :=
  fp + f * (3 * h + f)

/-- The vacuum Hamiltonian constraint is h(h+f)=0. -/
theorem hamiltonian_factor (h f hp fp : ℝ) :
    timeResidual h f hp fp +
        3 * externalResidual h f hp +
        circleResidual h f fp =
      6 * h * (h + f) := by
  unfold timeResidual externalResidual circleResidual
  ring

/-- The spatial trace is the logarithmic second-volume residual. -/
theorem volume_trace_factor (h f hp fp : ℝ) :
    3 * externalResidual h f hp + circleResidual h f fp =
      (3 * hp + fp) + (3 * h + f) ^ 2 := by
  unfold externalResidual circleResidual
  ring

/-- A Ricci-flat homogeneous solution is either static externally
    at this time, or has opposite circle and external Hubble rates. -/
theorem branch_dichotomy (h f hp fp : ℝ)
    (ht : timeResidual h f hp fp = 0)
    (he : externalResidual h f hp = 0)
    (hf : circleResidual h f fp = 0) :
    h = 0 ∨ f = -h := by
  have ha := hamiltonian_factor h f hp fp
  rw [ht, he, hf] at ha
  have hproduct : h * (h + f) = 0 := by nlinarith [ha]
  rcases mul_eq_zero.mp hproduct with hzero | hop
  · exact Or.inl hzero
  · exact Or.inr (by linarith)

/-- Positive external expansion forces *negative* circle Hubble rate. -/
theorem expanding_opposite_rate (h f hp fp : ℝ)
    (ht : timeResidual h f hp fp = 0)
    (he : externalResidual h f hp = 0)
    (hf : circleResidual h f fp = 0)
    (hpos : 0 < h) : f = -h := by
  rcases branch_dichotomy h f hp fp ht he hf with hzero | hop
  · linarith
  · exact hop

/-- At an expanding point, all vacuum time derivatives are determined. -/
theorem expanding_rate_derivatives (h f hp fp : ℝ)
    (ht : timeResidual h f hp fp = 0)
    (he : externalResidual h f hp = 0)
    (hf : circleResidual h f fp = 0)
    (hpos : 0 < h) :
    hp = -2 * h ^ 2 ∧ fp = 2 * h ^ 2 := by
  have hop := expanding_opposite_rate h f hp fp ht he hf hpos
  constructor
  · unfold externalResidual at he
    rw [hop] at he
    nlinarith [he]
  · unfold circleResidual at hf
    rw [hop] at hf
    nlinarith [hf]

/-- The internal circle cannot have even momentarily zero logarithmic
    rate when the external three-space is expanding. -/
theorem no_expansion_with_stationary_circle (h f hp fp : ℝ)
    (ht : timeResidual h f hp fp = 0)
    (he : externalResidual h f hp = 0)
    (hf : circleResidual h f fp = 0)
    (hpos : 0 < h) (fcircle : f = 0) : False := by
  have hop := expanding_opposite_rate h f hp fp ht he hf hpos
  linarith

/-- A non-contracting internal circle is incompatible with expansion. -/
theorem no_expansion_with_nondecreasing_circle (h f hp fp : ℝ)
    (ht : timeResidual h f hp fp = 0)
    (he : externalResidual h f hp = 0)
    (hf : circleResidual h f fp = 0)
    (hpos : 0 < h) (fnn : 0 ≤ f) : False := by
  have hop := expanding_opposite_rate h f hp fp ht he hf hpos
  linarith

/-- The exact zero-volume-acceleration identity after substituting
    vacuum spatial equations, corresponding externally to (a³b)''=0. -/
theorem vacuum_volume_trace_zero (h f hp fp : ℝ)
    (he : externalResidual h f hp = 0)
    (hf : circleResidual h f fp = 0) :
    (3 * hp + fp) + (3 * h + f) ^ 2 = 0 := by
  have ha := volume_trace_factor h f hp fp
  rw [he, hf] at ha
  linarith

/-- If external expansion is absent, the circle's Ricci equation is
    simply f' = - f². -/
theorem static_external_circle_evolution (f fp : ℝ)
    (hf : circleResidual 0 f fp = 0) :
    fp = -(f ^ 2) := by
  unfold circleResidual at hf
  nlinarith

/-- Purely metric-defined Einstein-frame acceleration, multiplied by
    the positive circle radius, has numerator hp+fp/2+h(h+f/2). -/
noncomputable def einsteinAccelNumerator (h f hp fp : ℝ) : ℝ :=
  hp + fp / 2 + h * (h + f / 2)

/-- On an expanding vacuum branch the numerator is -h²/2. -/
theorem expanding_einstein_deceleration_identity (h f hp fp : ℝ)
    (ht : timeResidual h f hp fp = 0)
    (he : externalResidual h f hp = 0)
    (hf : circleResidual h f fp = 0)
    (hpos : 0 < h) :
    einsteinAccelNumerator h f hp fp = -(h ^ 2) / 2 := by
  obtain ⟨hprime, fprime⟩ :=
    expanding_rate_derivatives h f hp fp ht he hf hpos
  have hop := expanding_opposite_rate h f hp fp ht he hf hpos
  unfold einsteinAccelNumerator
  rw [hprime, fprime, hop]
  ring

/-- Under the same Ricci-flat assumptions, Einstein-frame cosmic
    acceleration is strictly negative for any positive circle radius. -/
theorem expanding_einstein_decelerates (h f hp fp : ℝ)
    (ht : timeResidual h f hp fp = 0)
    (he : externalResidual h f hp = 0)
    (hf : circleResidual h f fp = 0)
    (hpos : 0 < h) :
    einsteinAccelNumerator h f hp fp < 0 := by
  rw [expanding_einstein_deceleration_identity h f hp fp ht he hf hpos]
  nlinarith [sq_pos_of_pos hpos]

end General5DVacuumRadion
