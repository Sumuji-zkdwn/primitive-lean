import PADFourLayer

/-!
# Four-layer PAD reconstruction and calibration ambiguity

Additive sidecar to PR #97 and the D-optimal determinant certificate of PR #101.
The statements are over rational four-layer coefficients and do NOT establish
real liquid-jet transport, electron-energy calibration, or stochastic stability.
-/

namespace PADFourLayerCalibration

open PADFourLayer

/-- Subtract the known mass and first-moment contributions. -/
def residual (x : ℚ) (p : Profile) : ℚ :=
  response x p - mass p - (x - 1) * mean p

/-- The cubic inverse problem becomes an affine interpolation after division
by `(x - 1)^2`. This identity itself needs no nonvanishing assumption. -/
theorem residual_factor (p : Profile) (x : ℚ) :
    residual x p = (x - 1)^2 * (p.p2 + (x + 2) * p.p3) := by
  cases p with
  | mk p0 p1 p2 p3 =>
    dsimp [residual, response, mass, mean]
    ring

/-- Denominator-free reconstruction identity for p3. -/
theorem recover_p3 (p : Profile) (t s : ℚ) :
    (s-t)*(t-1)^2*(s-1)^2*p.p3 =
      (t-1)^2*residual s p - (s-1)^2*residual t p := by
  rw [residual_factor, residual_factor]
  ring

/-- Denominator-free reconstruction identity for p2. -/
theorem recover_p2 (p : Profile) (t s : ℚ) :
    (s-t)*(t-1)^2*(s-1)^2*p.p2 =
      (s+2)*(s-1)^2*residual t p - (t+2)*(t-1)^2*residual s p := by
  rw [residual_factor, residual_factor]
  ring

/-- Exact effect of uncertain independently measured mass and mean on the
residual used in reconstruction. -/
theorem residual_difference (p q : Profile) (x : ℚ) :
    residual x p - residual x q =
      (response x p - response x q) - (mass p - mass q) -
      (x-1)*(mean p - mean q) := by
  unfold residual
  ring

/-- Perturb all four coefficients in a direction invisible at readout x.
The direction is `(y-1)^2*(y-x)` in polynomial form. -/
def perturb (p : Profile) (x eps : ℚ) : Profile :=
  ⟨p.p0-eps*x, p.p1+eps*(1+2*x), p.p2-eps*(x+2), p.p3+eps⟩

theorem perturb_mass (p : Profile) (x eps : ℚ) :
    mass (perturb p x eps) = mass p := by
  cases p with
  | mk p0 p1 p2 p3 =>
    dsimp [mass, perturb]
    ring

theorem perturb_mean (p : Profile) (x eps : ℚ) :
    mean (perturb p x eps) = mean p := by
  cases p with
  | mk p0 p1 p2 p3 =>
    dsimp [mean, perturb]
    ring

theorem perturb_response (p : Profile) (x eps y : ℚ) :
    response y (perturb p x eps) - response y p =
      eps*(y-1)^2*(y-x) := by
  cases p with
  | mk p0 p1 p2 p3 =>
    dsimp [response, perturb]
    ring

theorem perturb_probe (p : Profile) (x eps : ℚ) :
    response x (perturb p x eps) = response x p := by
  have h := perturb_response p x eps x
  have hz : eps*(x-1)^2*(x-x) = 0 := by ring
  rw [hz] at h
  linarith

theorem perturb_nontrivial (p : Profile) (x eps : ℚ) (he : eps ≠ 0) :
    perturb p x eps ≠ p := by
  intro h
  have hp3 : (perturb p x eps).p3 = p.p3 :=
    congrArg Profile.p3 h
  change p.p3 + eps = p.p3 at hp3
  have hz : eps = 0 := by linarith
  exact he hz

/-- If every energy may have its own latent profile, neither energy's single
readout identifies that profile, even with exactly known mass and mean.
The theorem does *not* assert a common profile shared by the energies. -/
theorem independent_energy_ambiguity
    (p : Profile) (t s eps1 eps2 : ℚ)
    (h1 : eps1 ≠ 0) (h2 : eps2 ≠ 0) :
    mass (perturb p t eps1) = mass p ∧
    mean (perturb p t eps1) = mean p ∧
    response t (perturb p t eps1) = response t p ∧
    perturb p t eps1 ≠ p ∧
    mass (perturb p s eps2) = mass p ∧
    mean (perturb p s eps2) = mean p ∧
    response s (perturb p s eps2) = response s p ∧
    perturb p s eps2 ≠ p := by
  exact ⟨perturb_mass p t eps1, perturb_mean p t eps1,
    perturb_probe p t eps1, perturb_nontrivial p t eps1 h1,
    perturb_mass p s eps2, perturb_mean p s eps2,
    perturb_probe p s eps2, perturb_nontrivial p s eps2 h2⟩

/-- The readout's finite-difference identity isolates parameter calibration
error, without invoking a derivative or a physical noise model. -/
theorem response_difference (p : Profile) (s t : ℚ) :
    response s p - response t p =
      (s-t)*(p.p1+(s+t)*p.p2+(s^2+s*t+t^2)*p.p3) := by
  cases p with
  | mk p0 p1 p2 p3 =>
    dsimp [response]
    ring

end PADFourLayerCalibration
