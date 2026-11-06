import Mathlib

/-!
# Two internal motions coupled to an outgoing scalar-wave channel

A conditional real classical model, not a photon or constituent-particle theorem.
The chosen nonnegative coupling energy is kappa/2 * (y-g*x1*x2)^2.
Its partial derivatives are proved, not postulated. The outgoing boundary law
2*c*y'=F is explicitly supplied in SolvesAt; it is not obtained here from a
weak/distributional PDE existence theorem. We derive local and integrated
energy balance and exact positivity of the emitted-work integral.
-/

noncomputable section
open Set MeasureTheory
namespace TwoMotionEmission

def coupling (κ g x₁ x₂ y : ℝ) : ℝ := κ / 2 * (y - g*x₁*x₂)^2
def force (κ g x₁ x₂ y : ℝ) : ℝ := κ * (g*x₁*x₂ - y)
def mechanical (ω₁ ω₂ x₁ v₁ x₂ v₂ : ℝ) : ℝ :=
  (v₁^2 + ω₁^2*x₁^2 + v₂^2 + ω₂^2*x₂^2) / 2
def energy (κ g ω₁ ω₂ x₁ v₁ x₂ v₂ y : ℝ) : ℝ :=
  mechanical ω₁ ω₂ x₁ v₁ x₂ v₂ + coupling κ g x₁ x₂ y

def power (c f : ℝ) : ℝ := f^2 / (2*c)
def emitted (c : ℝ) (F : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in 0..T, power c (F t)

theorem coupling_expansion (κ g x₁ x₂ y : ℝ) :
    coupling κ g x₁ x₂ y =
      κ*y^2/2 - (κ*g*x₁*x₂)*y + κ*g^2*x₁^2*x₂^2/2 := by
  unfold coupling
  ring

theorem coupling_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (g x₁ x₂ y : ℝ) :
    0 ≤ coupling κ g x₁ x₂ y := by
  unfold coupling
  positivity

theorem mechanical_nonneg (ω₁ ω₂ x₁ v₁ x₂ v₂ : ℝ) :
    0 ≤ mechanical ω₁ ω₂ x₁ v₁ x₂ v₂ := by
  unfold mechanical
  positivity

theorem energy_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (g ω₁ ω₂ x₁ v₁ x₂ v₂ y : ℝ) :
    0 ≤ energy κ g ω₁ ω₂ x₁ v₁ x₂ v₂ y :=
  add_nonneg (mechanical_nonneg _ _ _ _ _ _) (coupling_nonneg hκ _ _ _ _)

/-- The actual derivative of the potential in the outgoing boundary variable. -/
theorem coupling_hasDerivAt_y (κ g x₁ x₂ y : ℝ) :
    HasDerivAt (fun z => coupling κ g x₁ x₂ z) (-force κ g x₁ x₂ y) y := by
  convert (((hasDerivAt_id y).sub_const (g*x₁*x₂)).pow 2).const_mul (κ/2) using 1 <;>
    dsimp [coupling, force] <;> ring

/-- Backreaction on the first internal motion comes from the same potential. -/
theorem coupling_hasDerivAt_x1 (κ g x₁ x₂ y : ℝ) :
    HasDerivAt (fun z => coupling κ g z x₂ y)
      (g*x₂*force κ g x₁ x₂ y) x₁ := by
  convert (((((hasDerivAt_id x₁).const_mul g).mul_const x₂).const_sub y).pow 2).const_mul (κ/2) using 1 <;>
    dsimp [coupling, force] <;> ring

theorem coupling_hasDerivAt_x2 (κ g x₁ x₂ y : ℝ) :
    HasDerivAt (fun z => coupling κ g x₁ z y)
      (g*x₁*force κ g x₁ x₂ y) x₂ := by
  convert ((((hasDerivAt_id x₂).const_mul (g*x₁)).const_sub y).pow 2).const_mul (κ/2) using 1 <;>
    dsimp [coupling, force] <;> ring

structure Path where
  x₁ : ℝ → ℝ
  v₁ : ℝ → ℝ
  x₂ : ℝ → ℝ
  v₂ : ℝ → ℝ
  y : ℝ → ℝ

def forceAlong (κ g : ℝ) (z : Path) (t : ℝ) : ℝ :=
  force κ g (z.x₁ t) (z.x₂ t) (z.y t)

def energyAlong (κ g ω₁ ω₂ : ℝ) (z : Path) (t : ℝ) : ℝ :=
  energy κ g ω₁ ω₂ (z.x₁ t) (z.v₁ t) (z.x₂ t) (z.v₂ t) (z.y t)

/-- These are the explicitly chosen reduced dynamics at one time.
No existence, uniqueness or distributional reduction is included as a field. -/
structure SolvesAt (κ g ω₁ ω₂ c : ℝ) (z : Path) (t : ℝ) : Prop where
  dx₁ : HasDerivAt z.x₁ (z.v₁ t) t
  dv₁ : HasDerivAt z.v₁ (-ω₁^2*z.x₁ t - g*z.x₂ t*forceAlong κ g z t) t
  dx₂ : HasDerivAt z.x₂ (z.v₂ t) t
  dv₂ : HasDerivAt z.v₂ (-ω₂^2*z.x₂ t - g*z.x₁ t*forceAlong κ g z t) t
  dy : HasDerivAt z.y (forceAlong κ g z t / (2*c)) t

/-- Chain rule for arbitrary instantaneous velocities/accelerations. -/
theorem energy_chain_rule (κ g ω₁ ω₂ : ℝ) (z : Path) (t a₁ a₂ w : ℝ)
    (hx₁ : HasDerivAt z.x₁ (z.v₁ t) t) (hv₁ : HasDerivAt z.v₁ a₁ t)
    (hx₂ : HasDerivAt z.x₂ (z.v₂ t) t) (hv₂ : HasDerivAt z.v₂ a₂ t)
    (hy : HasDerivAt z.y w t) :
    HasDerivAt (energyAlong κ g ω₁ ω₂ z)
      (z.v₁ t * (a₁ + ω₁^2*z.x₁ t + g*z.x₂ t*forceAlong κ g z t) +
       z.v₂ t * (a₂ + ω₂^2*z.x₂ t + g*z.x₁ t*forceAlong κ g z t) -
       forceAlong κ g z t*w) t := by
  have hm := ((((hv₁.pow 2).add ((hx₁.pow 2).const_mul (ω₁^2))).add
    (hv₂.pow 2)).add ((hx₂.pow 2).const_mul (ω₂^2))).div_const 2
  have hi := ((hy.sub (((hx₁.const_mul g).mul hx₂))).pow 2).const_mul (κ/2)
  convert hm.add hi using 1 <;>
    dsimp [energyAlong, energy, mechanical, coupling, forceAlong, force] <;> ring

/-- Energy loss is a derived consequence of the supplied equations. -/
theorem energy_hasDerivAt (κ g ω₁ ω₂ c : ℝ) (z : Path) (t : ℝ)
    (hz : SolvesAt κ g ω₁ ω₂ c z t) :
    HasDerivAt (energyAlong κ g ω₁ ω₂ z)
      (-power c (forceAlong κ g z t)) t := by
  have h := energy_chain_rule κ g ω₁ ω₂ z t _ _ _
    hz.dx₁ hz.dv₁ hz.dx₂ hz.dv₂ hz.dy
  convert h using 1 <;> dsimp [power] <;> ring

theorem power_nonneg {c : ℝ} (hc : 0 < c) (f : ℝ) : 0 ≤ power c f := by
  exact div_nonneg (sq_nonneg f) (le_of_lt (mul_pos (by norm_num) hc))

theorem power_pos_iff {c : ℝ} (hc : 0 < c) (f : ℝ) :
    0 < power c f ↔ f ≠ 0 := by
  unfold power
  rw [div_pos_iff_of_pos_right (mul_pos (by norm_num) hc), sq_pos_iff]

theorem forceAlong_continuousOn (κ g ω₁ ω₂ c : ℝ) (z : Path) (S : Set ℝ)
    (hz : ∀ t ∈ S, SolvesAt κ g ω₁ ω₂ c z t) :
    ContinuousOn (forceAlong κ g z) S := by
  have h₁ : ContinuousOn z.x₁ S := fun t ht => (hz t ht).dx₁.continuousAt.continuousWithinAt
  have h₂ : ContinuousOn z.x₂ S := fun t ht => (hz t ht).dx₂.continuousAt.continuousWithinAt
  have hy : ContinuousOn z.y S := fun t ht => (hz t ht).dy.continuousAt.continuousWithinAt
  exact ((((h₁.const_mul g).mul h₂).sub hy).const_mul κ)

/-- Integrated energy balance uses the actual interval integral and FTC. -/
theorem energy_balance (κ g ω₁ ω₂ c T : ℝ) (z : Path)
    (hz : ∀ t ∈ uIcc 0 T, SolvesAt κ g ω₁ ω₂ c z t) :
    energyAlong κ g ω₁ ω₂ z T + emitted c (forceAlong κ g z) T =
      energyAlong κ g ω₁ ω₂ z 0 := by
  have hF := forceAlong_continuousOn κ g ω₁ ω₂ c z (uIcc 0 T) hz
  have hp : ContinuousOn (fun t => power c (forceAlong κ g z t)) (uIcc 0 T) :=
    (hF.pow 2).div_const (2*c)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => energy_hasDerivAt κ g ω₁ ω₂ c z t (hz t ht))
    hp.neg.intervalIntegrable
  rw [intervalIntegral.integral_neg] at h
  change -emitted c (forceAlong κ g z) T =
    energyAlong κ g ω₁ ω₂ z T - energyAlong κ g ω₁ ω₂ z 0 at h
  linarith

theorem emitted_nonneg {c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T) (F : ℝ → ℝ) :
    0 ≤ emitted c F T := by
  apply intervalIntegral.integral_nonneg hT
  intro t ht
  exact power_nonneg hc (F t)

/-- Continuity prevents a nonzero force confined to a measure-zero instant. -/
theorem emitted_pos_iff {c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc 0 T)) :
    0 < emitted c F T ↔ ∃ t ∈ Icc 0 T, F t ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have he : emitted c F T = 0 := by
      unfold emitted
      calc
        (∫ t in 0..T, power c (F t)) = ∫ t in 0..T, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hT.le] at ht
          simp [power, hn t ht]
        _ = 0 := by simp
    linarith
  · rintro ⟨t, ht, hft⟩
    apply intervalIntegral.integral_pos hT ((hF.pow 2).div_const (2*c))
    · intro u hu
      exact power_nonneg hc (F u)
    · exact ⟨t, ht, (power_pos_iff hc (F t)).2 hft⟩

theorem emitted_le_initial_energy {κ c T : ℝ} (hκ : 0 ≤ κ) (hc : 0 < c)
    (hT : 0 ≤ T) (g ω₁ ω₂ : ℝ) (z : Path)
    (hz : ∀ t ∈ Icc 0 T, SolvesAt κ g ω₁ ω₂ c z t) :
    0 ≤ emitted c (forceAlong κ g z) T ∧
      emitted c (forceAlong κ g z) T ≤ energyAlong κ g ω₁ ω₂ z 0 := by
  have hb := energy_balance κ g ω₁ ω₂ c T z (by simpa [uIcc_of_le hT] using hz)
  have hn := energy_nonneg hκ g ω₁ ω₂ (z.x₁ T) (z.v₁ T) (z.x₂ T) (z.v₂ T) (z.y T)
  exact ⟨emitted_nonneg hc hT _, by change 0 ≤ energyAlong κ g ω₁ ω₂ z T at hn; linarith⟩

/-- Outgoing branches; a causal past and their PDE existence are separate hypotheses. -/
def rightWave (c : ℝ) (y : ℝ → ℝ) (s t : ℝ) : ℝ := y (t-s/c)
def leftWave (c : ℝ) (y : ℝ → ℝ) (s t : ℝ) : ℝ := y (t+s/c)
def waveDensity (c qt qs : ℝ) : ℝ := (qt^2+c^2*qs^2)/2
def waveFlux (c qt qs : ℝ) : ℝ := -c^2*qt*qs

theorem rightWave_time (c s t d : ℝ) (y : ℝ → ℝ)
    (hy : HasDerivAt y d (t-s/c)) :
    HasDerivAt (fun u => rightWave c y s u) d t := by
  simpa [rightWave] using hy.comp t ((hasDerivAt_id t).sub_const (s/c))

theorem leftWave_time (c s t d : ℝ) (y : ℝ → ℝ)
    (hy : HasDerivAt y d (t+s/c)) :
    HasDerivAt (fun u => leftWave c y s u) d t := by
  simpa [leftWave] using hy.comp t ((hasDerivAt_id t).add_const (s/c))

theorem rightWave_space (c s t d : ℝ) (y : ℝ → ℝ)
    (hy : HasDerivAt y d (t-s/c)) :
    HasDerivAt (fun u => rightWave c y u t) (-d/c) s := by
  convert hy.comp s (((hasDerivAt_id s).div_const c).const_sub t) using 1 <;>
    dsimp [rightWave] <;> ring

theorem leftWave_space (c s t d : ℝ) (y : ℝ → ℝ)
    (hy : HasDerivAt y d (t+s/c)) :
    HasDerivAt (fun u => leftWave c y u t) (d/c) s := by
  convert hy.comp s (((hasDerivAt_id s).div_const c).const_add t) using 1 <;>
    dsimp [leftWave] <;> ring

theorem outgoing_density {c : ℝ} (hc : c ≠ 0) (w : ℝ) :
    waveDensity c w (-w/c) = w^2 ∧ waveDensity c w (w/c) = w^2 := by
  constructor <;> unfold waveDensity <;> field_simp [hc] <;> ring

theorem outgoing_flux {c : ℝ} (hc : c ≠ 0) (w : ℝ) :
    waveFlux c w (-w/c) = c*w^2 ∧ waveFlux c w (w/c) = -c*w^2 := by
  constructor <;> unfold waveFlux <;> field_simp [hc] <;> ring

/-- The two outgoing fluxes add to the local loss rate. -/
theorem two_sided_flux {c : ℝ} (hc : c ≠ 0) (f : ℝ) :
    waveFlux c (f/(2*c)) (-((f/(2*c))/c)) -
      waveFlux c (f/(2*c)) ((f/(2*c))/c) = power c f := by
  rw [(outgoing_flux hc _).1, (outgoing_flux hc _).2]
  unfold power
  field_simp [hc]
  ring

/-- Boundary slope jump of the two smooth branches, without a distribution claim. -/
theorem source_slope_jump {c : ℝ} (hc : c ≠ 0) (f : ℝ) :
    -c^2 * (-((f/(2*c))/c) - (f/(2*c))/c) = f := by
  field_simp [hc]
  ring

/-- A signal already emitted travels on each characteristic after its source changes. -/
theorem outgoing_transport (c s t h : ℝ) (hc : c ≠ 0) (y : ℝ → ℝ) :
    rightWave c y (s+c*h) (t+h) = rightWave c y s t ∧
    leftWave c y (s-c*h) (t+h) = leftWave c y s t := by
  constructor <;> dsimp [rightWave, leftWave] <;> congr 1 <;> field_simp [hc] <;> ring

/-- Shifted quartic potential: the cubic coefficient is lambda*x0. -/
def quartic (k λ u x : ℝ) : ℝ := k*x^2/2 + λ*x^4/4 - u*x

theorem shifted_quartic (k λ x₀ η : ℝ) :
    quartic k λ (k*x₀+λ*x₀^3) (x₀+η) - quartic k λ (k*x₀+λ*x₀^3) x₀ =
    (k+3*λ*x₀^2)*η^2/2 + λ*x₀*η^3 + λ*η^4/4 := by
  unfold quartic
  ring

end TwoMotionEmission
