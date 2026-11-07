import PrismHysteresisReadout

/-!
# Fluid prism phase memory: an effective capillary barrier, optical path and readout

This extends the verified, purely algebraic two-mode probe in PR #89. An
ideal two-state fluid interface is encoded at dimensionless heights ±1. The
quartic potential is an *effective phenomenological hypothesis*, NOT derived
from a Young-Laplace boundary value problem or a thermocapillary PDE.

Under a *chosen half-wave calibration* a single-pass path phase is
pi*(h+1)/2, and a balanced ideal interferometer produces contrast as a
function of h. We connect this phase readout to the pre-existing classical
two-amplitude witness and to a separate ideal threshold-write hysteron.

No actual N-BASF64 prism, Maxwell propagation, energy-dependent writing
thresholds, photodetector backaction, liquid stability times, or measurements
are modeled. In particular the two optical observables are calibrated to
agree on these two encoded states, not proved equal in an actual device.
-/

noncomputable section
namespace FluidPrismPhaseMemory

open DarkBrightObservation PrismHysteresisReadout

/-- Effective quartic interface energy in nondimensional coordinates. -/
def energy (h u : ℝ) : ℝ := (h^2 - 1)^2 / 4 - u*h

/-- Formal first and second derivatives of the effective potential. -/
def energySlope (h u : ℝ) : ℝ := h*(h^2-1)-u
def energyCurvature (h : ℝ) : ℝ := 3*h^2-1

theorem neutral_energy_nonnegative (h : ℝ) : 0 ≤ energy h 0 := by
  dsimp [energy]
  nlinarith [sq_nonneg (h^2 - 1)]

theorem neutral_energy_left : energy (-1) 0 = 0 := by
  norm_num [energy]

theorem neutral_energy_right : energy 1 0 = 0 := by
  norm_num [energy]

theorem neutral_barrier : energy 0 0 = 1/4 := by
  norm_num [energy]

theorem neutral_energy_zero_only (h : ℝ) (he : energy h 0 = 0) :
    h = 1 ∨ h = -1 := by
  have hs : (h^2-1)^2 = 0 := by
    dsimp [energy] at he
    nlinarith [he]
  have hm : (h^2-1)*(h^2-1)=0 := by nlinarith [hs]
  have hr : h^2-1=0 := by
    rcases mul_eq_zero.mp hm with h0 | h0
    · exact h0
    · exact h0
  have hf : (h-1)*(h+1)=0 := by nlinarith [hr]
  rcases mul_eq_zero.mp hf with h0 | h0
  · left; linarith
  · right; linarith

theorem neutral_stationary_left :
    energySlope (-1) 0 = 0 ∧ energyCurvature (-1) = 2 := by
  norm_num [energySlope, energyCurvature]

theorem neutral_stationary_right :
    energySlope 1 0 = 0 ∧ energyCurvature 1 = 2 := by
  norm_num [energySlope, energyCurvature]

theorem neutral_stationary_barrier :
    energySlope 0 0 = 0 ∧ energyCurvature 0 = -1 := by
  norm_num [energySlope, energyCurvature]

/-- Idealized two-valued fluid displacement. Physical film thickness is
    t0 + a*h with t0 sufficiently larger than a. -/
def height (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem height_false : height false = -1 := rfl
@[simp] theorem height_true : height true = 1 := rfl

theorem every_encoded_height_minimizes (b : Bool) :
    energy (height b) 0 = 0 := by
  cases b
  · exact neutral_energy_left
  · exact neutral_energy_right

/-- Single-pass optical phase from an index contrast and excess path length.
    All lengths and wavelength use the same units. -/
def opticalPhase (indexContrast path wavelength : ℝ) : ℝ :=
  2 * Real.pi * indexContrast * path / wavelength

/-- One-parameter normalized film phase at quadrature bias: one state
    gives phase 0 and the other phase pi. -/
def phase (h : ℝ) : ℝ := Real.pi * (h+1) / 2

/-- A half-wave path calibration 4*deltaN*a=lambda produces the normalized
    phase when the excess optical path is a*(h+1). This is conditional on
    a chosen interferometer geometry, not a consequence of prism refraction. -/
theorem calibrated_phase (deltaN a wavelength h : ℝ)
    (hw : wavelength ≠ 0)
    (hcal : 4*deltaN*a = wavelength) :
    opticalPhase deltaN (a*(h+1)) wavelength = phase h := by
  unfold opticalPhase phase
  apply (div_eq_iff hw).2
  rw [← hcal]
  ring

/-- Normalized ideal interferometric output port. -/
def port (h : ℝ) : ℝ := (1 + Real.cos (phase h)) / 2

theorem phase_false : phase (height false) = 0 := by
  norm_num [height, phase]

theorem phase_true : phase (height true) = Real.pi := by
  norm_num [height, phase]

theorem port_false : port (height false) = 1 := by
  rw [port, phase_false]
  norm_num

theorem port_true : port (height true) = 0 := by
  rw [port, phase_true]
  simp [Real.cos_pi]

/-- Identifying one of the two idealized states from one phase readout. -/
theorem port_separates : port (height false) ≠ port (height true) := by
  rw [port_false, port_true]
  norm_num

theorem port_injective_on_bits :
    Function.Injective (fun b : Bool => port (height b)) := by
  intro b c he
  cases b <;> cases c
  · rfl
  · exact False.elim (port_separates he)
  · exact False.elim (port_separates he.symm)
  · rfl

/-- The output port is physically normalized to [0,1] in the ideal model. -/
theorem port_bounded (h : ℝ) : 0 ≤ port h ∧ port h ≤ 1 := by
  have hlow := Real.neg_one_le_cos (phase h)
  have hhigh := Real.cos_le_one (phase h)
  dsimp [port]
  constructor <;> linarith

/-- Phase ambiguity: two heights differing by four normalized units give
    the same interferometer output, so a single cosine channel is not a
    universal height sensor. -/
theorem port_period_four (h : ℝ) : port (h+4) = port h := by
  have hp : phase (h+4) = phase h + 2*Real.pi := by
    dsimp [phase]
    ring
  dsimp [port]
  rw [hp, Real.cos_add]
  simp

/-- The previous PR #89's two-mode differential contrast agrees, on the
    two chosen encodings only, with a calibrated affine reading of the
    fluid interferometer port. This is a stipulated encoding calibration. -/
theorem calibrated_probe_relation (b : Bool) :
    readSignal b = (144/25 : ℝ) * (1 - 2 * port (height b)) := by
  cases b
  · rw [read_false, port_false]
    norm_num
  · rw [read_true, port_true]
    norm_num

/-- Writing at high/low pulse and then returning to neutral drive does not
    erase the selected state in the ideal two-threshold latch. -/
theorem retained_height_high :
    height (write (write false (2:ℝ)) (0:ℝ)) = 1 := by
  rw [write_high, hold_zero, height_true]

theorem retained_height_low :
    height (write (write false (-2:ℝ)) (0:ℝ)) = -1 := by
  rw [write_low, hold_zero, height_false]

theorem hysteretic_optical_separation :
    port (height (write (write false (2:ℝ)) (0:ℝ))) ≠
    port (height (write (write false (-2:ℝ)) (0:ℝ))) := by
  rw [retained_height_high, retained_height_low]
  change port (height true) ≠ port (height false)
  exact port_separates.symm

/-- In the pure bit-state update law, a neutral read input preserves all
    prior history. This is NOT a guarantee of physical measurement backaction. -/
theorem neutral_probe_does_not_rewrite (b : Bool) :
    write b (0:ℝ) = b :=
  hold_zero b

/-- Independent idealized fluid cells can in principle be optically addressed
    without confusing their bit strings, provided their readout ports are
    separately measurable. No cross-talk or packing constraints are modeled. -/
def cellReadout (n : ℕ) (memory : Fin n → Bool) : Fin n → ℝ :=
  fun i => port (height (memory i))

theorem cell_readout_injective (n : ℕ) :
    Function.Injective (cellReadout n) := by
  intro a b hab
  funext i
  exact port_injective_on_bits (congrFun hab i)

theorem memory_count (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2^n := by
  simp

/-- Robust against scalar detector error strictly smaller than 1/2
    in *normalized ideal output units*, for each encoded bit. -/
theorem noisy_low_above_threshold (error : ℝ) (he : |error| < 1/2) :
    1/2 < port (height false) + error := by
  rw [port_false]
  have hlo := (abs_lt.mp he).1
  linarith

theorem noisy_high_below_threshold (error : ℝ) (he : |error| < 1/2) :
    port (height true) + error < 1/2 := by
  rw [port_true]
  have hhi := (abs_lt.mp he).2
  linarith

end FluidPrismPhaseMemory
