import DarkBrightObservation

/-!
# Prism-memory readout: hysteresis and a reversible amplitude probe

Mathematical model, not a claim about a bare prism or actual optical storage.
The two amplitudes are classical complex mode amplitudes. The binary latch is an
externally supplied ideal Preisach-style hysteron, not derived from N-BASF64,
fluid dynamics, Maxwell equations, or an elastica energy.

A balanced interference readout (unnormalized B plus/minus iD intensities) detects
a phase-sensitive difference that is invisible in the initial coherence Q
and total power. The reversible mixer is ideal: real detectors, leakage,
absorption, disturbances of the liquid and actual nondemolition measurement
are NOT captured by these equations.
-/

noncomputable section
namespace PrismHysteresisReadout

open DarkBrightObservation

/-- Intensity of the unnormalized coherent combination B + iD. -/
def intensityPlus (x : Spinor) : ℝ :=
  (x.br - x.di)^2 + (x.bi + x.dr)^2

/-- Intensity of the unnormalized coherent combination B - iD. -/
def intensityMinus (x : Spinor) : ℝ :=
  (x.br + x.di)^2 + (x.bi - x.dr)^2

/-- A balanced detector measures four times the imaginary coherence. -/
theorem balanced_difference (x : Spinor) :
    intensityPlus x - intensityMinus x = 4 * imQ x := by
  dsimp [intensityPlus, intensityMinus, imQ]
  ring

/-- Two phase-sensitive intensity differences exactly recover the hidden
    optical imbalance. This is a single ideal mixing pulse after a
    baseline measurement, not a claim of experimentally nondestructive readout. -/
theorem balanced_probe_recovers_delta (x : Spinor) :
    delta x =
      (25 * (intensityPlus (step () x) - intensityMinus (step () x)) +
        7 * (intensityPlus x - intensityMinus x)) / 48 := by
  calc
    delta x = (25 * imQ (step () x) + 7 * imQ x) / 12 :=
      one_probe_recovers_delta x
    _ = (25 * (intensityPlus (step () x) - intensityMinus (step () x)) +
        7 * (intensityPlus x - intensityMinus x)) / 48 := by
      rw [balanced_difference (step () x), balanced_difference x]
      ring

/-- Two candidate internal memory configurations: same initial coherence
    and same total intensity, but opposite hidden imbalance. -/
def encoded : Bool → Spinor
  | false => witnessLeft
  | true => witnessRight

def blindRead (h : Bool) : Observation := output (encoded h)

theorem blind_equivalence : blindRead false = blindRead true := by
  exact current_collision.1

theorem equal_initial_power : norm2 (encoded false) = norm2 (encoded true) := by
  exact current_collision.2

/-- The phase-biased readout after the exact unitary mixer. -/
def readSignal (h : Bool) : ℝ :=
  intensityPlus (step () (encoded h)) -
  intensityMinus (step () (encoded h))

theorem read_false : readSignal false = -(144 / 25 : ℝ) := by
  change intensityPlus (step () witnessLeft) -
    intensityMinus (step () witnessLeft) = -(144 / 25 : ℝ)
  rw [balanced_difference]
  have hi : imQ (step () witnessLeft) = (-36 / 25 : ℝ) :=
    congrArg Prod.snd next_values.1
  rw [hi]
  norm_num

theorem read_true : readSignal true = (144 / 25 : ℝ) := by
  change intensityPlus (step () witnessRight) -
    intensityMinus (step () witnessRight) = (144 / 25 : ℝ)
  rw [balanced_difference]
  have hi : imQ (step () witnessRight) = (36 / 25 : ℝ) :=
    congrArg Prod.snd next_values.2
  rw [hi]
  norm_num

theorem probe_separates : readSignal false ≠ readSignal true := by
  rw [read_false, read_true]
  norm_num

/-- For this exact 3/5,4/5 pulse, an inverse pulse restores all four
    amplitude coordinates; this is an algebraic identity, not a proof that
    the measurement itself is physically nondemolition. -/
theorem unmix_after_pulse (x : Spinor) :
    mix (3/5) (-4/5) (step () x) = x := by
  cases x with
  | mk br bi dr di =>
    simp only [step, mix, Spinor.mk.injEq]
    constructor
    · ring
    constructor
    · ring
    constructor
    · ring
    · ring

/-- A schematic read-then-restore operation. -/
def readAndRestore (x : Spinor) : ℝ × Spinor :=
  (intensityPlus (step () x) - intensityMinus (step () x),
    mix (3/5) (-4/5) (step () x))

theorem restore_state (x : Spinor) :
    (readAndRestore x).2 = x := by
  exact unmix_after_pulse x

theorem restore_encoded (h : Bool) :
    (readAndRestore (encoded h)).2 = encoded h := by
  exact restore_state (encoded h)

theorem read_encoded_signal (h : Bool) :
    (readAndRestore (encoded h)).1 = readSignal h := rfl

/-- Ideal two-threshold hysteron: high pulse sets true, low pulse
    sets false, intermediate inputs keep the existing state. -/
def write (h : Bool) (u : ℝ) : Bool :=
  if (1 : ℝ) ≤ u then true
  else if u ≤ (-1 : ℝ) then false
  else h

theorem write_high (h : Bool) : write h (2 : ℝ) = true := by
  norm_num [write]

theorem write_low (h : Bool) : write h (-2 : ℝ) = false := by
  norm_num [write]

theorem hold_zero (h : Bool) : write h (0 : ℝ) = h := by
  norm_num [write]

/-- Equal neutral input does not erase the difference written by
    opposite pulses. -/
theorem two_writes_retained :
    write (write false (2 : ℝ)) (0 : ℝ) ≠
      write (write false (-2 : ℝ)) (0 : ℝ) := by
  norm_num [write]

/-- The two latched states are invisible to the static coherence readout. -/
theorem written_states_blind :
    blindRead (write false (2 : ℝ)) =
      blindRead (write false (-2 : ℝ)) := by
  rw [write_high, write_low]
  exact blind_equivalence.symm

/-- But one phase-sensitive pulse distinguishes both histories. -/
theorem written_states_separate :
    readSignal (write false (2 : ℝ)) ≠
      readSignal (write false (-2 : ℝ)) := by
  rw [write_high, write_low]
  exact probe_separates.symm

/-- Exact readout and restoration of both written configurations. -/
theorem written_state_restored (h : Bool) (u : ℝ) :
    (readAndRestore (encoded (write h u))).2 = encoded (write h u) :=
  restore_encoded (write h u)

end PrismHysteresisReadout
