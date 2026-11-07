import Mathlib
import DarkBrightObservation

/-!
Intensity-only observation symmetry for the two-amplitude model.

This module imports the existing Spinor, mix, reQ, imQ, and output definitions,
but proves the exchange/intensity results directly from those definitions. It
does not use any of the existing DarkBrightObservation theorems.

The result is an algebraic observation limit for this supplied mixer. It does
not identify the amplitudes with physical constituents of a photon.
-/

noncomputable section
namespace DarkBrightIntensity

open DarkBrightObservation

/-- Exchange the two complex amplitudes B and D. -/
def exchange (x : Spinor) : Spinor := ⟨x.dr, x.di, x.br, x.bi⟩

/-- The toy intensity |Q|², where Q = B * conjugate(D). -/
def intensity (x : Spinor) : ℝ := (reQ x)^2 + (imQ x)^2

abbrev Pulse := ℝ × ℝ

/-- Apply a finite ordered list of the supplied real-parameter mixers. -/
def runWord : List Pulse → Spinor → Spinor
  | [], x => x
  | pulse :: rest, x => runWord rest (mix pulse.1 pulse.2 x)

/-- Record the intensity before the first pulse and after every pulse. -/
def intensityTrace : List Pulse → Spinor → List ℝ
  | [], x => [intensity x]
  | pulse :: rest, x =>
      intensity x :: intensityTrace rest (mix pulse.1 pulse.2 x)

theorem reQ_exchange (x : Spinor) : reQ (exchange x) = reQ x := by
  rcases x with ⟨br, bi, dr, di⟩
  dsimp [exchange, reQ]
  ring

theorem imQ_exchange (x : Spinor) : imQ (exchange x) = -imQ x := by
  rcases x with ⟨br, bi, dr, di⟩
  dsimp [exchange, imQ]
  ring

/-- Exchanging B and D sends Q to its complex conjugate. -/
theorem output_exchange (x : Spinor) :
    output (exchange x) = (reQ x, -imQ x) := by
  exact Prod.ext (reQ_exchange x) (imQ_exchange x)

theorem intensity_exchange (x : Spinor) :
    intensity (exchange x) = intensity x := by
  simp only [intensity, reQ_exchange, imQ_exchange]
  ring

/-- The exchange commutes with every real-parameter mixer; no norm condition is needed. -/
theorem exchange_mix (c s : ℝ) (x : Spinor) :
    exchange (mix c s x) = mix c s (exchange x) := by
  rcases x with ⟨br, bi, dr, di⟩
  rfl

/-- Exchange commutes with any finite word of mixers. -/
theorem exchange_runWord (word : List Pulse) (x : Spinor) :
    exchange (runWord word x) = runWord word (exchange x) := by
  induction word generalizing x with
  | nil => rfl
  | cons pulse rest ih =>
      change exchange (runWord rest (mix pulse.1 pulse.2 x)) =
        runWord rest (mix pulse.1 pulse.2 (exchange x))
      calc
        exchange (runWord rest (mix pulse.1 pulse.2 x))
            = runWord rest (exchange (mix pulse.1 pulse.2 x)) := ih _
        _ = runWord rest (mix pulse.1 pulse.2 (exchange x)) := by
          rw [exchange_mix]

/-- Every finite intensity observation trace agrees for an exchanged pair. -/
theorem intensityTrace_exchange (word : List Pulse) (x : Spinor) :
    intensityTrace word (exchange x) = intensityTrace word x := by
  induction word generalizing x with
  | nil =>
      simp [intensityTrace, intensity_exchange]
  | cons pulse rest ih =>
      change intensity (exchange x) ::
          intensityTrace rest (mix pulse.1 pulse.2 (exchange x)) =
        intensity x :: intensityTrace rest (mix pulse.1 pulse.2 x)
      rw [intensity_exchange]
      have htail :
          intensityTrace rest (mix pulse.1 pulse.2 (exchange x)) =
            intensityTrace rest (mix pulse.1 pulse.2 x) := by
        calc
          intensityTrace rest (mix pulse.1 pulse.2 (exchange x))
              = intensityTrace rest (exchange (mix pulse.1 pulse.2 x)) := by
                  rw [exchange_mix]
          _ = intensityTrace rest (mix pulse.1 pulse.2 x) := ih _
      rw [htail]

/-- The terminal intensity after any finite mixer word is also identical. -/
theorem terminal_intensity_exchange (word : List Pulse) (x : Spinor) :
    intensity (runWord word (exchange x)) = intensity (runWord word x) := by
  calc
    intensity (runWord word (exchange x))
        = intensity (exchange (runWord word x)) := by
            rw [← exchange_runWord word x]
    _ = intensity (runWord word x) := intensity_exchange _

/-- B = 1 and D = i, represented with rational real coordinates. -/
def unitPhaseWitness : Spinor := ⟨1, 0, 0, 1⟩

/-- Q is -i for the witness and +i after exchanging B and D. -/
theorem unitPhase_complex_readouts :
    output unitPhaseWitness = (0, -1) ∧
      output (exchange unitPhaseWitness) = (0, 1) := by
  norm_num [output, reQ, imQ, exchange, unitPhaseWitness]

theorem unitPhase_complex_separates :
    output unitPhaseWitness ≠ output (exchange unitPhaseWitness) := by
  intro h
  have hi := congrArg Prod.snd h
  norm_num [output, reQ, imQ, exchange, unitPhaseWitness] at hi

/-- Both swapped states have the same |Q|² = 1. -/
theorem unitPhase_intensity_collision :
    intensity unitPhaseWitness = 1 ∧
      intensity (exchange unitPhaseWitness) = 1 := by
  norm_num [intensity, reQ, imQ, exchange, unitPhaseWitness]

/-- The added signed imaginary quadrature changes sign under exchange. -/
theorem signed_quadrature_breaks_exchange (x : Spinor) :
    imQ (exchange x) = -imQ x := imQ_exchange x

theorem unitPhase_signed_quadrature_separates :
    imQ unitPhaseWitness = -1 ∧
      imQ (exchange unitPhaseWitness) = 1 := by
  norm_num [imQ, exchange, unitPhaseWitness]

end DarkBrightIntensity
