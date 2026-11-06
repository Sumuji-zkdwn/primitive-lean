import FluidPrismPhaseMemory

/-!
# Two wavelength intensity observations of the existing fluid height model

The reference phase and first output are reused without modifying PR #92.
The second wavelength is 2/3 of the first only in the ideal specialization.
With dispersion the effective phase ratio is (deltaN2/deltaN1)*(lambda1/lambda2).
These are ideal cosine intensities, not measurements of the full complex phase.
The five-height alphabet below is a sensor test alphabet, not five proved
stable states of the quartic memory potential.
-/

noncomputable section
namespace TwoWavelengthPhase

open FluidPrismPhaseMemory

def wavelengthOne (wavelength : ℝ) : ℝ := wavelength
def wavelengthTwo (wavelength : ℝ) : ℝ := (2/3) * wavelength
def firstPort (h : ℝ) : ℝ := port h
def ratioPhase (r h : ℝ) : ℝ := r * phase h
def ratioPort (r h : ℝ) : ℝ := (1 + Real.cos (ratioPhase r h)) / 2
def observation (r h : ℝ) : ℝ × ℝ := (firstPort h, ratioPort r h)
def secondPort (h : ℝ) : ℝ := ratioPort (3/2) h
def idealObservation (h : ℝ) : ℝ × ℝ := observation (3/2) h

/-- The phase multiplier includes the ratio of index *contrasts*, not indices. -/
def effectiveRatio (deltaN1 deltaN2 lambda1 lambda2 : ℝ) : ℝ :=
  (deltaN2 / deltaN1) * (lambda1 / lambda2)

theorem wavelengths_positive (wavelength : ℝ) (hw : 0 < wavelength) :
    0 < wavelengthOne wavelength ∧ 0 < wavelengthTwo wavelength := by
  dsimp [wavelengthOne, wavelengthTwo]
  constructor
  · exact hw
  · positivity

theorem second_wavelength_ne_zero (wavelength : ℝ) (hw : wavelength ≠ 0) :
    wavelengthTwo wavelength ≠ 0 := by
  dsimp [wavelengthTwo]
  exact mul_ne_zero (by norm_num) hw

/-- Both channels use the same path and a reference half-wave calibration.
    The contrasts may differ; no actual material dispersion law is asserted. -/
theorem dispersive_calibrated_phase
    (deltaN1 deltaN2 a lambda1 lambda2 h : ℝ)
    (hd : deltaN1 ≠ 0) (hw1 : lambda1 ≠ 0) (hw2 : lambda2 ≠ 0)
    (hcal : 4 * deltaN1 * a = lambda1) :
    opticalPhase deltaN2 (a*(h+1)) lambda2 =
      ratioPhase (effectiveRatio deltaN1 deltaN2 lambda1 lambda2) h := by
  have href := calibrated_phase deltaN1 a lambda1 h hw1 hcal
  rw [ratioPhase, ← href]
  unfold opticalPhase effectiveRatio
  field_simp
  <;> ring

theorem nondispersive_ratio (deltaN wavelength : ℝ)
    (hd : deltaN ≠ 0) (hw : wavelength ≠ 0) :
    effectiveRatio deltaN deltaN (wavelengthOne wavelength)
      (wavelengthTwo wavelength) = 3/2 := by
  unfold effectiveRatio wavelengthOne wavelengthTwo
  field_simp
  <;> ring

theorem ideal_second_calibrated_phase (deltaN a wavelength h : ℝ)
    (hw : wavelength ≠ 0) (hcal : 4 * deltaN * a = wavelength) :
    opticalPhase deltaN (a*(h+1)) (wavelengthTwo wavelength) =
      ratioPhase (3/2) h := by
  have hd : deltaN ≠ 0 := by
    intro hz
    rw [hz] at hcal
    simp only [mul_zero, zero_mul] at hcal
    exact hw hcal.symm
  have hc := dispersive_calibrated_phase deltaN deltaN a wavelength
    (wavelengthTwo wavelength) h hd hw (second_wavelength_ne_zero wavelength hw) hcal
  simpa only [nondispersive_ratio deltaN wavelength hd hw, wavelengthOne] using hc

theorem first_channel_unchanged (h : ℝ) :
    (idealObservation h).1 = port h := rfl

theorem observation_refines_first (r x y : ℝ)
    (he : observation r x = observation r y) : firstPort x = firstPort y :=
  congrArg Prod.fst he

theorem first_left : firstPort (-1) = 1 := port_false
theorem first_right : firstPort 1 = 0 := port_true

theorem first_zero : firstPort 0 = 1/2 := by
  norm_num [firstPort, port, phase, Real.cos_pi_div_two]

theorem first_two : firstPort 2 = 1/2 := by
  have hp : phase 2 = Real.pi / 2 + Real.pi := by dsimp [phase]; ring
  simp [firstPort, port, hp, Real.cos_add, Real.cos_pi_div_two]

theorem first_three : firstPort 3 = 1 := by
  have hp : phase 3 = Real.pi + Real.pi := by dsimp [phase]; ring
  simp [firstPort, port, hp, Real.cos_add]

theorem second_left : secondPort (-1) = 1 := by
  norm_num [secondPort, ratioPort, ratioPhase, phase]

theorem second_zero : secondPort 0 = (2 - Real.sqrt 2) / 4 := by
  have hp : ratioPhase (3/2) 0 = Real.pi - Real.pi / 4 := by
    dsimp [ratioPhase, phase]; ring
  simp only [secondPort, ratioPort, hp, Real.cos_sub, Real.cos_pi,
    Real.sin_pi, Real.cos_pi_div_four]
  ring

theorem second_one : secondPort 1 = 1/2 := by
  have hp : ratioPhase (3/2) 1 = Real.pi / 2 + Real.pi := by
    dsimp [ratioPhase, phase]; ring
  simp [secondPort, ratioPort, hp, Real.cos_add, Real.cos_pi_div_two]

theorem second_two : secondPort 2 = (2 + Real.sqrt 2) / 4 := by
  have hp : ratioPhase (3/2) 2 = Real.pi / 4 + (Real.pi + Real.pi) := by
    dsimp [ratioPhase, phase]; ring
  simp only [secondPort, ratioPort, hp, Real.cos_add, Real.sin_add,
    Real.cos_pi, Real.sin_pi, Real.cos_pi_div_four]
  ring

theorem second_three : secondPort 3 = 0 := by
  have hp : ratioPhase (3/2) 3 = Real.pi + (Real.pi + Real.pi) := by
    dsimp [ratioPhase, phase]; ring
  simp [secondPort, ratioPort, hp, Real.cos_add, Real.sin_add]

theorem proposed_single_collision : firstPort (-1) = firstPort 3 := by
  rw [first_left, first_three]

theorem proposed_pair_values :
    idealObservation (-1) = (1,1) ∧ idealObservation 3 = (1,0) := by
  change (firstPort (-1), secondPort (-1)) = (1,1) ∧
    (firstPort 3, secondPort 3) = (1,0)
  rw [first_left, second_left, first_three, second_three]
  exact ⟨rfl, rfl⟩

theorem proposed_pair_separated : idealObservation (-1) ≠ idealObservation 3 := by
  rw [proposed_pair_values.1, proposed_pair_values.2]
  norm_num

theorem first_period_four (h : ℝ) : firstPort (h+4) = firstPort h :=
  port_period_four h

theorem second_period_eight (h : ℝ) : secondPort (h+8) = secondPort h := by
  have hp : ratioPhase (3/2) (h+8) =
      ratioPhase (3/2) h + ((2*Real.pi + 2*Real.pi) + 2*Real.pi) := by
    dsimp [ratioPhase, phase]; ring
  simp [secondPort, ratioPort, hp, Real.cos_add, Real.sin_add]

theorem ideal_period_eight (h : ℝ) :
    idealObservation (h+8) = idealObservation h := by
  apply Prod.ext
  · change firstPort (h+8) = firstPort h
    calc
      firstPort (h+8) = firstPort ((h+4)+4) := by congr 1 <;> ring
      _ = firstPort (h+4) := first_period_four (h+4)
      _ = firstPort h := first_period_four h
  · exact second_period_eight h

/-- The common reflection ambiguity survives for EVERY real phase ratio. -/
theorem observation_reflection (r h : ℝ) :
    observation r (-2-h) = observation r h := by
  have hp : phase (-2-h) = -phase h := by dsimp [phase]; ring
  apply Prod.ext
  · simp [observation, firstPort, port, hp]
  · simp [observation, ratioPort, ratioPhase, hp]

theorem no_ratio_globally_injective (r : ℝ) :
    ¬ Function.Injective (observation r) := by
  intro hi
  have he := hi (observation_reflection r 0)
  norm_num at he

theorem periodic_counterexample :
    (-1 : ℝ) ≠ 7 ∧ idealObservation (-1) = idealObservation 7 := by
  constructor
  · norm_num
  · have hp := ideal_period_eight (-1)
    norm_num at hp
    exact hp.symm

/-- A collision strictly inside the interval containing the five integer
    representatives. Mixed signs of the two cosine phases cause this. -/
theorem mixed_counterexample :
    (-1/3 : ℝ) ≠ 7/3 ∧ idealObservation (-1/3) = idealObservation (7/3) := by
  constructor
  · norm_num
  · apply Prod.ext
    · change firstPort (-1/3) = firstPort (7/3)
      have hp : phase (7/3) = 2*Real.pi - phase (-1/3) := by
        dsimp [phase]; ring
      simp [firstPort, port, hp, Real.cos_sub]
    · change secondPort (-1/3) = secondPort (7/3)
      have hp : ratioPhase (3/2) (7/3) =
          ratioPhase (3/2) (-1/3) + 2*Real.pi := by
        dsimp [ratioPhase, phase]; ring
      simp [secondPort, ratioPort, hp, Real.cos_add]

/-- A finite sensor alphabet; no new equilibrium or write dynamics are assumed. -/
def fiveHeight (i : Fin 5) : ℝ := (i.val : ℝ) - 1

theorem five_height_readout (i : Fin 5) :
    idealObservation (fiveHeight i) =
      ![(1,1), (1/2,(2-Real.sqrt 2)/4), (0,1/2),
        (1/2,(2+Real.sqrt 2)/4), (1,0)] i := by
  fin_cases i <;>
    norm_num [fiveHeight, idealObservation, observation, ← secondPort,
      first_left, first_zero, first_right, first_two, first_three,
      second_left, second_zero, second_one, second_two, second_three]

theorem five_height_readout_injective :
    Function.Injective (fun i : Fin 5 => idealObservation (fiveHeight i)) := by
  intro i j hij
  rw [five_height_readout, five_height_readout] at hij
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  fin_cases i <;> fin_cases j <;> norm_num at hij ⊢ <;> nlinarith

/-- This same finite alphabet is not identified by the first wavelength. -/
theorem five_height_first_not_injective :
    ¬ Function.Injective (fun i : Fin 5 => firstPort (fiveHeight i)) := by
  intro hi
  have hh : firstPort (fiveHeight (0 : Fin 5)) =
      firstPort (fiveHeight (4 : Fin 5)) := by
    norm_num [fiveHeight, first_left, first_three]
  have he := hi hh
  norm_num at he

/-- Sensor injectivity transfers to any set contained in the certified alphabet. -/
theorem injective_on_five_height_range :
    Set.InjOn idealObservation (Set.range fiveHeight) := by
  intro x hx y hy hxy
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨j, rfl⟩
  exact congrArg fiveHeight (five_height_readout_injective hxy)

end TwoWavelengthPhase
