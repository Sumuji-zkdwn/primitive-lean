import TwoWavelengthPhase

/-!
# Recovering a height carrier from two ideal cosine intensities

The double- and triple-angle identities recover `cos (phase h / 2)` from
the two intensities whenever the first intensity is not `3/4`.  On the
height interval `[-1,3]` this carrier is injective.  This gives an explicit,
non-tautological sufficient condition for any finite alphabet in that interval.

The exceptional value is essential: the previously proved heights `-1/3`
and `7/3` both have first intensity `3/4` and second intensity `1/2`.
These are mathematical statements about the ideal, nondispersive ratio `3/2`;
they assert neither additional stable fluid states nor physical calibration.
-/

noncomputable section
namespace TwoWavelengthRecovery

open TwoWavelengthPhase FluidPrismPhaseMemory

def halfPhase (h : ℝ) : ℝ := phase h / 2
def carrier (h : ℝ) : ℝ := Real.cos (halfPhase h)

theorem phase_eq_two_half (h : ℝ) : phase h = 2 * halfPhase h := by
  dsimp [halfPhase]
  ring

theorem ratio_phase_eq_three_half (h : ℝ) :
    ratioPhase (3/2) h = 3 * halfPhase h := by
  dsimp [ratioPhase, halfPhase]
  ring

/-- The first intensity is the square of the half-phase cosine carrier. -/
theorem first_port_eq_carrier_sq (h : ℝ) : firstPort h = carrier h ^ 2 := by
  change (1 + Real.cos (phase h)) / 2 = Real.cos (halfPhase h) ^ 2
  rw [phase_eq_two_half, Real.cos_two_mul]
  ring

/-- The second intensity supplies the sign of the carrier, except at `T1=3/4`. -/
theorem second_port_chebyshev (h : ℝ) :
    2 * secondPort h - 1 = carrier h * (4 * firstPort h - 3) := by
  change 2 * ((1 + Real.cos (ratioPhase (3/2) h)) / 2) - 1 =
    carrier h * (4 * firstPort h - 3)
  rw [ratio_phase_eq_three_half, Real.cos_three_mul, first_port_eq_carrier_sq]
  dsimp [carrier]
  ring

/-- An exact recovery formula, conditional on a nonzero denominator. -/
theorem carrier_recovery (h : ℝ) (hex : firstPort h ≠ 3/4) :
    (2 * secondPort h - 1) / (4 * firstPort h - 3) = carrier h := by
  have hden : 4 * firstPort h - 3 ≠ 0 := by
    intro hz
    apply hex
    linarith
  apply (div_eq_iff hden).2
  exact second_port_chebyshev h

theorem carrier_eq_of_observation_eq (h k : ℝ)
    (hex : firstPort h ≠ 3/4)
    (he : idealObservation h = idealObservation k) : carrier h = carrier k := by
  have hfirst : firstPort h = firstPort k := congrArg Prod.fst he
  have hsecond : secondPort h = secondPort k := congrArg Prod.snd he
  have hek : firstPort k ≠ 3/4 := by
    intro hz
    exact hex (hfirst.trans hz)
  calc
    carrier h = (2 * secondPort h - 1) / (4 * firstPort h - 3) :=
      (carrier_recovery h hex).symm
    _ = (2 * secondPort k - 1) / (4 * firstPort k - 3) := by rw [hfirst, hsecond]
    _ = carrier k := carrier_recovery k hek

/-- Complete algebraic collision classification, valid for all real heights.
    At the exceptional first intensity the second intensity is always `1/2`. -/
theorem observation_eq_iff_carrier (h k : ℝ) :
    idealObservation h = idealObservation k ↔
      carrier h = carrier k ∨ (firstPort h = 3/4 ∧ firstPort k = 3/4) := by
  constructor
  · intro he
    by_cases hex : firstPort h = 3/4
    · right
      have hfirst : firstPort h = firstPort k := congrArg Prod.fst he
      exact ⟨hex, hfirst.symm.trans hex⟩
    · exact Or.inl (carrier_eq_of_observation_eq h k hex he)
  · rintro (hc | ⟨hh, hk⟩)
    · have hfirst : firstPort h = firstPort k := by
        rw [first_port_eq_carrier_sq, first_port_eq_carrier_sq, hc]
      apply Prod.ext
      · exact hfirst
      · change secondPort h = secondPort k
        have hi := second_port_chebyshev h
        have hj := second_port_chebyshev k
        rw [hc, hfirst] at hi
        linarith
    · apply Prod.ext
      · change firstPort h = firstPort k
        rw [hh, hk]
      · change secondPort h = secondPort k
        have hi := second_port_chebyshev h
        have hj := second_port_chebyshev k
        rw [hh] at hi
        rw [hk] at hj
        norm_num at hi hj
        linarith

theorem half_phase_mem_Icc (h : ℝ) (hh : h ∈ Set.Icc (-1) 3) :
    halfPhase h ∈ Set.Icc 0 Real.pi := by
  have hformula : halfPhase h = Real.pi * (h + 1) / 4 := by
    dsimp [halfPhase, phase]
    ring
  rw [hformula]
  constructor
  · exact div_nonneg (mul_nonneg Real.pi_nonneg (by linarith [hh.1])) (by norm_num)
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    nlinarith [mul_nonneg Real.pi_nonneg (show 0 ≤ 3 - h by linarith [hh.2])]

/-- Cosine is injective for the half phases corresponding to `[-1,3]`. -/
theorem carrier_injOn_interval : Set.InjOn carrier (Set.Icc (-1) 3) := by
  intro h hh k hk hc
  have hp : halfPhase h = halfPhase k :=
    Real.injOn_cos (half_phase_mem_Icc h hh) (half_phase_mem_Icc k hk) hc
  dsimp [halfPhase, phase] at hp
  have hz : Real.pi * (h - k) = 0 := by nlinarith [hp]
  have he : h - k = 0 := (mul_eq_zero.mp hz).resolve_left Real.pi_ne_zero
  linarith

/-- A concrete sufficient condition: remain within `[-1,3]` and exclude the
    exceptional first intensity `3/4`.  The state set need not be finite. -/
theorem ideal_injOn_of_interval_and_exclusion (S : Set ℝ)
    (hinterval : S ⊆ Set.Icc (-1) 3)
    (hex : ∀ h ∈ S, firstPort h ≠ 3/4) : Set.InjOn idealObservation S := by
  intro h hh k hk he
  exact carrier_injOn_interval (hinterval hh) (hinterval hk)
    (carrier_eq_of_observation_eq h k (hex h hh) he)

/-- Any finite alphabet satisfying the explicit interval and intensity
    conditions has an injective two-wavelength readout. -/
theorem finite_alphabet_injective_of_interval (S : Finset ℝ)
    (hinterval : ∀ h ∈ S, h ∈ Set.Icc (-1) 3)
    (hex : ∀ h ∈ S, firstPort h ≠ 3/4) :
    Function.Injective (fun h : {h : ℝ // h ∈ S} => idealObservation h.val) := by
  intro h k he
  apply Subtype.ext
  exact carrier_injOn_interval (hinterval h.val h.property) (hinterval k.val k.property)
    (carrier_eq_of_observation_eq h.val k.val (hex h.val h.property) he)

end TwoWavelengthRecovery
