/-!
# Observation kernels, four-phase coordinates, and recovery counterexamples

The four-phase model below is the coordinate normal form (x,-u,-x,u)
identified by PR #19's `LinearInputWFSMobiusFourier.trace4_values`.
This module does not import that branch or assert an equivalence of dynamics.
The statements concern only observations, their kernels, and exact inverses.

Scalar pencils are one-dimensional linear matrix pencils. They isolate the
necessity of the hypotheses used in the general reconstruction theorem.
-/

noncomputable section

namespace LinearInputComplementaryObservationExamples

/-- A one-dimensional real pencil observed at the two opposite parameters. -/
def scalarPair (b c x : ℝ) : ℝ × ℝ :=
  ((b + c) * x, (b - c) * x)

/-- The scalar instance of the explicit inverse/mean decoder. -/
def scalarDecode (b : ℝ) (y : ℝ × ℝ) : ℝ :=
  b⁻¹ * ((y.1 + y.2) / 2)

/-- A singular center can lead to complete information loss. -/
theorem zero_pencil_collision :
    (0 : ℝ) ≠ 1 ∧ scalarPair 0 0 0 = scalarPair 0 0 1 := by
  norm_num [scalarPair]

/-- Conversely, invertibility of the center is not necessary for joint
injectivity: the difference probe can retain the entire state. -/
theorem singular_center_can_be_injective :
    ¬ IsUnit (0 : ℝ) ∧ Function.Injective (scalarPair 0 1) := by
  constructor
  · simp [isUnit_iff_ne_zero]
  · intro x y h
    have hp := congrArg Prod.fst h
    simpa [scalarPair] using hp

theorem singular_center_alternative_decoder (x : ℝ) :
    (scalarPair 0 1 x).1 = x := by
  simp [scalarPair]

/-- Nonzero repeated observations can also share a nonzero kernel.
Here B(x,u)=(x,0) and C=0. -/
def sharedProjection (z : ℝ × ℝ) : ℝ × ℝ := (z.1, 0)

theorem repeated_projection_collision :
    ((0 : ℝ), 0) ≠ (0, 1) ∧
    (sharedProjection (0, 0), sharedProjection (0, 0)) =
      (sharedProjection (0, 1), sharedProjection (0, 1)) := by
  norm_num [sharedProjection]

/-- With B=1 and C=0, only equal observation pairs are realizable. -/
theorem inconsistent_pair_not_realizable :
    ¬ ∃ x : ℝ, scalarPair 1 0 x = (1, 0) := by
  rintro ⟨x, h⟩
  have hp := congrArg Prod.fst h
  have hm := congrArg Prod.snd h
  norm_num [scalarPair] at hp hm
  linarith

/-- Decoding arbitrary data does not make it realizable: a right inverse
is asserted only on the image of the observation map. -/
theorem inconsistent_pair_not_reconstructed :
    scalarPair 1 0 (scalarDecode 1 (1, 0)) ≠ (1, 0) := by
  norm_num [scalarPair, scalarDecode]

/-- Over characteristic two, B=C=1 gives two identical zero probes. -/
def binaryPair (x : ZMod 2) : ZMod 2 × ZMod 2 :=
  (((1 : ZMod 2) + 1) * x, ((1 : ZMod 2) - 1) * x)

theorem binary_pair_zero (x : ZMod 2) : binaryPair x = (0, 0) := by
  simp [binaryPair, show (1 : ZMod 2) + 1 = 0 by decide]

/-- Invertibility of B alone is insufficient in characteristic two. -/
theorem characteristic_two_collision :
    IsUnit (1 : ZMod 2) ∧ (0 : ZMod 2) ≠ 1 ∧ binaryPair 0 = binaryPair 1 := by
  refine ⟨isUnit_one, ?_, ?_⟩
  · decide
  · rw [binary_pair_zero, binary_pair_zero]

/-- The even observations in the coordinate form proved in PR #19. -/
def evenObserve (z : ℝ × ℝ) : ℝ × ℝ := (z.1, -z.1)

/-- The odd observations in that same coordinate form. -/
def oddObserve (z : ℝ × ℝ) : ℝ × ℝ := (-z.2, z.2)

theorem even_observe_eq_iff (z w : ℝ × ℝ) :
    evenObserve z = evenObserve w ↔ z.1 = w.1 := by
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    simp [evenObserve, h]

theorem odd_observe_eq_iff (z w : ℝ × ℝ) :
    oddObserve z = oddObserve w ↔ z.2 = w.2 := by
  constructor
  · intro h
    exact congrArg Prod.snd h
  · intro h
    simp [oddObserve, h]

/-- The even kernel is the u axis. -/
theorem even_observation_kernel (z : ℝ × ℝ) :
    evenObserve z = (0, 0) ↔ z.1 = 0 := by
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    simp [evenObserve, h]

/-- The odd kernel is the x axis. -/
theorem odd_observation_kernel (z : ℝ × ℝ) :
    oddObserve z = (0, 0) ↔ z.2 = 0 := by
  constructor
  · intro h
    exact congrArg Prod.snd h
  · intro h
    simp [oddObserve, h]

theorem complementary_phase_kernels (z : ℝ × ℝ) :
    evenObserve z = (0, 0) ∧ oddObserve z = (0, 0) ↔ z = (0, 0) := by
  rw [even_observation_kernel, odd_observation_kernel]
  constructor
  · rintro ⟨hx, hu⟩
    exact Prod.ext hx hu
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- The raw even/odd pair has a direct coordinate decoder. -/
def phasePairDecode (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ := (p.1.1, p.2.2)

theorem phase_pair_decode (z : ℝ × ℝ) :
    phasePairDecode (evenObserve z, oddObserve z) = z := by
  rcases z with ⟨x, u⟩
  rfl

/-- Averaging the raw even and odd readouts is a different operation from
decoding their pair. Its center is singular despite joint injectivity. -/
def phaseAverage (z : ℝ × ℝ) : ℝ × ℝ :=
  (((evenObserve z).1 + (oddObserve z).1) / 2,
   ((evenObserve z).2 + (oddObserve z).2) / 2)

theorem phase_average_collision :
    ((0 : ℝ), 0) ≠ (1, 1) ∧ phaseAverage (0, 0) = phaseAverage (1, 1) := by
  norm_num [phaseAverage, evenObserve, oddObserve]

/-- Coordinates only: four samples in their original phase order. -/
def phaseTrace (z : ℝ × ℝ) (j : Fin 4) : ℝ :=
  if j = 0 then z.1 else if j = 1 then -z.2 else if j = 2 then -z.1 else z.2

theorem phase_trace_values (z : ℝ × ℝ) :
    phaseTrace z 0 = z.1 ∧ phaseTrace z 1 = -z.2 ∧
    phaseTrace z 2 = -z.1 ∧ phaseTrace z 3 = z.2 := by
  simp [phaseTrace]

/-- One even and one odd phase recover the two real coordinates. -/
def phaseDecode (q : Fin 4 → ℝ) : ℝ × ℝ := (q 0, -q 1)

theorem phase_decode_trace (z : ℝ × ℝ) : phaseDecode (phaseTrace z) = z := by
  rcases z with ⟨x, u⟩
  simp [phaseDecode, phaseTrace]

theorem phase_trace_injective : Function.Injective phaseTrace := by
  intro z w h
  have hd := congrArg phaseDecode h
  simpa only [phase_decode_trace] using hd

/-- Four real data values are realizable exactly when the two redundant
opposite-phase identities hold. -/
def PhaseCompatible (q : Fin 4 → ℝ) : Prop := q 2 = -q 0 ∧ q 3 = -q 1

theorem phase_trace_decode_of_compatible (q : Fin 4 → ℝ)
    (hq : PhaseCompatible q) : phaseTrace (phaseDecode q) = q := by
  rcases hq with ⟨h2, h3⟩
  funext j
  fin_cases j <;> simp [phaseTrace, phaseDecode, h2, h3]

theorem phase_compatible_iff_realizable (q : Fin 4 → ℝ) :
    PhaseCompatible q ↔ ∃ z : ℝ × ℝ, phaseTrace z = q := by
  constructor
  · intro hq
    exact ⟨phaseDecode q, phase_trace_decode_of_compatible q hq⟩
  · rintro ⟨z, rfl⟩
    simp [PhaseCompatible, phaseTrace]

end LinearInputComplementaryObservationExamples
