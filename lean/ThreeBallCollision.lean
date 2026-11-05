import Mathlib

/-!
# Exact contact-order dependence for three elastic balls

A line of balls with masses (1, 2, 1) and initial velocities (1, 0, -1).
`collideLM` and `collideMR` are the standard one-dimensional, perfectly
elastic *binary* collision maps. Their rational coefficients are fixed by the
given masses. The proof uses exact rational arithmetic, not floating point.

A positive arrival-time offset is defined to mean "left contacts first".
Only nonzero offsets are assigned a binary-collision schedule. The value at
exact simultaneity is intentionally left unspecified: binary collision rules
alone do not prescribe an impact law for three simultaneous contacts.

This module models impact velocities and their contact order, not continuous
ball positions, contact deformation or compliant three-body mechanics.
-/

namespace ThreeBallCollision

/-- Velocities of the left (mass 1), middle (mass 2), right (mass 1) balls. -/
structure Velocity where
  left : ℚ
  middle : ℚ
  right : ℚ
  deriving Repr, DecidableEq

/-- Left-middle binary elastic impact, with masses 1 and 2. -/
def collideLM (v : Velocity) : Velocity :=
  ⟨(-v.left + 4 * v.middle) / 3,
   (2 * v.left + v.middle) / 3,
   v.right⟩

/-- Middle-right binary elastic impact, with masses 2 and 1. -/
def collideMR (v : Velocity) : Velocity :=
  ⟨v.left,
   (v.middle + 2 * v.right) / 3,
   (4 * v.middle - v.right) / 3⟩

/-- Total momentum for masses (1, 2, 1). -/
def momentum (v : Velocity) : ℚ :=
  v.left + 2 * v.middle + v.right

/-- Twice the kinetic energy; the common factor 1/2 is omitted. -/
def twiceEnergy (v : Velocity) : ℚ :=
  v.left ^ 2 + 2 * v.middle ^ 2 + v.right ^ 2

theorem lm_reverses_relative_speed (v : Velocity) :
    (collideLM v).left - (collideLM v).middle =
      -(v.left - v.middle) := by
  dsimp [collideLM]
  ring

theorem mr_reverses_relative_speed (v : Velocity) :
    (collideMR v).middle - (collideMR v).right =
      -(v.middle - v.right) := by
  dsimp [collideMR]
  ring

theorem lm_preserves_momentum (v : Velocity) :
    momentum (collideLM v) = momentum v := by
  dsimp [momentum, collideLM]
  ring

theorem mr_preserves_momentum (v : Velocity) :
    momentum (collideMR v) = momentum v := by
  dsimp [momentum, collideMR]
  ring

theorem lm_preserves_energy (v : Velocity) :
    twiceEnergy (collideLM v) = twiceEnergy v := by
  dsimp [twiceEnergy, collideLM]
  ring

theorem mr_preserves_energy (v : Velocity) :
    twiceEnergy (collideMR v) = twiceEnergy v := by
  dsimp [twiceEnergy, collideMR]
  ring

/-- Both outer balls approach the stationary middle ball at unit speed. -/
def initial : Velocity := ⟨1, 0, -1⟩

/-- Positive time offset: LM, then MR, then LM again. -/
def leftFirst : Velocity := collideLM (collideMR (collideLM initial))

/-- Negative time offset: MR, then LM, then MR again. -/
def rightFirst : Velocity := collideMR (collideLM (collideMR initial))

theorem left_first_stage_one :
    (collideLM initial).left = (-1 / 3 : ℚ) ∧
    (collideLM initial).middle = (2 / 3 : ℚ) ∧
    (collideLM initial).right = (-1 : ℚ) := by
  norm_num [initial, collideLM]

theorem left_first_stage_two :
    (collideMR (collideLM initial)).left = (-1 / 3 : ℚ) ∧
    (collideMR (collideLM initial)).middle = (-4 / 9 : ℚ) ∧
    (collideMR (collideLM initial)).right = (11 / 9 : ℚ) := by
  norm_num [initial, collideLM, collideMR]

theorem left_first_exact :
    leftFirst.left = (-13 / 27 : ℚ) ∧
    leftFirst.middle = (-10 / 27 : ℚ) ∧
    leftFirst.right = (11 / 9 : ℚ) := by
  norm_num [leftFirst, initial, collideLM, collideMR]

theorem right_first_exact :
    rightFirst.left = (-11 / 9 : ℚ) ∧
    rightFirst.middle = (10 / 27 : ℚ) ∧
    rightFirst.right = (13 / 27 : ℚ) := by
  norm_num [rightFirst, initial, collideLM, collideMR]

theorem left_first_preserves_momentum :
    momentum leftFirst = momentum initial := by
  simp [leftFirst, lm_preserves_momentum, mr_preserves_momentum]

theorem right_first_preserves_momentum :
    momentum rightFirst = momentum initial := by
  simp [rightFirst, lm_preserves_momentum, mr_preserves_momentum]

theorem left_first_preserves_energy :
    twiceEnergy leftFirst = twiceEnergy initial := by
  simp [leftFirst, lm_preserves_energy, mr_preserves_energy]

theorem right_first_preserves_energy :
    twiceEnergy rightFirst = twiceEnergy initial := by
  simp [rightFirst, lm_preserves_energy, mr_preserves_energy]

/-- Both schedules have the same momentum and energy observations. -/
theorem same_conserved_observations :
    momentum leftFirst = momentum rightFirst ∧
    twiceEnergy leftFirst = twiceEnergy rightFirst := by
  constructor
  · exact left_first_preserves_momentum.trans right_first_preserves_momentum.symm
  · exact left_first_preserves_energy.trans right_first_preserves_energy.symm

/-- Two impacts fail to commute even before the final (third) impact. -/
theorem impacts_do_not_commute :
    collideLM (collideMR initial) ≠
      collideMR (collideLM initial) := by
  intro h
  have hm := congrArg Velocity.middle h
  norm_num [initial, collideLM, collideMR] at hm

/-- Middle-ball velocity differs by exactly 20/27. -/
theorem middle_velocity_jump :
    rightFirst.middle - leftFirst.middle = (20 / 27 : ℚ) := by
  norm_num [rightFirst, leftFirst, initial, collideLM, collideMR]

theorem different_final_states : leftFirst ≠ rightFirst := by
  intro h
  have hm := congrArg Velocity.middle h
  rw [left_first_exact.2.1, right_first_exact.2.1] at hm
  norm_num at hm

/-- A binary contact is admissible when the left object's speed is greater. -/
def leftApproaches (v : Velocity) : Prop := v.left > v.middle

/-- A binary contact is admissible when middle approaches right. -/
def rightApproaches (v : Velocity) : Prop := v.middle > v.right

theorem left_first_contact_speeds :
    leftApproaches initial ∧
    rightApproaches (collideLM initial) ∧
    leftApproaches (collideMR (collideLM initial)) := by
  norm_num [leftApproaches, rightApproaches, initial, collideLM, collideMR]

theorem right_first_contact_speeds :
    rightApproaches initial ∧
    leftApproaches (collideMR initial) ∧
    rightApproaches (collideLM (collideMR initial)) := by
  norm_num [leftApproaches, rightApproaches, initial, collideLM, collideMR]

theorem final_velocities_separate :
    (leftFirst.left < leftFirst.middle ∧ leftFirst.middle < leftFirst.right) ∧
    (rightFirst.left < rightFirst.middle ∧ rightFirst.middle < rightFirst.right) := by
  norm_num [leftFirst, rightFirst, initial, collideLM, collideMR]

/-- "First contact" is deliberately retained as history information. -/
inductive FirstContact
  | left
  | right
  deriving DecidableEq, Repr

def outcome : FirstContact → Velocity
  | .left => leftFirst
  | .right => rightFirst

/--
Once first-contact history is forgotten, the same initial velocity vector
cannot predict both center velocities by a single deterministic function.
-/
theorem no_history_free_middle_predictor :
    ¬ ∃ prediction : Velocity → ℚ,
        ∀ first : FirstContact,
          prediction initial = (outcome first).middle := by
  rintro ⟨prediction, hp⟩
  have hl := hp FirstContact.left
  have hr := hp FirstContact.right
  change prediction initial = leftFirst.middle at hl
  change prediction initial = rightFirst.middle at hr
  have heq : leftFirst.middle = rightFirst.middle := hl.symm.trans hr
  rw [left_first_exact.2.1, right_first_exact.2.1] at heq
  norm_num at heq

/-- Only nonzero time offsets select a binary collision history. -/
def middleByOffset (offset : ℚ) : Option ℚ :=
  if 0 < offset then some leftFirst.middle
  else if offset < 0 then some rightFirst.middle
  else none

theorem positive_offset (offset : ℚ) (h : 0 < offset) :
    middleByOffset offset = some (-10 / 27 : ℚ) := by
  simp [middleByOffset, h, left_first_exact.2.1]

theorem negative_offset (offset : ℚ) (h : offset < 0) :
    middleByOffset offset = some (10 / 27 : ℚ) := by
  have hn : ¬ (0 : ℚ) < offset := not_lt.mpr (le_of_lt h)
  simp [middleByOffset, hn, h, right_first_exact.2.1]

/-- No simultaneous three-body impact rule is postulated here. -/
theorem simultaneous_unassigned : middleByOffset 0 = none := by
  norm_num [middleByOffset]

/--
For every positive rational tolerance δ, the offsets ±ε can be made closer
to zero than δ, while the two final center speeds stay at ±10/27.
-/
theorem jump_persists_arbitrarily_close (δ : ℚ) (hδ : 0 < δ) :
    ∃ ε : ℚ, 0 < ε ∧ ε < δ ∧
      middleByOffset ε = some (-10 / 27 : ℚ) ∧
      middleByOffset (-ε) = some (10 / 27 : ℚ) := by
  have hpos : 0 < δ / 2 := by linarith
  have hsmall : δ / 2 < δ := by linarith
  have hneg : -(δ / 2) < (0 : ℚ) := by linarith
  exact ⟨δ / 2, hpos, hsmall,
    positive_offset _ hpos, negative_offset _ hneg⟩

#print axioms ThreeBallCollision.lm_preserves_momentum
#print axioms ThreeBallCollision.lm_preserves_energy
#print axioms ThreeBallCollision.mr_preserves_momentum
#print axioms ThreeBallCollision.mr_preserves_energy
#print axioms ThreeBallCollision.same_conserved_observations
#print axioms ThreeBallCollision.impacts_do_not_commute
#print axioms ThreeBallCollision.middle_velocity_jump
#print axioms ThreeBallCollision.no_history_free_middle_predictor
#print axioms ThreeBallCollision.jump_persists_arbitrarily_close

end ThreeBallCollision
