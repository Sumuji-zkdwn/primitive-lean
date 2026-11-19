import ThreeBallCollision

/-!
# Free-flight realization of the three-ball contact orders

`docs/research/2026-11-14-three-ball-position-reentry.md` computed by hand, and
checked only with Python fractions, that hard balls with free gaps `a, b > 0`,
`a ≠ b`, and initial velocities `(1, 0, -1)` really perform the contact orders
LRL (`a < b`) or RLR (`b < a`) of `ThreeBallCollision.lean`, and listed the Lean
formalization of the free-gap model and its connection to the existing velocity
theorems as unproved. This file gives that formalization.

The state is the pair of free gaps `g_L = x_M - x_L - 2ρ`, `g_R = x_R - x_M - 2ρ`,
the velocities and the clock. Between impacts the gaps change at the rates
`v_M - v_L` and `v_R - v_M`. `outcome` decides the next event from the state:

* `separated`: no gap is closing, so no further contact ever happens
  (`separated_gaps_never_close`);
* `simultaneous`: both gaps close at the same instant, which binary impact
  laws leave unspecified;
* `contact side τ`: the gap on `side` closes first, after time `τ`.

`advance` flies freely for `τ` and applies the binary impact map of
`ThreeBallCollision.lean` on that side. During the flight both gaps stay
nonnegative (`flight_gaps_nonneg`).

Main results, for every rational `0 < a < b` (with `d = b - a`; positivity is the
physical requirement of nonnegative initial gaps, the event algebra only uses `a < b`):

* `left_first_schedule`: contacts L, R, L at times `a`, `a + 3d/5`, `a + 6d`, with
  the other gap `d`, `3d/5`, `9d` at those contacts, then `separated`;
* the final velocities are exactly `ThreeBallCollision.leftFirst`;

and symmetrically `right_first_schedule` for `0 < b < a` with `rightFirst`.
Hence the final middle velocity is `-10/27` for every `a < b` and `10/27` for
every `b < a` (`middle_velocity_jump`): it does not converge as `a - b → 0`.
Equal radii, free flight and instantaneous binary impacts are assumptions of
the model; simultaneous three-ball impact is not modelled.
-/

namespace ThreeBallFreeFlight

open ThreeBallCollision

/-- Free gaps, velocities and the clock. -/
structure State where
  gapL : ℚ
  gapR : ℚ
  vel : Velocity
  time : ℚ
  deriving DecidableEq

/-- Closing rate data: `ġ_L = v_M - v_L`, `ġ_R = v_R - v_M`. -/
def rateL (v : Velocity) : ℚ := v.middle - v.left

def rateR (v : Velocity) : ℚ := v.right - v.middle

inductive Side
  | L
  | R
  deriving DecidableEq

inductive Outcome
  | separated
  | simultaneous
  | contact (side : Side) (τ : ℚ)
  deriving DecidableEq

/-- Time for a gap `g` with rate `r` to close, if it is closing. -/
def hitTime (g r : ℚ) : Option ℚ := if r < 0 then some (g / -r) else none

/-- The next event of the free-flight model. -/
def outcome (s : State) : Outcome :=
  match hitTime s.gapL (rateL s.vel), hitTime s.gapR (rateR s.vel) with
  | none, none => .separated
  | some τ, none => .contact .L τ
  | none, some τ => .contact .R τ
  | some τ, some τ' =>
      if τ < τ' then .contact .L τ else if τ' < τ then .contact .R τ' else .simultaneous

/-- Free flight for time `τ`, then the binary impact on `side`. -/
def advance (s : State) (side : Side) (τ : ℚ) : State :=
  match side with
  | .L => ⟨0, s.gapR + τ * rateR s.vel, collideLM s.vel, s.time + τ⟩
  | .R => ⟨s.gapL + τ * rateL s.vel, 0, collideMR s.vel, s.time + τ⟩

/-- One event step; `none` when separated or at an unspecified simultaneous impact. -/
def step (s : State) : Option State :=
  match outcome s with
  | .contact side τ => some (advance s side τ)
  | _ => none

/-! ## General properties of the model -/

/-- If no gap is closing, the gaps never decrease again. -/
theorem separated_gaps_never_close (s : State) (hL : 0 ≤ rateL s.vel) (hR : 0 ≤ rateR s.vel)
    (t : ℚ) (ht : 0 ≤ t) :
    s.gapL ≤ s.gapL + t * rateL s.vel ∧ s.gapR ≤ s.gapR + t * rateR s.vel := by
  constructor <;> nlinarith

/-- The next contact time is no later than any closing time. -/
theorem contact_time_le {s : State} {side : Side} {τ : ℚ} (h : outcome s = .contact side τ) :
    (∀ τ', hitTime s.gapL (rateL s.vel) = some τ' → τ ≤ τ') ∧
      (∀ τ', hitTime s.gapR (rateR s.vel) = some τ' → τ ≤ τ') := by
  unfold outcome at h
  refine ⟨fun τ' h' => ?_, fun τ' h' => ?_⟩ <;>
  · cases hA : hitTime s.gapL (rateL s.vel) <;> cases hB : hitTime s.gapR (rateR s.vel) <;>
      simp only [hA, hB, Option.some.injEq, reduceCtorEq] at h h' <;>
      (try split_ifs at h) <;>
      simp only [Outcome.contact.injEq] at h <;>
      linarith

theorem outcome_separated_iff (s : State) :
    outcome s = .separated ↔ 0 ≤ rateL s.vel ∧ 0 ≤ rateR s.vel := by
  have hA : hitTime s.gapL (rateL s.vel) = none ↔ 0 ≤ rateL s.vel := by
    unfold hitTime
    split_ifs with h
    · simp [h]
    · simpa using not_lt.mp h
  have hB : hitTime s.gapR (rateR s.vel) = none ↔ 0 ≤ rateR s.vel := by
    unfold hitTime
    split_ifs with h
    · simp [h]
    · simpa using not_lt.mp h
  rw [← hA, ← hB]
  unfold outcome
  cases hitTime s.gapL (rateL s.vel) <;> cases hitTime s.gapR (rateR s.vel) <;>
    simp only [reduceCtorEq, and_self, and_false, false_and, iff_false]
  split_ifs <;> simp

/-- During a contact flight, both gaps stay nonnegative (they are affine in time). -/
theorem flight_gaps_nonneg (s : State) (hgL : 0 ≤ s.gapL) (hgR : 0 ≤ s.gapR)
    {side : Side} {τ : ℚ} (h : outcome s = .contact side τ) (t : ℚ) (ht0 : 0 ≤ t)
    (htτ : t ≤ τ) :
    0 ≤ s.gapL + t * rateL s.vel ∧ 0 ≤ s.gapR + t * rateR s.vel := by
  have key : ∀ g r : ℚ, 0 ≤ g → (∀ τ', hitTime g r = some τ' → t ≤ τ') → 0 ≤ g + t * r := by
    intro g r hg hlim
    by_cases hr : r < 0
    · have hτ' := hlim (g / -r) (by simp [hitTime, hr])
      have hpos : 0 < -r := by linarith
      have : t * (-r) ≤ g := by
        have := mul_le_mul_of_nonneg_right hτ' hpos.le
        rwa [div_mul_cancel₀ g hpos.ne'] at this
      nlinarith
    · nlinarith
  obtain ⟨h1, h2⟩ := contact_time_le h
  exact ⟨key _ _ hgL fun τ' h' => htτ.trans (h1 τ' h'), key _ _ hgR fun τ' h' => htτ.trans (h2 τ' h')⟩

/-! ## The left-first schedule for `0 < a < b` -/

/-- Initial state: gaps `a, b`, velocities `(1, 0, -1)`, clock `0`. -/
def start (a b : ℚ) : State := ⟨a, b, initial, 0⟩

theorem left_first_schedule (a b : ℚ) (_ha : 0 < a) (hab : a < b) :
    let d := b - a
    outcome (start a b) = .contact .L a ∧
    step (start a b) = some ⟨0, d, collideLM initial, a⟩ ∧
    outcome ⟨0, d, collideLM initial, a⟩ = .contact .R (3 * d / 5) ∧
    step ⟨0, d, collideLM initial, a⟩ =
      some ⟨3 * d / 5, 0, collideMR (collideLM initial), a + 3 * d / 5⟩ ∧
    outcome ⟨3 * d / 5, 0, collideMR (collideLM initial), a + 3 * d / 5⟩ = .contact .L (27 * d / 5) ∧
    step ⟨3 * d / 5, 0, collideMR (collideLM initial), a + 3 * d / 5⟩ =
      some ⟨0, 9 * d, leftFirst, a + 6 * d⟩ ∧
    outcome ⟨0, 9 * d, leftFirst, a + 6 * d⟩ = .separated := by
  intro d
  have hd : 0 < d := by simp only [d]; linarith
  have o1 : outcome (start a b) = .contact .L a := by
    simp [outcome, hitTime, start, rateL, rateR, initial, hab]
  have o2 : outcome ⟨0, d, collideLM initial, a⟩ = .contact .R (3 * d / 5) := by
    simp only [outcome, hitTime, rateL, rateR, initial, collideLM]
    norm_num
    ring_nf
  have o3 : outcome ⟨3 * d / 5, 0, collideMR (collideLM initial), a + 3 * d / 5⟩ =
      .contact .L (27 * d / 5) := by
    simp only [outcome, hitTime, rateL, rateR, initial, collideLM, collideMR]
    norm_num
    ring_nf
  have o4 : outcome ⟨0, 9 * d, leftFirst, a + 6 * d⟩ = .separated := by
    rw [outcome_separated_iff]
    simp only [rateL, rateR, leftFirst, initial, collideLM, collideMR]
    norm_num
  refine ⟨o1, ?_, o2, ?_, o3, ?_, o4⟩
  · unfold step; rw [o1]
    simp only [advance, start, rateR, initial, Option.some.injEq, State.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ring
  · unfold step; rw [o2]
    simp only [advance, rateL, initial, collideLM, Option.some.injEq, State.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ring
  · unfold step; rw [o3]
    simp only [advance, rateR, initial, collideLM, collideMR, leftFirst, Option.some.injEq,
      State.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ring

/-! ## The right-first schedule for `0 < b < a` -/

theorem right_first_schedule (a b : ℚ) (_hb : 0 < b) (hba : b < a) :
    let d := a - b
    outcome (start a b) = .contact .R b ∧
    step (start a b) = some ⟨d, 0, collideMR initial, b⟩ ∧
    outcome ⟨d, 0, collideMR initial, b⟩ = .contact .L (3 * d / 5) ∧
    step ⟨d, 0, collideMR initial, b⟩ =
      some ⟨0, 3 * d / 5, collideLM (collideMR initial), b + 3 * d / 5⟩ ∧
    outcome ⟨0, 3 * d / 5, collideLM (collideMR initial), b + 3 * d / 5⟩ = .contact .R (27 * d / 5) ∧
    step ⟨0, 3 * d / 5, collideLM (collideMR initial), b + 3 * d / 5⟩ =
      some ⟨9 * d, 0, rightFirst, b + 6 * d⟩ ∧
    outcome ⟨9 * d, 0, rightFirst, b + 6 * d⟩ = .separated := by
  intro d
  have hd : 0 < d := by simp only [d]; linarith
  have o1 : outcome (start a b) = .contact .R b := by
    simp [outcome, hitTime, start, rateL, rateR, initial, hba, not_lt.mpr hba.le]
  have o2 : outcome ⟨d, 0, collideMR initial, b⟩ = .contact .L (3 * d / 5) := by
    simp only [outcome, hitTime, rateL, rateR, initial, collideMR]
    norm_num
    ring_nf
  have o3 : outcome ⟨0, 3 * d / 5, collideLM (collideMR initial), b + 3 * d / 5⟩ =
      .contact .R (27 * d / 5) := by
    simp only [outcome, hitTime, rateL, rateR, initial, collideLM, collideMR]
    norm_num
    ring_nf
  have o4 : outcome ⟨9 * d, 0, rightFirst, b + 6 * d⟩ = .separated := by
    rw [outcome_separated_iff]
    simp only [rateL, rateR, rightFirst, initial, collideLM, collideMR]
    norm_num
  refine ⟨o1, ?_, o2, ?_, o3, ?_, o4⟩
  · unfold step; rw [o1]
    simp only [advance, start, rateL, initial, Option.some.injEq, State.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ring
  · unfold step; rw [o2]
    simp only [advance, rateR, initial, collideMR, Option.some.injEq, State.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ring
  · unfold step; rw [o3]
    simp only [advance, rateL, initial, collideLM, collideMR, rightFirst, Option.some.injEq,
      State.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ring

/-- At equal gaps both contacts are simultaneous; the binary model stops there. -/
theorem equal_gaps_simultaneous (a : ℚ) (_ha : 0 < a) :
    outcome (start a a) = .simultaneous := by
  simp [outcome, hitTime, start, rateL, rateR, initial]

/-- The final middle velocity jumps across `a = b`: by the two schedules it is `-10/27`
for every `0 < a < b` and `10/27` for every `0 < b < a`, so it has no limit as `a - b → 0`. -/
theorem middle_velocity_jump :
    leftFirst.middle = -10 / 27 ∧ rightFirst.middle = 10 / 27 ∧
      leftFirst.middle ≠ rightFirst.middle := by
  refine ⟨left_first_exact.2.1, right_first_exact.2.1, ?_⟩
  rw [left_first_exact.2.1, right_first_exact.2.1]
  norm_num

/-- The final clock is `min a b + 6 |b - a|` on both sides. -/
theorem final_time (a b : ℚ) :
    (a < b → a + 6 * (b - a) = min a b + 6 * |b - a|) ∧
      (b < a → b + 6 * (a - b) = min a b + 6 * |b - a|) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [min_eq_left h.le, abs_of_pos (by linarith)]
  · rw [min_eq_right h.le, abs_of_neg (by linarith)]
    ring

end ThreeBallFreeFlight

#print axioms ThreeBallFreeFlight.left_first_schedule
#print axioms ThreeBallFreeFlight.right_first_schedule
#print axioms ThreeBallFreeFlight.flight_gaps_nonneg
#print axioms ThreeBallFreeFlight.outcome_separated_iff
