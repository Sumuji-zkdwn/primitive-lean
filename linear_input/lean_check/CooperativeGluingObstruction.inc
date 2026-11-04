/-!
# Cooperative local action coverage without global operational gluing

Each of two local operations can meet one global requirement, and all
finite action words are allowed. Nevertheless, destructive interference
between operations can make the joint requirement unreachable.

This improves on the single-local capacity obstruction of PR #67:
individual requirements are actionable and arbitrary sequential
cooperation is permitted. An explicit invariant prevents gluing the
two locally successful fragments into a globally successful state.

A contrasting non-destructive library achieves the joint requirement
by a two-letter word. Gating the future availability of local actions
by the joint postcondition derives total local-operation extinction
for the destructive library, then historical nonpreservation using
PR #66. This gating rule is an EXPLICIT modeling assumption.
-/

section

namespace LinearInputCooperativeGluing

open LinearInputOperatorWords
open LinearInputSemanticIntervals
open LinearInputHistoryNonpreservation
open LinearInputTemporalExtinction
open LinearInputFiniteSelfSynthesis

/-- The global requirement must hold in one state, not merely in a
union of outcomes observed in different states. -/
def JointGoal (x : Bool × Bool) : Prop :=
  x.1 = true ∧ x.2 = true

def GoalFlag (x : Bool × Bool) : Bool := x.1 && x.2

theorem goalFlag_false_iff_not_joint (x : Bool × Bool) :
    GoalFlag x = false ↔ ¬ JointGoal x := by
  cases x with
  | mk a b =>
      cases a <;> cases b <;> decide

/-- The first primitive writes the first bit and deletes the second;
the other primitive performs the opposite destructive write. -/
def destructive (loc : Fin 2) (_x : Bool × Bool) : Bool × Bool :=
  if loc = 0 then (true, false) else (false, true)

/-- A non-interfering control retains any previously set bit. -/
def cumulative (loc : Fin 2) (x : Bool × Bool) : Bool × Bool :=
  if loc = 0 then (true, x.2) else (x.1, true)

def Meets (requirement : Fin 2) (x : Bool × Bool) : Prop :=
  if requirement = 0 then x.1 = true else x.2 = true

/-- Joint local coverage permits a DIFFERENT successful action word
for every requirement. It does not assert a global witness. -/
def CollectiveCoverage
    (step : Fin 2 → Bool × Bool → Bool × Bool)
    (start : Bool × Bool) : Prop :=
  ∀ req : Fin 2, ∃ word : List (Fin 2),
    Meets req (run step word start)

def JointlyReachable
    (step : Fin 2 → Bool × Bool → Bool × Bool)
    (start : Bool × Bool) : Prop :=
  ∃ word : List (Fin 2), JointGoal (run step word start)

theorem destructive_individual_coverage :
    CollectiveCoverage destructive (false, false) := by
  intro req
  fin_cases req
  · exact ⟨[0], by decide⟩
  · exact ⟨[1], by decide⟩

theorem destructive_every_primitive_misses_goal
    (loc : Fin 2) (x : Bool × Bool) :
    ¬ JointGoal (destructive loc x) := by
  by_cases h : loc = 0
  · simp [destructive, h, JointGoal]
  · simp [destructive, h, JointGoal]

/-- The obstruction is closed under the entire old action vocabulary,
not merely one operation or two particular orders. -/
theorem destructive_old_invariant :
    OldInvariant (fun x : Bool × Bool => ¬ JointGoal x) destructive := by
  intro loc x _
  exact destructive_every_primitive_misses_goal loc x

theorem destructive_no_joint_word
    (word : List (Fin 2)) :
    ¬ JointGoal (run destructive word (false, false)) := by
  exact invariant_old_word (fun x : Bool × Bool => ¬ JointGoal x)
    destructive destructive_old_invariant word (false, false)
    (by simp [JointGoal])

theorem collective_coverage_does_not_glue :
    CollectiveCoverage destructive (false, false) ∧
    ¬ JointlyReachable destructive (false, false) := by
  constructor
  · exact destructive_individual_coverage
  · rintro ⟨word, hgoal⟩
    exact destructive_no_joint_word word hgoal

theorem destructive_noncommuting :
    destructive 0 (destructive 1 (false, false)) ≠
      destructive 1 (destructive 0 (false, false)) := by
  decide

/-- In the non-destructive control the same individual requirements
compose into one simultaneously satisfying state. -/
theorem cumulative_two_steps_reach_joint_goal :
    JointGoal (run cumulative [0, 1] (false, false)) := by
  decide

theorem cumulative_jointly_reachable :
    JointlyReachable cumulative (false, false) := by
  exact ⟨[0, 1], cumulative_two_steps_reach_joint_goal⟩

theorem cumulative_primitives_commute (x : Bool × Bool) :
    cumulative 0 (cumulative 1 x) =
      cumulative 1 (cumulative 0 x) := by
  rfl

/-- A global demand enforced at time t>0 says a local operation is
enabled only if its resulting state simultaneously satisfies BOTH
requirements. At time 0 either local action is available. -/
def gatedTimeline
    (step : Fin 2 → Bool × Bool → Bool × Bool) :
    LocalTimeline (Bool × Bool) Unit (Fin 2) where
  locals := [0, 1]
  available := fun t loc x =>
    if t = 0 then true else GoalFlag (step loc x)
  action := step
  readout := fun _ _ => ()

/-- Exact criterion at any time after the global demand activates:
all local domains disappear iff no primitive can attain the joint
goal in one step from ANY state. -/
theorem gated_extinction_iff_no_joint_action
    (step : Fin 2 → Bool × Bool → Bool × Bool)
    (time : ℕ) (ht : time ≠ 0) :
    AllExtinct (gatedTimeline step) time ↔
      ∀ loc (x : Bool × Bool), ¬ JointGoal (step loc x) := by
  constructor
  · intro he loc x
    have hloc : loc ∈ ([0, 1] : List (Fin 2)) := by
      fin_cases loc <;> simp
    have hd := he x loc hloc
    have hf : GoalFlag (step loc x) = false := by
      simpa [gatedTimeline, ht] using hd
    exact (goalFlag_false_iff_not_joint (step loc x)).mp hf
  · intro h x loc _
    have hf : GoalFlag (step loc x) = false :=
      (goalFlag_false_iff_not_joint (step loc x)).mpr (h loc x)
    simpa [gatedTimeline, ht] using hf

/-- Thus the all-extinct hypothesis of PR #66 can now be derived
from a joint-goal incompatibility condition on cooperating actions. -/
theorem goal_incompatibility_forces_history_loss
    (step : Fin 2 → Bool × Bool → Bool × Bool)
    (time : ℕ) (ht : 1 ≤ time)
    (hmiss : ∀ loc x, ¬ JointGoal (step loc x))
    (hmoving :
      stepAt (gatedTimeline step) 0 (false, false) ≠ (false, false)) :
    ¬ Preserves (historyAt (gatedTimeline step) 0)
        (historyAt (gatedTimeline step) time) := by
  have htime : time ≠ 0 := by omega
  exact extinction_forces_nonpreservation
    (gatedTimeline step) 0 time (false, false) hmoving
    ((gated_extinction_iff_no_joint_action step time htime).mpr hmiss)

theorem destructive_initially_moves :
    stepAt (gatedTimeline destructive) 0 (false, false) ≠
      (false, false) := by
  decide

theorem destructive_later_extinct (time : ℕ) (ht : 1 ≤ time) :
    AllExtinct (gatedTimeline destructive) time := by
  have htime : time ≠ 0 := by omega
  exact (gated_extinction_iff_no_joint_action
    destructive time htime).mpr destructive_every_primitive_misses_goal

theorem destructive_history_not_preserved (time : ℕ) (ht : 1 ≤ time) :
    ¬ Preserves (historyAt (gatedTimeline destructive) 0)
      (historyAt (gatedTimeline destructive) time) := by
  exact goal_incompatibility_forces_history_loss destructive time ht
    destructive_every_primitive_misses_goal destructive_initially_moves

theorem destructive_interval_not_preserved
    (stop : ℕ) (ht : 1 ≤ stop) :
    ¬ PreservedOn (gatedTimeline destructive) 0 stop := by
  exact interval_with_extinct_endpoint_is_not_preserved
    (gatedTimeline destructive) 0 stop 1 (by omega) ht
    (false, false) destructive_initially_moves
    (destructive_later_extinct 1 (by omega))

/-- This loss is operational rather than a loss of current readout:
the state can still be embedded as a snapshot with constant output. -/
theorem destructive_snapshots_still_preserved (time : ℕ) :
    SnapshotPreserves (historyAt (gatedTimeline destructive) 0)
      (historyAt (gatedTimeline destructive) time) := by
  refine ⟨fun x => x, ?_, ?_⟩
  · intro x y h
    exact h
  · intro x
    rfl

/-- Changing only the destructive actions does not restore historical
fidelity when their already-extinct availability domains are held
fixed. Changing the domains or the global goal is outside this theorem. -/
theorem destructive_no_action_rewrite_repairs_history
    (time : ℕ) (ht : 1 ≤ time)
    (newActions : Fin 2 → Bool × Bool → Bool × Bool) :
    ¬ Preserves (historyAt (gatedTimeline destructive) 0)
      (historyAt
        (reassignActions (gatedTimeline destructive) newActions)
        time) := by
  exact extinction_blocks_every_local_action_rewrite
    (gatedTimeline destructive) 0 time (false, false)
    destructive_initially_moves (destructive_later_extinct time ht)
    newActions

/-- By contrast, cumulative cooperation succeeds at the two-step
trajectory, despite each local alone failing to attain the goal
from the initial empty state. -/
theorem cumulative_valid_two_time_steps :
    JointGoal
      (stepAt (gatedTimeline cumulative) 1
        (stepAt (gatedTimeline cumulative) 0 (false, false))) := by
  decide

theorem cumulative_later_not_totally_extinct :
    ¬ AllExtinct (gatedTimeline cumulative) 1 := by
  intro he
  have havail :
      (gatedTimeline cumulative).available 1 1 (true, false) = true := by
    decide
  have hdisabled := he (true, false) (1 : Fin 2) (by simp)
  rw [hdisabled] at havail
  cases havail

end LinearInputCooperativeGluing
