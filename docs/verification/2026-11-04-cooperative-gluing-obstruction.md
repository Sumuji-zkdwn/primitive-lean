# Cooperative gluing obstruction from destructive local interference

Date: 2026-11-04. Stacked on verified PR #67.

## Central distinction

PR #67 derives extinction when no **single local system** has enough
capability to meet all simultaneous global requirements. That is not
enough to address systems that can cooperate, delegate or compose their
local operations.

Here both local operations can be applied in **arbitrary finite
sequences**. Each of two global requirements can be achieved using
some local operation, but the two requirements may still be mutually
incompatible over every reachable shared state because later actions
erase earlier success.

Let state `x = (b0, b1) : Bool × Bool`, and let the joint goal mean
`b0=true ∧ b1=true`. Requirements 0 and 1 are individually satisfied
when the corresponding bit is true.

## Destructive versus compatible cooperation

Two available primitives are:

```
A(x) = (true, false)
B(x) = (false, true)
```

They each fulfill one requirement immediately. But each also resets
the other bit. They do not commute, and the invariant
`¬(b0=true ∧ b1=true)` is preserved by EVERY primitive. With initial
state `(false,false)`, PR #60's `invariant_old_word` implies NO
finite composition of `A` and `B` can reach the joint goal.

A non-destructive control keeps prior success:

```
A'(x) = (true, x.2)
B'(x) = (x.1, true)
```

The composite `B' ∘ A'` reaches `(true,true)`; the primitives
commute and retain achieved requirements.

Thus "every requirement has some local successful operator word" does
**not** imply "one common word satisfies all requirements". This is
a gluing obstruction arising from interference during composition,
not from the inability of any local to support one requirement.

## Link to historical preservation

`gatedTimeline step` is a staged two-local system:
- at time 0 both primitives are available;
- at all later times, a local operator is available from current state
  `x` exactly when its result satisfies the JOINT goal.

A generic iff theorem says, at later times, all local domains are
extinct exactly when every primitive fails the joint goal for every
possible input state.

Under destructive cooperation, all resulting states are exclusive,
so every local operator becomes unavailable. The old time-zero
effective action genuinely moves the initial state, while the later
effective transition becomes the identity; PR #66's formal theorem
then proves a failure of historical preservation.

Arbitrary replacement of the underlying local action functions
does not recover history if the already-extinct availability domains
are fixed. Changing the goal, admission policy, domains, or the state
space is a different repair mechanism, not ruled out here.

Under non-destructive cooperation, the time-zero action creates
`(true,false)` and time-one action creates `(true,true)`. Joint
satisfaction is possible, and total local extinction does NOT occur.

## Exact proved candidates

- `destructive_individual_coverage`
- `destructive_no_joint_word` (arbitrary finite words)
- `collective_coverage_does_not_glue`
- `cumulative_jointly_reachable`
- `gated_extinction_iff_no_joint_action` (a necessary and sufficient
  criterion under an explicit postcondition-gating rule)
- `goal_incompatibility_forces_history_loss`
- `destructive_history_not_preserved`,
  `destructive_interval_not_preserved`
- `cumulative_valid_two_time_steps`,
  `cumulative_later_not_totally_extinct`

The five-state or unlimited self-programming claims are not addressed.

## Boundaries

Time is discrete, local action choice is prioritized, and successful
simultaneous satisfaction is defined on one global state. Admission of
local actions based on the entire global postcondition is an explicit
extra assumption. In particular, the same two destructive primitives
could remain available indefinitely if the gate were not imposed;
then failure to reach the goal would NOT by itself imply extinction.

This does not prove that every finite noncommutative operation algebra
fails to glue, nor that local/global incompatibility universally forces
physical extinction. The desired mathematical claim is a conditional
invariant and its sharp constructive countermodel.

## Validation

Additive Lean module:
`linear_input/lean_check/CooperativeGluingObstruction.inc`,
namespace `LinearInputCooperativeGluing`.
Independent brute force:
`tests/test_cooperative_gluing_obstruction.py`.
Pinned integration:
`python -B -X utf8 tools/verify.py --integration-only`,
including all-declaration `lake env lean --trust=0`, axiom audit,
source SHA-256 registration and regression tests.

Do not count these as proved until an exact-head GitHub Actions
integration verification passes. Previous proof sources are unchanged.
