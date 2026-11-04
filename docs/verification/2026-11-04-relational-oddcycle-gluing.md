# Relational gluing: pairwise feasibility versus shared global realizability

Date: 2026-11-04. New additive module branching from verified PR #69,
without editing the independently evolving concurrent partial-write branch.

## Distinguishing three different meanings of "local compatibility"

Let `S` be the set of possible global states and `I` the index set of
local constraint systems. Each `C i : S -> Prop` is a relational
constraint that can only be evaluated on a *complete shared global state*.

There are three distinct feasibility levels:

- `IndividuallyFeasible C`: each local constraint C(i) has SOME witness.
- `PairwiseFeasible C`: each PAIR C(i),C(j) has a common witness, which
  may differ for different pairs.
- `GloballyFeasible C`: ONE shared state satisfies ALL constraints.

The implication chain global => pairwise => individual is valid for
arbitrary index and state types. Both reverse implications are false,
even for finite Boolean models.

The crucial point is the difference between `∀i,j ∃s` and
`∃s ∀i,j`. Neither conjunction distributes over the choice of
possibly different witnesses.

## Strict counterexamples

**One Boolean coordinate, two conflicting requirements.**
Local 0 requires `s=true`; local 1 requires `s=false`. Each individual
constraint is satisfiable, but no common state satisfies both, so
`IndividuallyFeasible` does not entail `PairwiseFeasible`.

**Three Boolean coordinates, three disequality edges.**
A single global state is `s : Fin 3 -> Bool`. Three local relational
constraints require:

`s(0) ≠ s(1)`, `s(1) ≠ s(2)`, and `s(2) ≠ s(0)`.

Every two constraints are jointly satisfiable, but no complete state
satisfies all three. An odd cycle cannot be two-coloured. A four-cycle
is a contrasting globally satisfiable example. A further independent
Python oracle checks cycles of size three through eight.

## Why this does NOT contradict the exact fixed-write gluing theorem

An ordinary partial assignment `p : Coord -> Option Value` prescribes
particular values at specific coordinates. With a supplied fallback
value, all such fixed assignments can be combined into one global state
iff they AGREE on all shared defined coordinates. Here pairwise
agreement IS sufficient.

The odd-cycle case is different: each local constraint is a RELATION
allowing many complete states. Its pairwise feasibility checks are
allowed to choose different complete states for different pairs.
Therefore it is possible for all pairs to have witnesses without a
single globally consistent assignment.

An additional global constraint can also rule out an otherwise
perfectly compatible family of fixed local writes. Having a total
assignment does not guarantee that it meets every external global goal.

## Interpretation for PR #69 and the fifth definition

PR #69 already showed that individual operations can produce different
local successes without one finite sequential word producing the
combined goal. This PR shows a corresponding phenomenon in **parallel
constraints**: individual and even pairwise simultaneous feasibility
do not guarantee global relational feasibility.

The fifth definition ("保存性") remains a **falsifiable property**.
Neither relational incompatibility nor failure to glue, by itself,
means that local operations have physically vanished or that historical
preservation fails. Connecting this obstruction to PR #66's history
theorems requires a separately stated admission rule or resource
constraint, not a hidden universal preservation/decay assumption.

This source does not make claims about arbitrary continuous-time
systems, quantum dynamics, the universal termination problem, or
unrestricted self-generation of operators.

## Verification scope

Lean source: `linear_input/lean_check/RelationalOddCycleGluing.inc`
Namespace: `LinearInputRelationalGluing`.
Finite oracle: `tests/test_relational_oddcycle_gluing.py`.
Integration: `python -B -X utf8 tools/verify.py --integration-only`,
pinned Lean/Mathlib `lake env lean --trust=0`, all-declaration axiom
audit, SHA-256 source-provenance checks, and regression tests.

New declarations are proof candidates pending exact-head CI success.
Prior source files and main are unchanged.
