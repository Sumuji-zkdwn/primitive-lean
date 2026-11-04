# Finite internal repair synthesis — 2026-11-04

## Distinguish necessary novelty from construction

PR #60 formalized a *necessity* theorem: old words preserve a region, and if
every local subsystem rejects that entire region at terminal time, no old word
meets the preservation requirement. Any successful extended word must use
a fresh action. That argument, by itself, cannot construct a repair.

This additive file provides a **finite constructive realization**. It reads
an explicit, finite list of candidate states, an explicit finite list of
local subsystems, and Boolean local acceptance tables. It searches for the
first candidate accepted by at least one listed subsystem, then constructs a
single-point state transformer carrying the initial state to that candidate.

Definitions: `chooseTarget`, `patch`, `generate`, `someLocal`,
`synthesizeFromLocals`.

## Claims formalized in Lean

- Search soundness: returned target belongs to candidates and passes the
  acceptance predicate.
- Search completeness **relative to the candidate catalog**: if a candidate
  passes, search returns some target.
- None-case exhaustiveness: if the search returns none, no candidate in
  the supplied catalog passes.
- Local table correctness: `someLocal` is true exactly when a listed local
  subsystem accepts the candidate.
- Generated action soundness: the returned patch maps the start state to
  an accepted candidate, preserving all other states.
- Conditional internal synthesis: if the finite local table captures all
  terminal local acceptance, the old region is invariant and terminally
  extinct, the start has a local witness at time 0, and at least one viable
  candidate appears in the catalog, the algorithm outputs a fresh transformer.
  Applying it for one step preserves both endpoints of the interval and its
  result at the initial state cannot equal any old finite operator word.

This uses the previously verified `one_step_interval` and
`viable_repair_not_old_generated` lemmas, not newly postulated axioms.

## Explicit Fin 3 result

The fixed candidate catalog is `[0,1,2]`; local components are `[0,1]`.
The local Boolean table accepts `x=2` at terminal time only through local 1.
The synthesized patch maps 1 to 2 and otherwise leaves states unchanged:
exactly the fresh primitive in PR #60. In the same concrete model the new
action strictly refines the prior predictive quotient, using PR #56.

An empty acceptance table produces `none` rather than creating a witness.

## What remains unproved

This is a bounded algorithm, not universal self-reproduction. The candidate
state catalog and Boolean local acceptance tests are **given inputs**. The
proof does not show that they arise endogenously, that they can be discovered
from an unreachable outside world, or that a viable target exists without an
explicit feasibility hypothesis. The state type stays fixed; only the
operator vocabulary expands. No claims of continuous-time preservation,
resource conservation, minimal-cost repair, termination of unbounded
recursive synthesis, or autonomous recursive instrument creation are made.

## Validation contract

New source `linear_input/lean_check/FiniteSelfSynthesis.inc`, namespace
`LinearInputFiniteSelfSynthesis`. Independent exhaustive finite oracle:
`tests/test_finite_self_synthesis.py`.

Use `python -B -X utf8 tools/verify.py --integration-only`. Only a successful
exact-head source/hash audit, pinned Lean `--trust=0` compilation, all-
declaration axiom audit and finite tests establish verified status. The PR
must remain draft/unmerged until verification is completed.
