# Demand capacity, pairwise non-gluing, and derived extinction

Date: 2026-11-04. Additive source stacked on verified PR #66.

## Question
The essay's fifth definition ("保存性") is tested as a property that MAY FAIL.
PR #65 formalized nonpreservation and its irreparable observation/dynamics
obstructions. PR #66 modeled time-dependent local operation loss, but
introduced the total-extinction predicate explicitly.

This experiment asks when finite capacity and simultaneous global
requirements are sufficient to DERIVE total domain loss, then uses
PR #66's historical nonpreservation theorem. No assumption that arbitrary
growth, finite size, noncommutativity, or history dependence alone causes
extinction is made.

## Model and general results

Each local `loc : Λ` has a Boolean support table
`support : Λ → Req → Bool`. It can act under a global demand list
only if it supports **all** requirements on that list:

`Covers support demands loc := ∀ r ∈ demands, support loc r = true`.

`allSupported` is the executable Boolean form, and the exact Boolean/
Proposition equivalence is formally proved.

Increasing the demand list (by inclusion) cannot help a local that already
fails an older demand. The generic capacity theorem assumes:
- Req is a finite set of N possible demand types;
- every listed local supports at most c elements of Req;
- c < N;
- the global demand list contains every Req element.

Under those assumptions, no local covers the global demand. A corresponding
Boolean theorem shows that every local operation becomes unavailable.

`capacityTimeline` uses the *derived* `allSupported` as the time- and
state-dependent availability in PR #66's `LocalTimeline`. The bridge theorem
`capacity_overload_forces_history_loss` shows that, if the old effective
successor moves a state, then total support overload implies failure of a
faithful old-to-later history embedding. This is conditional on the
stated resource bound and full-demand assumption; extinction is no longer
independently postulated.

## Explicit pairwise-but-not-global counterexample

Let there be three requirements 0,1,2 and three local systems 0,1,2.
Local i supports *every requirement except i*. Any two requirements can
be jointly serviced by the remaining local, but no local supports all
three. This is a minimal local-to-global compatibility obstruction:
pairwise joint feasibility does not imply a single simultaneous witness.

At t=0, active demand = [0,1]; local 2 can execute a nontrivial toggle.
At t>=1, demand = [0,1,2]; no local remains available; the effective
transition is forced to become identity. The old nontrivial toggle history
therefore cannot be faithfully preserved after t=0, nor across any
discrete interval that includes a later extinct endpoint. Current
snapshots remain compatible, making the failure strictly dynamical.

## Independent falsifying controls

- Any system with one local supporting all three demands continues to
  operate despite the same global demand growth; capacity c<N is essential.
- A finite library containing two noncommuting swaps can stay available
  indefinitely, so noncommutativity and finiteness alone do not imply
  domain extinction or historical loss.
- Local availability is **conjunctive** for simultaneous demands; a system
  that aggregates independent local solutions by composition or delegation
  needs a different model. "Every pair is feasible" is therefore not
  sufficient for total simultaneous feasibility under this semantics.

## Boundaries

This provides a sufficient finite capacity mechanism, not a universal
explanation for local-system extinction. No physical resource units,
continuous time, universal operation synthesis, or one-to-one identification
with the philosophical essay is asserted. We do not claim that every
global expansion deletes local states, nor that changing an observation
language cannot repair the outcome.

## Verification

`linear_input/lean_check/LocalCapacityIncompatibility.inc`
namespace `LinearInputCapacityExtinction`, additive to previous
`--trust=0` sources.

Python finite reference `tests/test_local_capacity_incompatibility.py`
enumerates every three-by-three Boolean support table, checks demand
monotonicity, the threshold example, and explicit noncommuting controls.

The branch is provisional until its exact source commit passes pinned
Lean/Mathlib `lake env lean --trust=0`, all-declaration axiom audit,
source-provenance hash checks, and all relevant regression tests.
