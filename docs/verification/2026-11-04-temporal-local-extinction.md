# Temporal extinction of partial local operations (2026-11-04)

## Purpose

Continue verified PR #65's interpretation of the fifth definition:
**preservation is an operational property to test and potentially falsify**,
not a universal axiom that an expanding meaning space must maintain.

The new source studies genuine *time-dependent loss of local operation
domains*, rather than postulating a globally fixed action or assuming
historical restoration after loss.

## Local operations and historical preservation

`LocalTimeline S Ω Λ` contains:
- `locals : List Λ`, a prioritized finite library of local operations;
- `available : ℕ → Λ → S → Bool`, time- and state-dependent domains;
- `action : Λ → S → S`, the action of each local operation;
- `readout : ℕ → S → Ω`, the time-dependent observation.

The effective `stepAt X t x` executes the first available local operator
at time t and state x, or stutters at x if none is available.

`historyAt X t` freezes the corresponding observation and step as PR #65's
`HistoryModel`. Preservation means an injective state embedding commuting
with both observation and successor; snapshots alone are weaker.

`AllExtinct X t` says **every** listed local operation is unavailable at
every underlying state at time t. This is stronger than the extinction of
one local component.

## Proved targets (pending exact-commit verification)

1. `extinct_step_identity`: total disappearance of local operation domains
   forces the effective successor to become the identity.
2. `extinction_forces_nonpreservation`: if some earlier state genuinely
   moves and every later local domain is empty, there can be no
   injective observation- and action-preserving historical embedding,
   independent of the actual observer.
3. `extinction_blocks_every_local_action_rewrite`: the obstruction
   persists under arbitrary changes to the local action functions
   **provided all availability domains stay empty**.
4. `preservation_iff_old_stationary_under_extinction`: if earlier and
   later readouts agree, historical preservation under total later
   extinction is equivalent to the earlier effective successor already
   being stationary. This is an exact boundary theorem, not just a
   one-direction obstruction.
5. `interval_with_extinct_endpoint_is_not_preserved`: the obstruction at
   one time in the closed discrete interval falsifies interval-wide
   historical preservation, with the prior moving-state assumption.

## Sharp finite witness and counterexamples

The two-state witness starts with an active toggle performed by local
system 0 at time 0. At time 1 system 0 disappears, but local system 1
performs the same toggle; **historical preservation still holds**.
From time 2 onward both local domains disappear, leaving an identity
successor. The original toggling history now has no faithful embedding,
although snapshot observations remain fully compatible.

Every rewrite of the local action functions still fails while all local
domains remain empty, which is a no-repair result for a fixed *operation
availability* structure. Reactivating the old local domain at time 2
recovers historical preservation, illustrating exactly which assumption
the repair must violate.

**Endpoint recovery does not imply interval preservation.** An added
`recoveredAfterGap` model loses every local operation at time 2 and
reactivates the original toggle at time 3. Faithful old-to-new embeddings
exist between times 0 and 3, but no faithful embedding exists between
times 0 and 2. Therefore `PreservedOn recoveredAfterGap 0 3` is false.
This isolates the interval-specific failure: later representability
does not make the entire earlier interval historically preserved.

The proof does **not** assert that no possible extension of the state
space or update of availability/observations can restore a missing
history. PR #65 separately shows loss of an observable label may be
irreparable even with arbitrary local transition rewrites while the
observer is fixed.

## Mathematical limits

- Time is discrete, and local operation choice is deterministic and
  prioritized. The model does not yet cover simultaneous interacting
  operations, state-dependent nondeterministic outcomes, probabilistic
  extinction, continuous-time decay, or changes of the state type itself.
- Absolute disappearance of local operations is an **input assumption**;
  it is not derived from global growth, finite resources or incompatibility.
- The one-step preservation/interval predicate chosen is a modeling
  decision, not proof that the user's original wording uniquely determines it.
- The model contains a counterexample proving that one local extinction
  does not imply total nonpreservation.

## Validation

File: `linear_input/lean_check/TemporalLocalExtinction.inc`.
Namespace: `LinearInputTemporalExtinction`.
Independent brute force: `tests/test_temporal_local_extinction.py`
(enumerates all two-state, two-local operator maps and availability masks).

The entire stacked proof is verified via
`python -B -X utf8 tools/verify.py --integration-only` with pinned
Lean/Mathlib `lake env lean --trust=0`, all-declaration axiom audit
and SHA256 source provenance. Until exact-head success, new statements
remain candidates. Previous proof source files are unmodified.
