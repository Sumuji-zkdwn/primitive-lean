# Fifth definition as a falsifiable preservation property — 2026-11-04

## Correction to the prior research interpretation

The fifth definition ("保存性") of the user's essay "意味空間の限界に関して"
is **not** introduced here as an axiom that every self-extension must satisfy.
The purpose of this module is to detect when history *cannot be preserved*,
including cases in which global state count and observational diversity
increase. It complements, but must not be silently equated with, PR #60's
conditional interval-maintenance model.

## Formal object and preservation criterion

A deterministic history model `HistoryModel S Ω` contains:
- `observe : S → Ω`, its current readout,
- `advance : S → S`, its next-step operator.

`Preserves A B` holds iff **some injective** `f : S → T` simultaneously
satisfies:
- observation consistency: `B.observe (f x) = A.observe x`;
- temporal consistency: `f (A.advance x) = B.advance (f x)`.

The formula is a chosen operational interpretation of preservation, not a
claim that the original prose uniquely determines it. It preserves any
finite word of the single successor operator by induction, since one-step
transitions commute.

The separate `SnapshotPreserves A B` retains only injectivity and
observation consistency. A valid snapshot map can fail to preserve history.

## Structural impossibility theorems

**Observation extinction.** If there is some earlier state whose observation
label occurs in *no* later state, no history-preserving embedding exists.
No change of the later successor operator can make that historical label
appear if the readout is fixed. Likewise, applying *any* later-state
transformation before that fixed readout cannot recreate the missing label.

**Dynamical incompatibility.** If the old system contains a state moved by
its successor, while every state of the later system is a fixed point,
no injective transition-preserving embedding can exist, independently of
the observer. This obstruction can apply even when an observation-preserving
snapshot embedding exists.

**One-step exact criterion.** If the later observer is injective, historical
preservation is equivalent to the existence of an injective snapshot
representation that respects the *observed* successor in a single step.
This is a genuine necessary-and-sufficient criterion **under the explicitly
stated injective-observer hypothesis**. No general fiber-count
classification of arbitrary dynamical systems is claimed.

Preservation is reflexive and transitive, but is not assumed globally.

## Two exact finite countermodels

1. Older system has `Fin 2` states and observable labels `{0,1}`.
   Later system has `Fin 4` states and labels `{1,2,3}`.
   The global state count and observable diversity **strictly increase**,
   but label `0` is absent. Therefore preservation fails, no matter
   how the successor operation of the later system is rewritten.
2. Earlier system has `Fin 2` and a toggling successor, with the same
   readout on both states. Later system has the same states/readouts, but
   an identity successor. Snapshot preservation is possible, yet
   *historical* preservation is not.

## Why an arbitrary state extension is different from internal repair

The tagged sum `Sum S T` can embed an actual copy of earlier history:
`adjoinOldHistory A B` respects both old and later dynamics.
This is a **real enrichment of the state type**, not a repair performed
inside the later fixed state universe. It cannot make the original
nonpreservation false in retrospect.

The theorem about internal irreparability fixes the later observation.
Changing the observation language, introducing new states, or relaxing
the historical fidelity criteria can evade it. Those changes must be
modeled separately, never claimed to follow from a new transition alone.

## Non-results and remaining tasks

No theorem here says every noncommutative system becomes extinct, or that
finite growth always destroys local histories. The model tracks one total
deterministic successor and a total readout; partial operations, genuinely
time-varying local algebras, decay measures, ordered time intervals, and
endogenous reasons for extinction remain open.

Do not identify the set-theoretic increase of state numbers with improved
semantic fidelity, or the later *addition* of history with *preservation
through* a period during which that history was absent.

## Verification contract

Lean: `linear_input/lean_check/HistoryNonpreservation.inc`,
sole namespace `LinearInputHistoryNonpreservation`.
Finite oracle: `tests/test_history_nonpreservation.py`.
Validator: `python -B -X utf8 tools/verify.py --integration-only`,
including pinned Mathlib/Lean `lake env lean --trust=0`,
all-registered-declaration axiom audit, source provenance SHA-256,
and exhaustive finite regression tests.

All earlier Lean source files are unchanged; source remains candidate until
an exact-head CI success is obtained.
