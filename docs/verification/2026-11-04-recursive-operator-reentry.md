# Recursive operator re-entry — finite catalogue closure (2026-11-04)

## Purpose and provenance

The existing verified chain distinguishes (i) finite operator-word observational
equivalence in PR #55, (ii) compatibility, strict quotient refinement, and
nonword primitives in PR #56–57, (iii) necessity of a fresh action under an
old-invariant terminal local-extinction barrier in PR #60, and (iv) executable
bounded-candidate repair synthesis in PR #61.

This module makes the finite operator catalogue an **input to its next generation
round**. Descriptors produced in round k become available to the fixed
child-generation function in round k+1. No theorem asserts that the generator
rule itself rewrites its own code.

## Definitions

For an arbitrary descriptor type α with decidable equality, each descriptor
t denotes the explicit state transformer `patch start t`. A fixed external
rule `children : α → List α` supplies finitely many candidate successor
descriptors. A Boolean predicate `viable` filters the novel frontier.

- `novelFrontier children known` contains child descriptors that have not
  yet been registered.
- `reenter children viable known` selects a viable fresh child and appends it
  to the existing catalogue, or returns none.
- `iterateReentry children viable n known` performs at most n such rounds;
  a failed round keeps the last valid catalogue.

## Formal statements

1. Every selected descriptor occurs in the child frontier, passes the
   viability test, and was not already registered.
2. A successful round preserves all old catalogue entries and grows its length
   strictly by one.
3. Each new descriptor denotes a **functionally distinct** one-point patch.
   Functional difference is *not* automatically an increase in observational
   distinguishability.
4. The generator is complete within its current finite frontier. A result of
   none is a certificate that no viable fresh generated child exists.
5. Bounded iteration never deletes old entries and is stable after a failed
   generation round.
6. Under the terminal viability, invariant region, and local-equivalence
   assumptions of PR #60, a reentered candidate constructs a one-step
   interval-preserving repair unreachable through the old vocabulary.
7. Fin 4 witness: [0] → [0,1] → [0,1,2] → [0,1,2,3], then saturation.

## Boundaries

The fixed `children` function is externally provided; it is not inferred
from a model of the external world or proven self-modifying. The underlying
state type does not change. The construction does not produce infinitely
many different patches on a finite state set, solve all repair problems, or
guarantee strict growth of the predictive quotient.

If the current generated frontier is empty or contains no viable unknown
descriptor, the algorithm stops. This is a bounded, deterministic form of
operator **re-entry**, not a fully autonomous self-expanding computer.

## Validation

Source: `linear_input/lean_check/RecursiveOperatorReentry.inc`.
Namespace: `LinearInputRecursiveReentry`.
Independent oracle: `tests/test_recursive_operator_reentry.py`.
Pinned verification: `python -B -X utf8 tools/verify.py --integration-only`,
combined `lake env lean --trust=0`, no forbidden proof shortcuts,
all-declaration axiom audit, and source/hash checks.

Candidate status until an exact-head CI success is observed.
