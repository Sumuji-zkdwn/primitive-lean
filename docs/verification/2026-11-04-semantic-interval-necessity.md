# Semantic interval preservation and operator necessity (2026-11-04)

## Purpose

Formalize a *conditional* reading of the February 2026 essay on the limits of
meaning space, using the verified operator-word and vocabulary-refinement
development from PR #55–#57. It is **not** an equivalence proof between a
philosophical essay and an arbitrary physical/cognitive process.

## Definitions and their exact scope

- `alive t loc x` states that local component `loc` can maintain global
  state `x` at discrete prefix time `t`.
- `HasLocal alive t x` means *at least one* local component supports the
  current global state.
- `IntervalSurvival alive step word x` checks viability after **each prefix**
  of the actual finite operator word; time is the prefix length.
- `OldInvariant region old` means each old primitive preserves `region`.
- `TerminalExtinction alive region n` means **all local components** reject
  states in `region` at the terminal time `n`.

No assumption of continuous time, state creation, bounded resources, or
automatically inferred local extinction is made. The model allows different
local components to replace one another. The same underlying state type is
retained before and after vocabulary expansion.

## Core logical chain

1. `invariant_old_word`: every old word remains in the invariant region.
2. `no_old_word_reaches_survival`: when every terminal local rejects that
   region, no old word can maintain terminal viability.
3. `interval_requires_new_symbol`: if an extended word of terminal length
   `n` maintains viability at *every prefix*, that word necessarily contains
   at least one symbol from the fresh alphabet.
4. `viable_repair_not_old_generated`: any explicitly supplied viable repair
   state is not reachable by any old word from the initial state.
5. `viable_and_strict_extension`: when a fresh primitive also breaks the
   previous complete word-observation equivalence, its successful interval
   action coincides with a **non-injective forgetting quotient**. The
   quotient assertion reuses PR #56, not a newly assumed proposition.

### Finite witness and decisive counterexample

- Initial state is 1 of `Fin 3`, old action is identity, and new action maps
  1 to 2. Local 0 supports state 1 only at time 0; local 1 supports state 2
  at time 1. Old words fail, the new action survives, and it splits the old
  quotient (which cannot distinguish 0 from 1).
- Separate model: local 0 supports state 1 at time 0 and goes extinct at
  time 1, but local 1 can support **the same state 1** at time 1. The old
  identity word preserves the interval. Extinction of one local component
  is therefore insufficient for forced operator novelty.

## Explicit boundaries

The existence of a repair, its discoverability, and a self-generating builder
are **not** proved. Stronger claims would require a constructive synthesis
operator and a corresponding success/termination theorem. Even forced
operator novelty does **not** always imply a finer meaning quotient: PR #57
proves that a conservative, nonword-generatable operator can exist.

The terminal-extinction assumption is stronger than the mere disappearance of
one local system. Replacing it by such a weaker condition makes the general
necessity claim false, as the countermodel demonstrates.

## Validation contract

Source: `linear_input/lean_check/SemanticIntervalNecessity.inc`
Namespace: `LinearInputSemanticIntervals`.
Independent regression: `tests/test_semantic_interval_necessity.py`.

Before a successful source-pinned GitHub Actions run, the declarations in this
file are **proof candidates**, not verified theorems. The required audit is
`python -B -X utf8 tools/verify.py --integration-only`, including pinned
`lake env lean --trust=0`, all-declaration axiom audit and preserved source
hashes. No existing original proof file has been modified.
