# Mutable rule-table self-modification: finite proof scope
**Date:** 2026-11-04

## Research position

PR #62 verified **bounded recursive re-entry of newly registered operator
descriptors** under a fixed `children` function. The new experiment changes the
object-level generation rules themselves, instead of merely reusing a fixed rule
table. It is deliberately weaker than universal self-programming: the
higher-order `bootCompiler` (which maps learned descriptors to new rule edges)
remains a fixed, independently supplied piece of code.

## Precise model

A machine state is a pair `(known, edges)`. The `known` list contains
registered one-point patch descriptors (target state values). The `edges`
list consists of pairs `(source, target)`, indicating a candidate operator
descriptor `target` can be constructed from the known descriptor `source`.

On each step, the machine:
1. computes candidate targets by interpreting its current rule-edge table
   over known source descriptors;
2. discards previously known targets and targets failing a Boolean viability test;
3. selects the first viable candidate and appends it to `known`;
4. computes fresh rule edges from that newly learned descriptor using the
   fixed compiler, then **appends those edges to its own mutable rule table**.

This is a form of staged rule-data self-modification with a fixed meta-level
interpreter. The new rules become available to the very same generation
mechanism in subsequent rounds.

## Claimed Lean proof obligations

- `modifyStep_sound`: every accepted descriptor is fresh and viable; the
  new state equals the previous catalogue plus the descriptor and the
  previous edge table plus the compiler's exact output.
- `modifyStep_complete`: a viable unknown candidate in the current
  generated frontier suffices for a successful step.
- `modifyStep_none_certificate`: failure means no viable unknown descriptor
  can be reached by the **currently installed** rules.
- `modifyStep_strict_growth`: every successful step strictly grows the
  catalogue, without erasing existing descriptors or rule edges.
- `reactivation_requires_rule_edit`: with an identical known catalogue,
  viable predicate and meta-compiler, a machine that can advance and one
  that cannot must have different object-level rule tables.
- `modified_rule_repair_survives`: link the exact accepted operator to
  PR #60's old-region extinction obstruction, conditional on viability
  of the local support predicate and old invariant preservation.
- `iterateMachine_stops`: saturated generation remains stable after a
  failed step.

## Concrete four-state controlled comparison

The fixed meta-compiler maps descriptor 1 to new edge `1 -> 2`, descriptor
2 to new edge `2 -> 3`, and all others to the empty list.

The seed machine has known list `[0]` and the single edge `0 -> 1`.
Its succession is:

```
known [0]         edges [0->1]
known [0,1]       edges [0->1,1->2]
known [0,1,2]     edges [0->1,1->2,2->3]
known [0,1,2,3]   edges [0->1,1->2,2->3]
then saturation
```

The frozen comparison has the **same** `known=[0,1]` as the first modified
state, but only the initial rule `0 -> 1`. It cannot generate a novel
descriptor, while the internally modified state advances to descriptor 2.
Thus the renewed generation is causally attributable to an actual change
in the installed rule table, not merely to an enlarged `known` list.

## Boundaries and counterclaims

The meta-compiler is not learned, rewritten, or discovered. This model does
not establish an unrestricted hierarchy of self-modifying meta-rules or
guarantee indefinite growth. Every round must pass an explicit viability
condition, and a finite descriptor universe can saturate. Distinct learned
operator patches need not increase the observational quotient, even if they
are functionally distinct.

In particular, the philosophical claim that the "natural cage" must expand
is **not** a theorem without preservation, extinction, representability
and feasibility conditions. Here those conditions are explicit hypotheses.

## Audit

Source: `linear_input/lean_check/RuleSelfModification.inc`
Namespace: `LinearInputRuleSelfModification`.
Regression: `tests/test_rule_self_modification.py`.
Verifier: `python -B -X utf8 tools/verify.py --integration-only`;
full registered `lake env lean --trust=0` build and axiom audit.

The original proof sources of PR #55–#62 are unchanged. This source is a
candidate until commit-pinned CI demonstrates successful compilation and
allowed axioms only.
