# Parallel local-to-global gluing, admissibility and reachability

Date: 2026-11-04. Stacked on independently verified PR #69.
Fifth-definition preservation is tested as a falsifiable property; it is
not introduced as a universal axiom.

## Distinguish three independent meanings of "gluing"

Local operation outcomes are represented by partial assignments
`part : Λ → I → Option V`, where `none` means a local component
does not specify a value at a coordinate. A collection `locals`
specifies the active contributors.

1. **Value/overlap consistency:** any two local values that specify
   the same coordinate must agree.
2. **Global admissibility:** the assembled global assignment must pass
   a separately supplied system-wide predicate.
3. **Operational realizability:** the assembled assignment must actually
   be obtainable from the initial state by a finite word in the
   available action vocabulary, not simply be set-theoretically
   constructible.

These criteria are not interchangeable.

## General Lean statements

`PairwiseCompatible locals part` means every overlapping coordinate
is assigned the same value by all relevant locals.
`Represents locals part g` says a total global assignment respects
every locally specified value. `HasGlue` quantifies over such an
assignment.

If V is inhabited, `gluing_iff_pairwise_compatible` proves:

`HasGlue locals part ↔ PairwiseCompatible locals part`.

The `[Inhabited V]` requirement provides a value for coordinates not
specified by any local system. `CoversCoordinates` further says that
every coordinate has at least one defined local value. Under this
coverage hypothesis, `gluing_unique_under_full_coverage` proves
that the global assignment is unique and equal to the constructed
canonical assignment.

Global policy matters. With full coverage, `admissible_glue_iff`
proves that an admissible total assignment exists exactly when
overlap compatibility holds and the canonical assembled state
satisfies the policy.

Operational dynamics matter independently. `operational_gluing_iff`
proves, assuming coordinate coverage, an exact three-way condition:

```
operational gluing
↔ overlap compatibility
  ∧ global admissibility of canonical glue
  ∧ some executable finite action word produces the canonical observation
```

The action language can act on an arbitrary state type S with an
observation `S → I → V`. Thus this is an exact criterion for the
specified operational model, not a claim of physical realizability
or computational resource feasibility in all possible systems.

## Two-local, two-coordinate countermodels

**Overlapping full results conflict:** PR #69's destructive primitives
produce full assignments (true,false) and (false,true). Treated as
two simultaneous full local outcome reports, they disagree on each
coordinate and have no common global gluing.

**Disjoint reports are compatible but policy can forbid the result:**
local 0 reports coordinate 0=true; local 1 reports coordinate 1=true.
Their partial assignments overlap nowhere and uniquely glue to
(true,true). A global rule that forbids both bits being true makes
an *admissible* glue impossible despite local compatibility.

**Set-theoretic glue need not be operationally reachable:** The same
disjoint reports uniquely glue to (true,true). Yet every finite
composition of PR #69's destructive operators leaves at most one bit
true. Therefore no operator word realizes the glued state. A
non-destructive cumulative library does reach that state in two steps.

These examples isolate separate obstructions without hiding the
destructive side effects of actual operators.

## Scope and remaining issues

Partial functions into a common type are a **specific representation**
of simultaneous local results. Two-state nondeterministic transitions,
contextual measurements, memory-dependent observations, incompatible
local coordinate charts, partial order constraints on time, and
distributed multi-agent synchronization require additional structure.

Even when a consistent and admissible total assignment exists, the
actual operation vocabulary may still lack a word to realize it.
Likewise, reaching the goal at an endpoint does not imply interval
history preservation: PR #66 proves that earlier history can be lost
in between. The gluing theorem is not an axiom of universal
preservation.

## Validation
New additive source:
`linear_input/lean_check/ParallelLocalGluing.inc`.
Namespace `LinearInputParallelGluing`.
Finite oracle:
`tests/test_parallel_local_gluing.py` (all 81 local report tables).
Pinned Lean/Mathlib `--trust=0`, all-declaration axiom audit,
source SHA256 provenance, all regression tests.

Proof statements must not be counted verified until the exact-head
GitHub Actions CI result is successful.
