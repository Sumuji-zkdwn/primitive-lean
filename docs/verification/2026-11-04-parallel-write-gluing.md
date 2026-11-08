# Parallel local write gluing: exact finite-family criterion

> PR #71 originally placed this proof in `ParallelLocalGluing.inc` under the namespace `LinearInputParallelGluing`, the same path and namespace as the different proof of PR #70. It was integrated under the names above so that both coexist; the Lean text is otherwise byte-identical to commit `fac681e`.

Date: 2026-11-04. Additive formalization stacked on verified PR #69.

## Mathematics and relation to preceding work

PR #67 showed an obstruction when no single local can handle the full
demand. PR #69 allowed sequential cooperation but exhibited destructive
interference: each demand can be reached by its own finite action word,
while no word realizes both demands together.

The present model addresses **simultaneous** local proposals rather than
sequential action words. A local system writes a *partial assignment* of
values into coordinates of one common global state, and an amalgamation
must honor every local write on the same underlying coordinates.

## Exact definitions

- Coordinate type `I`; value type `V`.
- A local proposal `p : I → Option V`; `none` means no write.
- `Compatible p q` means at every common written index, both
  proposals require exactly the same value.
- `Realizes s p` means the global state `s : I → V` satisfies each
  value explicitly written by `p`.
- `glue base p q` chooses p's value, then q's if p is undefined,
  and retains the base otherwise.

The exact two-proposal theorem is:

`Compatible p q ↔ ∃ s, Realizes s p ∧ Realizes s q`.

The forward direction supplies an executable gluing construction.
The reverse direction forbids hidden incompatibility: one common
state cannot simultaneously assign unequal values at the same index.

## More than two local systems

`firstWrite ps i` scans a finite list for its first proposal defined
at index `i`; `glueAll base ps` supplies the corresponding global
state. `PairwiseCompatible ps` means **every ordered pair** of
members agrees wherever their writes overlap.

`pairwise_iff_exists_global` proves, for *arbitrary finite families*:

```
PairwiseCompatible ps
  ↔ ∃ global, ∀ p ∈ ps, Realizes global p
```

It does NOT impose a fixed bound on the number of local systems.
The global state is unique on coordinates explicitly written by
at least one member, and the chosen base state is retained on all
untouched coordinates. Without a base value, the unassigned
coordinates need not have a preferred completion.

This is a concrete gluing theorem for partial functions. It is
not an unrestricted sheaf gluing theorem for arbitrary presheaves
or a claim of consistency for arbitrary overlapping operations.

## Explicit finite countermodels

- Two local proposals write True and False to coordinate 0.
  Each proposal is internally valid, but there is no global state
  realizing both.
- Two other proposals write True to disjoint coordinates 0 and 1.
  The canonical global state assigns both True.
- Two proposals writing the *same* True value at one overlapping
  coordinate can be glued despite the overlap itself.
- The whole-state destructive outputs `(True,False)` and
  `(False,True)` from PR #69 become incompatible full writes,
  whereas the noninterfering partial-coordinate updates glue.

## Historical preservation: separate condition

We additionally build a *controlled* temporal gate:

- time 0: a two-state toggle local action is available;
- time 1: it remains available iff the two concurrent partial-write
  proposals are compatible.

Under precisely that gate (and the same fixed old action/observer),
historical preservation is equivalent to overlap compatibility.
If proposals conflict, every local operation domain becomes empty,
and PR #66's extinction obstruction forces historical nonpreservation.
If they are compatible, the original toggle successor still exists
and the identity state injection preserves the history.

**The gate is an explicit assumption**, not a theorem that conflicting
parallel writes inherently destroy all available actions. Different
policies might reject one proposal, schedule operations sequentially,
use conflict resolution, introduce arbitration, or change the state
representation. Those alternatives are outside this model.

Compatibility alone does NOT imply PR #65 historical preservation if
the later successor or observer changes independently of this gate.
The fifth definition remains a property to falsify, not an axiom
demanding preservation.

## Limits and next steps

The finite patch family is synchronous, all writes use the same
coordinate and value types, and gluing is extensional. This
formalization says nothing about network delays, causal order,
resource contention, partial read dependencies, transactional
isolation, arbitrary non-commuting event streams, or contextual
observational equivalence.

To address those cases, one would need to add explicit read sets,
causal constraints, interleaving semantics and an observation-level
fidelity test. None are silently inferred from patch compatibility.

## Verification contract

Source: `linear_input/lean_check/ParallelWriteGluing.inc`
Namespace: `LinearInputParallelWriteGluing`.
Test oracle: `tests/test_parallel_write_gluing.py`, enumerating all
two-coordinate writes with each value in `{none,false,true}`, for
families of up to four proposals, including every global Bool state.

Pinned full check:
`python -B -X utf8 tools/verify.py --integration-only`,
including `lake env lean --trust=0`, all-declaration axiom audit,
SHA256 manifest/source provenance and the entire repository test set.
New Lean statements remain candidates until exact-head CI passes.
Prior source files are untouched.
