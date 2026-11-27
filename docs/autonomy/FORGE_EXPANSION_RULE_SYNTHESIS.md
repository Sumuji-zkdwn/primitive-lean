# Synthesis of saturation-preserving expansion rules

Stacked research on #293 and #292. No production ledger, main branch, or
scheduler changes. This explores expansion programs rather than choosing
one fixed product construction. The grammar and sufficient proof schemas
are reviewed fixed code; arbitrary grammar discovery is not claimed.

## Rules and proof

Given a parent saturated as T_n, consider adjoining one point, taking a
two-coordinate product, or taking a three-coordinate product.

For point adjunction, extend parent successor and transposition by fixing
the new point. Connect it to an old point by a bridge transposition.
The old symmetric group and bridge generate S_(n+1). An elementary collapse
is obtained either by extending the old collapse or by merging the added
point into the anchor. Together these generate T_(n+1).

For a product, the grammar generates local swaps and collapses conditioned
on each other coordinate: unconstrained, zero, or last. Free translations
are available on every axis. The structural verifier demands one isolated
transposition for each axis, and one isolated collapse. Translation
conjugates of the transpositions yield every edge transposition of the
connected Cartesian grid. Thus they generate the full symmetric group.
Conjugates of the elementary collapse then yield all merges; collapsing
fibers and permuting representatives realizes every transformation.

A fully guarded collapse on X^d has rank n^d-1. A singular independent
coordinatewise product has rank at most (n-1)n^(d-1), so the certified
interaction is genuinely outside the old independent product family.

These are sufficient, not necessary, structural criteria. A rejected
candidate is not claimed to be nonsaturating. The formulas are classical
mathematical arguments and are not yet Lean-formalized. The root's
rank-separation proof can optionally be rechecked with --kernel; child
canonical gate calls are abstract parent operations, not compiled words
in the actual original alphabet.

## Search and tests

| Shape | Generated | Passed criterion | Rejected |
| --- | ---: | ---: | ---: |
| Point | 4 | 4 | 0 |
| Product2 | 54 | 16 | 38 |
| Product3 | 19683 | 768 | 18915 |

All 20 passing point/product2 candidates for n=2 were independently
checked by exact transformation-monoid closure, including permutation
closure. For the selected product3 rule, gate behavior was checked on
every state for parent cardinalities 2 through 5. Restart, tampering,
and budget stops were tested. Symbolic growth mode selected 2, 8, 512,
134217728, 18014398509481984 under a 65-bit cardinality cap. Compact
mode selected 2, 3, 4. Counts refer to candidate rules, not necessarily
nonisomorphic or semantically distinct rules.

The choice objective is explicit: growth prioritizes largest resulting
cardinality under the bit budget, compact prioritizes fewest generators
then largest cardinality. The ledger records and replays all choices,
proof scopes, and candidate counts. Stop on budget or lack of a certified
rule; never infer saturation from a failed search.

## Reproduction

```sh
python -B -m tools.autonomy.forge_rule_search --selftest
python -B -m tools.autonomy.forge_rule_search --output verification/rules-model --steps 4
python -B -m tools.autonomy.forge_rule_search --root forge --state tests/fixtures/forge_monoid_evolution6.json --semantic tests/fixtures/forge_monoid_semantic4.json --output verification/rules-forge --steps 2
```

Use a fresh output path and the same policy and budget for restart. CI
reconstructs the actual historical Forge root and adds the rank-255
candidate in shadow, not production. The next work is constructive
compilation of canonical parent gates, and a general Lean saturation
proof layer. Local checks here do not establish production activation.
