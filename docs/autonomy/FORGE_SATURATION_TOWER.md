# Saturation-triggered product tower (shadow controller)

This is an independent bounded controller, stacked on the rank-255 research
PR #292. It never writes a production ledger, schedules jobs, or merges code.
The Forge root includes the proposed collapse in a shadow alphabet, not an
assertion that generation seven was admitted into production.

## Saturation criterion and transition

Let n >= 2 and T_n be all endomaps of an n-element set. A cyclic successor C,
a transposition S=(0 1) and an elementary collapse E=(0 -> 1) generate T_n:
conjugating S by powers of C supplies adjacent swaps; permutations conjugate
E to any elementary collapse. Every endomap factors into a collapse of each
fiber to a representative followed by a permutation of the representatives
onto the distinct target values.

Once T_n is certified, replace X by X x X and use high/low coordinates (h,l).
Construct child gates by controlled applications of the parent's gates:

- C': apply C to l; also apply C to h when l was n-1.
- S': apply S to l only when h=0.
- E': apply E to l only when h=0.

Under x=hn+l these are exactly the successor modulo n^2, swap of 0 and 1,
and collapse 0 to 1. Thus T_(n^2) is generated. This is strictly beyond
independent coordinatewise operations: the latter have rank rank(f)rank(g);
if singular their rank is at most n(n-1). E' has rank n^2-1, strictly above
that bound. The formulas use only typed, fixed control primitives; this is a
reviewed expansion rule, not discovery of arbitrary new grammar.

The root for the live snapshot reconstructs all six generation receipts using
the #292 verifier, checks the group witness and rank-255 collapse, and can
recheck the prior Lean certificates with --kernel. The group universality
argument uses classical Jordan and transformation-monoid facts, not Lean
proofs of these theorems. The abstract canonical generators at this root
exist by universality, but explicit words in the original Forge alphabet
have not yet been synthesized. Child evaluations use the abstract canonical
gates. The product theorem is elementary but not yet Lean-formalized.

## Reproduction

```sh
python -B -m tools.autonomy.forge_tower --selftest
python -B -m tools.autonomy.forge_tower --output verification/model-a --steps 3
python -B -m tools.autonomy.forge_tower --resume verification/model-a/tower.json --output verification/model-b --steps 4
python -B -m tools.autonomy.forge_tower --root forge --state tests/fixtures/forge_monoid_evolution6.json --semantic tests/fixtures/forge_monoid_semantic4.json --output verification/forge-shadow --steps 3 --kernel
```

Each completed transition writes a chain-hashed row in a fresh shadow output.
Resume re-derives the root and every prior transition; tampered history is
rejected. Proof scopes are recorded explicitly. All three child gate tables
are checked exhaustively through size 65,536; above that, the general divmod
identity argument and boundary probes apply. No enumeration of T_n is
attempted for large n. Default work budget: at most three transitions per
invocation, at most 65 bits for the cardinality of the state space. Hard
limits: 12 total rows, 1,025 bits. Saturation is not inferred from failure
to find a new candidate.

## Verification scope

Local exact closure for 2 x 2: 16 independent maps, 24 permutations under
the two reversible child gates, 256 maps under all three gates. Tests check
parent sizes 2 through 6, identical resumed vs uninterrupted history,
tamper rejection, and budget termination. The controller can represent
2 -> 4 -> 16 -> 256 -> 65536 -> 4294967296 -> 2^64 in the small root model.
This is symbolic expressivity, not a dense truth table or performance claim.

Production integration requires explicit review of the rank-255 admission,
a stable tower ledger schema, a full saturation proof layer (including
the group and product theorems), and a production scheduling decision.
