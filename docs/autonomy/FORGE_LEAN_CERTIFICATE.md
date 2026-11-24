# Forge → Lean: certified semantic receipts as operator-word theorems

This is the first bounded integration of the actual Semantic Foundry data ledger
with the existing `LinearInputOperatorWords` theory. It does not change the
original theorem declarations, generator grammar, production ledgers or main.

## Exact mathematical contract

Signals are `Fin 256`, packed four base-four samples. Constant signals are
exactly 0, 85, 170, 255. The six old primitive maps preserve that set.
Their tables are reconstructed from both existing Python interpreters over all
256 inputs. Lean checks the 24 constant cases, then proves closure for
**arbitrary finite words** by induction. For a verified semantic receipt, the
entire 256-entry table is reconstructed using both semantic evaluators, and its
behavior digest must match the actual validated receipt.

For each such table T, Lean checks its concrete witness and proves T differs
from every old word. Moreover, for *any* named macro dictionary whose entries
are old words and *any* word of these macro names, T differs from its action.
The last theorem uses the original project's `run_generated` theorem directly:
the macro word expands to a single old word. This is not a bounded-length
search or a new copied definition of word execution.

## Reproducibility and lifecycle

PR CI uses the actual retained receipt sf_43ed97b6ef1909a1 from
`tests/fixtures/semantic_bridge_semantic.json` (2026-11-23). It replays the entire
chain, rejects a tampered copy, generates twice and compares exact output.
There are four general theorems plus four per certified receipt (eight for the
initial one). All new proofs must pass `--trust=0` and the standard axiom
allowlist. The report records receipt IDs, input/output witnesses, exact source
and ledger hashes; it is explicitly pending until the kernel and audit pass.

After review and merge, a separate main-only daily workflow (14:31 UTC)
reads the live Semantic Foundry ledger, up to its existing 24-receipt bound.
It emits a reproducible Lean source, exact JSON snapshot and verification
report as artifacts, with read-only repository permission and no generated
source or ledger pushed to any branch. No inference API or external secrets.
GitHub schedule delivery remains best effort.

## Boundary

The new Lean module is assembled from the existing unchanged
`OperatorWordObservations.inc` and generated numeral-only tables; it is not
yet registered in the full MainResult integration. Lean proves statements
about the exported finite maps; agreement with the two Python evaluators is
checked outside Lean, not itself formalized as a Lean interpreter-equivalence
theorem. Only Semantic Foundry receipts and the old signal4 alphabet are
covered; this is not a proof of novelty relative to the already enlarged
alphabet, and does not yet feed Lean theorems back into Forge's search.
A natural next step is to consume these certified invariants when proposing
and rejecting candidate operations, or export Semantic Bridge receipts.
