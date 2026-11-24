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
and rejecting candidate operations, or export Semantic Bridge receipts. The second stage below implements the
first of those feedback experiments, without production promotion.

## Second stage: proof-guided expansion beyond the enlarged language

The first version's comparison alphabet was only the six original signal4
primitives. That criterion cannot tell whether a subsequent semantic receipt
is new relative to previously admitted semantics. The second stage replaces
that limitation with a stronger, snapshot-specific invariant.

All current Semantic Foundry recipes contain exactly one four-location pulse
selector. Its image has at most four elements; adding deterministic maps
before or after it cannot increase that image bound. The existing six
primitive maps preserve constant inputs. For the six primitives and every
replayed semantic receipt, Lean proves the disjunctive property
"preserves all constant signals OR has image contained in four outputs."
This property is closed under composition, so it holds for every word,
including arbitrary-length words and arbitrary dictionaries of such macros.
The Lean proof explicitly reuses the existing word execution theory.

The workflow first verifies that theorem against the exact current snapshot
and audits its axioms. Only then does the search run. A pending or mismatched
proof report is rejected. The fixed reviewed grammar has 28 extremum-based
recipes: four rotations, twelve masks and twelve edits retaining the other
three samples. The search first tests constant inputs, then searches for five
distinct output witnesses. A failing test only means "not separated by this
invariant"; it is **not** proof of old-language expressibility. Survivors
undergo independent exhaustive replay on all 256 inputs. The maximum image
rank determines selection, with deterministic tie breaking.

The expected regression is four constant-test exclusions, twelve rank-test
exclusions, twelve surviving candidates. The selected candidate overwrites
the first maximum sample with 3, retaining the other three samples. Its
finite image has 175 distinct outputs in the independent Python computation,
and a constant input is sent to a nonconstant output. Lean separately checks
one constant witness and five distinct output witnesses and derives the
arbitrary-word nonexpressibility theorem, including named macro dictionaries.
The exact image count of 175 is a finite computation, not a kernel theorem.
The discovery report is sealed only after a second kernel/axiom check.

This is a proof-first **read-only** loop: the theorem guides actual candidate
selection and the selected candidate is checked again. Both reports and
exact source files are retained. The candidate is not installed into
Semantic Foundry or used as a production parent; the third stage below
admits it into the proof artifact's expanded word alphabet. The new grammar is reviewed
source, not invented code; no new state-write privileges, no automatic
merge and no unbounded language expansion. Future feedback rounds must
derive a new invariant relative to the enlarged alphabet before promoting
the candidate, rather than pretending this rank-four theorem survives.

## Third stage: reentry and a reversible strict extension

The second stage's exact audited selected map (rank 175, overwrite first
maximum with 3) is replayed, hash-matched and made a real letter in
`promotedStep`, alongside the six original primitives and every actual
Semantic Foundry receipt from the snapshot. `promoted_reentry` states its
one-letter execution equals the discovered map. A prior pending or
hash-mismatched certificate cannot enter this stage.

The old rank-four invariant is now false. Replace it by the weaker but
still separating invariant:

    preserves all constant signals OR is not injective.

For endomorphisms of a finite set, a composite of two injective maps is
injective, and injectivity of a composite implies injectivity of both
factors (finite injectivity implies surjectivity). Consequently the
disjunction is closed under composition. The six original maps preserve
constants; all admitted semantic receipts and the rank-175 map have
explicit checked collisions. The new Lean theorem covers arbitrary-length
words in this **expanded** alphabet and arbitrary macro dictionaries.

After checking that theorem, enumerate a fixed grammar of 48 controlled
XOR maps. Each changes a selected two-bit sample by XOR with 1, 2 or 3
depending on a predicate on the three other samples. All are involutions.
Four predicate types are all equal, not all equal, first pair equal, and
even sum. Independent full-domain evaluators must agree. The expected
regression is 12 constant-preserving candidates and 36 separating
candidates; select maximum changed-input count with deterministic tie
break. The selected map toggles the low bit of sample zero when the other
three samples have even sum: 128 changed inputs, 256 distinct outputs.
Lean checks its involution property on all 256 inputs, derives injectivity,
checks a constant counterexample, and proves nonexpressibility in the
promoted alphabet and its arbitrary compiled macros.

The promotion is local to the proof artifact. The earlier and new
certificate sources, ledger snapshot and mappings are retained; no
production ledger or source branch is written by the workflow. New
exact-head CI must pass before the third-stage assertions are described
as kernel-verified. The grammar is reviewed, not automatically invented.
This is a second bounded iteration with true alphabet reentry, not an
unbounded autonomous proof search. A further iteration must find another
invariant: the current one is broken by the reversible discovery.
