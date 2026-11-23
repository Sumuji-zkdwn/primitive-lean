# Semantic Bridge: verified new semantics become reusable Generic Forge tools

Semantic Foundry establishes a narrow strict capability gain in the 4-sample
signal domain. Generic Forge already has a growing library of verified
primitive compositions. **Semantic Bridge** makes the two output libraries
usable together in a growing, source-provenanced data-only operator graph.

The existing Generic and Semantic Forge workflows and data are **read-only**
and unchanged. The integration is a trusted adapter with its own independent
ledger and a separate daily GitHub Actions workflow.

## What it actually builds

A hybrid operator is an ordered composition of **typed tokens**:

~~~json
[
  {"kind": "generic", "id": "gf_198afad7a91bc9a2"},
  {"kind": "semantic", "id": "sf_43ed97b6ef1909a1"}
]
~~~

The Generic parent in this example is the actual certified macro
\`add_one;add_one\` modulo four on each of four signal samples.
The Semantic parent is the actual certified extremum-location detector.

For the signal \`[0,3,1,2]\`, the Generic macro returns \`[2,1,3,0]\`.
The Semantic detector then returns \`[0,0,1,0]\`.
This is a genuine **input-dependent** hybrid, not an alias or a
long string that performs only constant output.

Every hybrid is checked on **all 256 finite signals by two separate
execution paths**:
- Generic stage: existing reference and packed Generic Forge interpreters.
- Semantic stage: list-based and bit-packed Semantic Foundry interpreters.

A hybrid must be (a) semantically different from prior verified hybrids,
(b) nontrivial across the four single-peak probe positions, and
(c) contain a constant-input counterexample to the original primitive
closure invariant. This last item certifies that, although the hybrid
uses old Generic components, it remains impossible to express as a
composition of the *six original* signal primitives alone.

## Self-reuse and honest novelty

Verified hybrid receipts can become named parent components
(\`{"kind":"bridge","id":"sb_..."}\`). The generator expands such
references into typed, source-anchored Generic/Semantic tokens, and
constructs new hybrids by adjoining a newly available certified token.

This is **real reuse of newly available semantics inside the old
Generic Forge environment**. It is deliberately an adapter instead
of changing Generic Forge's historical receipt schema or importing
untrusted data as code.

It does NOT establish that each further hybrid extends expressive
power **beyond the new expanded language** containing Semantic
Foundry already. The strong impossibility result compares with the
old six-primitive-only closure; later hybrids are distinct observable
functions inside the enlarged closure.

## Verification and state safety

Source branches:
- \`autonomy/generic-forge-state\` (read-only, independently validated)
- \`autonomy/semantic-capability-state\` (read-only, independently validated)

Writable bridge branch:
- \`autonomy/semantic-bridge-state\`
- \`docs/autonomy/semantic-bridge-state.json\`

The controller:
- \`tools/autonomy/semantic_bridge.py\`
- \`.github/workflows/semantic-bridge.yml\`

Each receipt records ordered source tokens, flattened primitives,
optional verified hybrid parent, exact source commit and both upstream
hash-linked source anchors, exhaustive two-interpreter behavior hash,
constant-input counterexample, 4-position response, evaluator ID,
bounded score, UTC date and the SHA-256 receipt chain.

Every run revalidates both source histories and its own receipt ancestry
from scratch. Unknown operator IDs, redefined upstream semantics,
unverified parent references, duplicates and altered evidence fail closed.
No dynamic Python code, shell scripts, PR code, or arbitrary interpreter
functions are loaded from a state branch.

An unprivileged PR job runs tests and a full hybrid generation /
reconstruction. Once reviewed and merged into main, a main-push and
a daily **13:11 UTC / 22:11 JST** schedule can trigger a single
proof-gated hybrid; one receipt is permitted per UTC day, with at most
32 persisted results in this generation. A separate write-enabled job
reconstructs the **exact same** candidate from trusted main code and
fresh upstream data, re-evaluates all 256 signals independently, and
commits only the one allowlisted JSON file. No auto main merge occurs.

Hosted GitHub scheduling may run late, miss a run or exhaust quota.
A signed cryptographic provenance or proof of system integrity against
a malicious repository maintainer is not claimed.

## Reproduce with actual certified upstreams

~~~bash
python -m unittest discover -s tests -p test_semantic_bridge.py -v

python -m tools.autonomy.semantic_bridge prepare \
  --generic tests/fixtures/semantic_bridge_generic.json \
  --semantic tests/fixtures/semantic_bridge_semantic.json \
  --state tests/fixtures/semantic_bridge_empty.json \
  --day 2026-11-24 --head "$(git rev-parse HEAD)" \
  --output verification/semantic-bridge/candidate

python -m tools.autonomy.semantic_bridge seal \
  --generic tests/fixtures/semantic_bridge_generic.json \
  --semantic tests/fixtures/semantic_bridge_semantic.json \
  --state tests/fixtures/semantic_bridge_empty.json \
  --head "$(git rev-parse HEAD)" \
  --evidence verification/semantic-bridge/candidate \
  --output verification/semantic-bridge/verified.json
~~~

Then choose the operator ID from the verified JSON and execute the
hybrid on a new signal using the \`run\` subcommand.

The goal is a functioning *cross-system* research loop: already
certified artifacts from different systems become source-checked
ingredients for new certified computations, without granting
generated data any executable authority.
