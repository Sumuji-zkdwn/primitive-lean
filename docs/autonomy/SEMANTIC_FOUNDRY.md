# Semantic Foundry — testable expressive growth beyond primitive combinations

## Why it is different

Generic Forge / Meta Forge construct longer compositions of six original
operations per environment. Novel strings, distinct output tables and
multi-generation ancestry do NOT prove new expressive power: every stored
expression can be flattened into the original operations.

**Semantic Foundry** tests a stronger claim: can an automatically
parameterized new operator be shown **not to equal any finite composition
of the old primitives, of any length**?

For the finite four-sample signal environment, the answer is yes, with a
very specific and independently checkable scope.

## A simple old-closure invariant

The original six signal4 primitives are:

- reverse four samples;
- rotate the samples;
- add one modulo four to every sample;
- adjacent XOR;
- clip values by a uniform threshold;
- swap neighboring sample pairs.

Define property **C** for a function F: if the input signal has
four equal components, the output also has four equal components.

For each primitive, property C is verified on all **four** possible
constant signals by **two separate implementations** of the original
environment (six operations × four constants = 24 independent
comparisons). This exhausts all possible constant-valued input
signals in the 2-bit four-sample environment.

**Closure argument:** if F and G satisfy C, then their composition
G∘F satisfies C. This is immediate: F sends constant inputs to
constant outputs, so G preserves the property again. By induction,
**every arbitrarily long composition** of the original six primitives
satisfies C. This is a mathematical implication about these finite
functions, not merely a bounded-depth comparison.

## Generated new semantic construction

The interpreter is extended with one reviewed, strongly typed
semantic *schema*, not a hard-coded list of resulting functions:

~~~json
[{"kind": "peak", "order": "max", "tie": "first", "level": 1}]
~~~

It finds the maximal sample value, chooses the first location
attaining it, and emits a one-hot pulse of level 1 at that position.
The other parameters can generate minimum/maximum selection,
first/last ties and pulse levels 1–3.

Example input and output:

~~~text
input       [0, 3, 1, 2]
generated   [0, 1, 0, 0]
~~~

On the *constant zero signal*, the same example produces
\`[1,0,0,0]\`. This violates property C; hence **no finite
composition of the original six primitives**, regardless of length,
can have this behavior. No attempt to enumerate all words is needed.

The generator also requires the outputs of four single-peak inputs
to differ pairwise. This excludes a trivial fixed-index constant
stamp: the chosen position must depend on the actual signal.

Each generated function is run on **all 256 inputs**, through two
independent implementations: a readable list reduction and a packed
bit-index reduction. Behavior fingerprint, constant witness,
four-basis outputs and diversity/coverage measures are stored.

This is a proof of a **strict expressive extension of the original
signal4 primitive-composition language**, conditional on the
explicit and exhaustively checked finite interpreter semantics.
It is NOT a physical discovery, an unconditional theorem about
arbitrary signals, or a Lean kernel proof.

## New verified semantics can be reused

Previously accepted semantic expressions become generator parents.
The first cycle selects a valid parameterized extremum operation;
later cycles can prepend or append a *reviewed original primitive*
to an earlier verified semantic operator. Only behaviorally distinct
outputs, still violating the original closure invariant and still
responsive to all four peak locations, can be accepted.

The generator may reuse and combine **its newly verified semantic
operators**, but the trusted semantic grammar and interpreter code
remain fixed. This feature does not let the process install arbitrary
Python, create new axioms, modify CI files or rewrite the objective.

Receipts contain the exact typed recipe, optional verified parent,
full-domain behavior SHA-256, input-dependent counterexample,
4-position response certificate, old-closure base-invariant digest,
source commit SHA, verifier identity, UTC day and a linked SHA-256
history. The entire recorded ancestry is rechecked at each run.

## Trust and lifecycle

- Python: \`tools/autonomy/semantic_forge.py\`
- PR and main workflow: \`.github/workflows/semantic-forge.yml\`
- Persistent data-only branch:
  \`autonomy/semantic-capability-state\`
- Exact saved JSON:
  \`docs/autonomy/semantic-capability-state.json\`
- Daily schedule: **12:07 UTC / 21:07 JST**; manual launch allowed
- One verified result per UTC day; 24-receipt maintenance bound
- Up to 120 typed candidate expressions examined per step
- Generated operator language: one extremum selector with at most
  four preceding/succeeding old primitive operations
- Trusted main code generates each candidate; its full behavior is
  audited by independent implementations on every finite input
- PR CI: unprivileged, exhaustive regression and candidate use;
  no automatic data writes
- Main: read-only proposal job + a *separate* state-write job that
  reconstructs the exact candidate from trusted code, compares
  bytes, independently reruns the full audit, and commits only
  one certified JSON receipt to the isolated branch
- No external AI inference, arbitrary generated source execution,
  main-branch rewrites, auto-merge, or external physical assertions

GitHub Actions schedules may be delayed, dropped, or quota-limited.
The previous high-frequency test was bounded to five receipts and
completed; this new workflow uses a low-volume daily cadence.

## Reproduce the finite distinction

~~~bash
python -m unittest discover -s tests -p test_semantic_forge.py -v
python -B -m tools.autonomy.semantic_forge prepare \
  --state tests/fixtures/semantic_forge_empty.json \
  --day 2026-11-24 --head "$(git rev-parse HEAD)" \
  --output verification/semantic-forge/candidate
python -B -m tools.autonomy.semantic_forge receipt \
  --state tests/fixtures/semantic_forge_empty.json \
  --head "$(git rev-parse HEAD)" \
  --evidence verification/semantic-forge/candidate \
  --output verification/semantic-forge/verified-state.json
~~~

Once the full-domain audit has sealed a record, its operator can be
run directly:

~~~bash
python -B -m tools.autonomy.semantic_forge run \
  --state verification/semantic-forge/verified-state.json \
  --operator-id sf_ACTUAL_VERIFIED_ID \
  --signal-json '[0,3,1,2]'
~~~

Use the actual ID from the state. This returns both the output and
the complete verified recipe, without executing generated code.

## Scientific limits and next frontier

This is a **narrow genuine separation**, not a demonstration that an
autonomous machine can invent any desired semantics. The reviewed
extremum-construction schema is still human-authored. Moreover, after
the first new function is admitted, subsequent *different* functions
do not automatically imply ever-increasing expressive power relative
to the enlarged language. Exact extension must be proved against
the relevant prior closure at each stage.

A future Semantic Foundry could suggest new typed **semantic schemas**
rather than just new parameters, but this requires a verifier for
type-preservation, resource/safety bounds, semantic equivalence and
nontriviality that remains separate from the candidate generator.
