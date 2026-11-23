# Definition Foundry — finite new observational definitions and criteria

**Status:** Independently scheduled, proof-gated prototype. It is not a general
automatic creator of new physical laws or arbitrary mathematical foundations.

## Why this exists

Research Conveyor: reviewed finite tasks. Finite Discovery: new model
instances using a fixed transformation grammar. Strategy Evolution:
new *compositions* of reviewed transformation rules.

Definition Foundry addresses the next boundary by generating candidate
**observation functions** and **evaluation objectives** as explicitly
typed, machine-readable mathematical definitions. It explores their
consequences against actually verified finite models. The running cycle
requires no GPT or human prompt, but the underlying definition language
and scientific objectives still have reviewed finite bounds.

## Input and trust boundary

It reads the source-reviewed models and two independent verified-only
ledgers:
- autonomy/finite-discovery-state
- autonomy/strategy-evolution-state

Both ledgers are validated by their existing fail-closed verification
logic. Definition Foundry checks their exact JSON snapshot SHA-256
again before accepting results; if either upstream ledger changes while
Lean is running, the publisher rejects the stale plan. Historical
receipts are never overwritten.

Four pinned original seed models are also available, with actual
sources for observer words, the first-level Laakso raw vertices,
mod-3 Siphon E, and the hidden observer model. A verified definition
can become a new model seed for later definitions, with a checked
parent identifier in the append-only ledger.

No stored JSON may supply an executable Python, JavaScript, shell or
Lean program. Only the reviewed interpreter and deterministic Lean
renderer are executed.

## The typed language of candidate definitions

Every expression denotes a **total function**
K_new : Fin n -> FiniteObservation for a specific finite deterministic
machine. Integer-valued output is checked to be in 0..7.

A small, versioned type system contains:

| Expression constructor | Type and meaning |
| --- | --- |
| read | color: existing readout K(s) |
| after(a,e) | same type as e: evaluate e after one specified primitive a |
| bit(e,label) | flag: 1 if e(s)=label, else 0 |
| eq(e,f) | flag: 1 if the two outputs agree |
| xor(p,q) | flag: Boolean exclusive-or |
| pair(p,q) | color: p+2q for two Boolean flags |

Expressions have depth at most 4, at most 9 AST nodes, and use only
actual operations from the source model. No external dynamic imports
or invented semantics. Nested after operators allow 2-step
lookahead *as a stipulated mathematical observable*: it is **not**
a demonstrated realizable measurement of the physical future.

The controller constructs different candidate readouts automatically,
normalizes each complete finite observation table, and gives the
resulting machine a content-addressed identifier.

## The typed language of evaluation criteria

The engine also chooses the test criterion as **data**, not a
preselected English request. Approved criteria include a change in:

- distinguishability of the designated pair
- number of distinguishable state pairs across the entire machine
- minimal number of named operations needed to separate the pair
- number of distinct current-readout colors

Each criterion may request an increase, decrease or flip, according to
its declared type. Scores are exact, bounded finite Python functions,
not a theorem of scientific importance. Partition refinement is
independently cross-checked by product-system BFS over every unordered
state pair before a successful receipt is published.

Scores do not license a universal claim that one observational
definition is objectively better. Unusual or more numerous output
labels can win some local criteria without being practical sensors.
Future scoring and physical realization remain research problems.

## Three different Lean verification obligations

Every accepted proposed definition must survive **three separate
kernel-checked obligations**, all at the exact immutable source SHA:

1. Proof Forge compiles the *baseline* finite observer model. It proves
   the shortest separating word and its minimality, or observational
   equivalence under all finite words.
2. Proof Forge compiles the *derived* model, with the same state
   transitions and pair but the newly defined observable.
3. An independently generated Lean semantic theorem checks, for
   **every state in the finite model**, that evaluating the candidate
   expression agrees with the asserted full observation table.
   This uses finite case analysis and Lean's kernel checked proof
   terms; its axiom report is inspected separately.

An accepted result is only a mathematical statement about that
**explicit finite observer machine**. It does not establish an
infinite-system or continuous physical law. The Python-based utility
criterion is labelled a finite heuristic; the definition's table
semantics and the selected pair's behavior are what Lean verifies.

## Example (no prediction of physical time)

On the reviewed four-state primitive observer model, K=[0,0,0,1],
operation f=[0,2,3,3], initial pair (0,1), the original shortest
separating word is [f,f]. The candidate observation

  K_new(s) = K(f(f(s)))

has the exact table [0,1,1,1], so the same initial pair becomes
distinguishable at the empty word. The Lean semantic theorem proves
the equality between this expression and all four table entries,
and Proof Forge separately proves the old and new shortest words.

This does not make K(f(f(s))) an available measurement in a physical
laboratory. It establishes a finite, formally certified *conditional
observer design*.

## Deployment and guardrails

Scheduled once daily at **06:17 UTC / 15:17 Japan time**, after the
Finite Discovery and Strategy Evolution runs. The schedule may be
delayed by GitHub-hosted Actions capacity. At most **40 successful
definition receipts** and **one new proof per UTC calendar day**.
Several read-only proof attempts may fail without advancing state.

The three verification jobs run with no write credentials. Only a
separate, post-success publisher checks the actual compiled Lean
logs/axioms, reconstructs source bytes, independently rechecks
all state pairs, and appends **one JSON receipt** to the isolated
autonomy/definition-foundry-state branch. No main auto-merge,
PR source writing, automatic program rewriting or external paid
model API is involved.

Daily operation does not need a laptop, human or GPT. Expanding the
grammar beyond this trusted version or changing the mathematical
meaning of new primitive operators still requires independent review
and a source-compatible checker.

## Reproduction

From the repository root:

~~~sh
python -m unittest discover -s tests -p test_definition_foundry.py -v
python -B -m tools.autonomy.definition_foundry prepare \
  --root . \
  --finite tests/fixtures/definition_foundry_finite.json \
  --strategy tests/fixtures/definition_foundry_strategy.json \
  --state tests/fixtures/definition_foundry_empty.json \
  --head "$(git rev-parse HEAD)" --day 2026-11-23 \
  --output /tmp/definition-foundry
~~~

These commands create **unverified** proof obligations. The
repository's workflow .github/workflows/definition-foundry.yml
runs real pinned Lean --trust=0 compilation and axiom audits before
it creates any persistent result. The smoke suite validates five
additional typed expressions, including readout lookahead, equality,
Boolean combinations and finite Laakso updates.
