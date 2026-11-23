# Self-directed Finite Discovery — no human or GPT in the operating loop

This is a **running, bounded model-search engine**, not a statement that
all mathematical research can be automated. Once deployed, it operates
on GitHub-hosted Actions without a desktop, paid API, external LLM, or
repeated human input. It does not change executable source or main.

## The change from the 13-item Research Conveyor

Research Conveyor has 13 manually reviewed finite targets and then
stops. Finite Discovery starts with four independently reviewed seed
models and **constructs further hypotheses from the last verified
model and its outcome**. This is a self-generating *finite experiment
queue*, not a natural-language theorem invention system.

The source anchors are the exact byte-pinned research documents and
modules used by the existing reviewed adapters:
- Observer operation words / hidden observation bit;
- Laakso first-level raw-vertex observation and rightward update;
- Siphon E polynomial map reduced explicitly to F3 squared.

The Siphon source Git blob is pinned, as are the observer and Laakso
sources and Laakso's supporting Lean/Python definitions in the existing
reviewed adapter. A source change halts the engine for re-review.
No research document or historical PR text is executed.

## Closed experimental loop

1. The trusted main controller reads the **data-only**, Git-tracked
   ledger in branch autonomy/finite-discovery-state. It verifies its
   schema, reviewed source catalog SHA-256 and every receipt's
   previous-hash chain.
2. For any untested reviewed root, it proposes the next seed. After
   seed experiments it derives further finite machines using a small
   explicit grammar, conditioned on the previous Lean-certified
   distinguishability result:
   - **bisimulation_quotient**: partition-refine a finite machine and
     construct a smaller observational quotient. The Python quotient
     calculation is not misrepresented as a general Lean theorem.
   - **compose_first_action**: add a macro equivalent to two primitive
     actions; test whether shortest named-word length changes.
   - **forget_last_observation**: coarsen a readout; seek new invisible
     pairs.
   - **remove_last_action**: restrict a vocabulary; test observational
     equivalence under fewer available continuations.
   - **split_hidden_readout**: let the observer measure one previously
     invisible component.
   - **append_distinguishing_probe**: add a specific primitive action
     to test whether a formerly equivalent pair can be separated.
   - **duplicate_hidden_sheet**: adjoin an intentionally invisible
     state sheet.
   - **perturb_one_transition**: test robustness to a single edit in
     a deterministic transition table.
   - **change_observer_pair**: compare another pair with identical
     current readout.
   - **adjoin_absorbing_state**: expand the finite state set.
3. It removes duplicate concrete models via SHA-256, applies a
   deterministic **breadth-first, domain-balanced** selection, and
   generates one concrete question about the selected pair.
4. Proof Forge constructs a shortest distinguishing word or a closed
   relation certifying **all finite words are observationally equal**.
   GitHub Actions compiles the exact emitted Lean with the pinned
   toolchain and --trust=0, then audits theorem axioms. No positive
   result is recorded before this check.
5. A separate limited-write job repeats the proof audit, reconstructs
   the exact candidate and Lean bytes, and appends a source-pinned,
   hash-chained JSON receipt. A failed check creates no receipt.
6. A following run reads the prior verified result and proposes a
   different branch: a previous equivalence leads toward refined
   readouts or probes; a previous distinguisher leads toward vocabulary
   changes, compression and robustness testing.

The ledger records the **finite** outcome, shortest word if any,
parent experiment, mutation rule, source/head SHA, proof SHA and
comparison with the parent outcome. A counterexample to a
specific pairwise conjecture is NOT automatically proof or refutation
of the original real or infinite-state research statement.

## Limits and economics

- Maximum 12 enumerated states, 4 deterministic actions and 8
  observation labels, as enforced by Proof Forge.
- At most 96 accepted experiments, depth at most 5 in the current
  mutation grammar. Both are explicit budget caps. Model extension
  is **automatic within this grammar**, but the search space and
  scientific objectives are not infinite.
- One new verified experiment per UTC calendar day; the GitHub
  schedule is **04:17 UTC / 13:17 JST**. GitHub may delay schedules
  due to runner capacity. A push to main starts the first trial,
  subject to the daily idempotency check.
- Only the audited JSON ledger branch is written. The engine has
  **no code-modification step, no autonomous main merge and no
  unreviewed theorem injection**.
- No human or GPT is required **during the bounded run**. To
  extend the class of admissible theories, change the objective or
  accept mathematically meaningful new semantics, a new reviewed
  interpreter/grammar is still required. This is not an AGI or proof
  of mathematical discovery in the open-ended sense.
- The GitHub-hosted Actions workload consumes platform runner
  quota. No external model/API token is used.

## Safety architecture

The pull_request workflow tests grammar, strict ledger checks and
real generated Lean certificates, with no persisted Git credentials.
The main-only job checks out source code from an exact trusted main
commit and reads state as **data**, with read-only permissions. A
separate post-success job with contents:write rechecks the model,
proof source, axiom audit, checkout commit and entire state ledger,
then commits **only** docs/autonomy/finite-discovery-state.json to
autonomy/finite-discovery-state. A concurrent run with a stale state
must fail to push.

Even a wholly deterministic search can get stuck, optimize an
uninteresting metric, or miss an essential hypothesis. These are
scientific limitations, not CI failures; the engine must not label a
successful finite certificate as an unconditionally true physics law.

## Reproduce

On a checkout of the reviewed source:

~~~sh
python -m unittest discover -s tests -p test_finite_discovery.py -v
python -m tools.autonomy.finite_discovery prepare \
  --root . --state tests/fixtures/finite_discovery_empty.json \
  --head "$(git rev-parse HEAD)" --day 2026-11-23 \
  --output /tmp/finite-discovery-cycle
~~~

This emits an **UNVERIFIED** proposed Lean certificate. In CI the
pinned kernel must compile it before receipt accepts the result.

For independent CI inspection, see workflow
.github/workflows/finite-discovery.yml. The smoke generator compiles
seven additional source-reviewed seeds/mutations to ensure the
grammar is represented in real Lean, not merely a Python oracle.

## Long-term technical direction

To approach a genuinely open-ended system, the next stage must add
**checked expansion of the hypothesis language itself**, rather than
only new instances of fixed transition rules. Candidate interpreters
would need a separate sandbox, total resource budget, machine-checkable
semantics, differential tests against independent reference models,
a theorem checker independent of the proposal mechanism, and explicit
versioned controls for changing the scientific objective.

There is no general algorithm that can guarantee it will decide
arbitrary mathematical statements; undecidability prevents that
stronger promise. Finite Discovery removes repeated human/LLM
operation for an inspectable subset while preserving that boundary.
