# Strategy Evolution — bounded research about the research rules

Strategy Evolution is the next independent, proof-gated stage after
Research Conveyor and Finite Discovery. It attempts to **evolve finite
experiment rules**, not just generate new instances from a fixed list.

It requires no ChatGPT/GPT call, external model API, always-running
computer, or manually written task each day. It uses a deterministic
search over a **typed, fixed vocabulary** of finite transformations.
This is NOT general autonomous creation of arbitrary mathematical
theories or a method that can decide every theorem.

## Actual upstream evidence

The input is the proof-verified JSON ledger in the separate branch
autonomy/finite-discovery-state. It is checked using the upstream
verifier and an exact source-catalog hash. The first actual upstream
record includes an observer four-state model with a proven shortest
two-operation separator. The strategy engine also starts from four
source-anchored, reviewed seed models: observer, Laakso raw-vertex
updates, modular Siphon E, and observer hidden-state equivalence.

Untrusted ledger entries are data, not commands. They do not define
imports, dynamic Python functions, Lean tactics, shell commands or
arbitrary source code.

## How it learns new rules

A *strategy* is a JSON list of one to three **typed finite
transformations**. The interpreter knows only the reviewed operations
provided by Finite Discovery:

- bisimulation quotient
- composition of a primitive with itself
- loss of an observation distinction
- restriction of the available action alphabet
- a newly visible hidden readout
- an additional simple separating probe
- duplication of a hidden sheet
- a one-entry transition perturbation
- a change to the state pair being compared
- adding an absorbing state

The engine first tests single-operation strategies against the
source-anchored models. A composite such as
compose_first_action followed by forget_last_observation is allowed
**only if the first rule already has a Lean-verified receipt**. This
is genuinely a new, compositional search rule relative to its
previously tested parent, but the type grammar itself remains fixed.

The policy counts past verified results by final operation and source.
It weighs (a) observed finite difference between original and
mutated model, (b) measured usefulness of already certified rules,
(c) a small bonus for underexplored operations and (d) source balance.

Each candidate receives a bounded Python preview score:
- 12 if the target pair changes distinguishable/indistinguishable
- 6–10 if its minimal named-operation length changes
- 3 if the finite state space size changes
- 2 if only the action vocabulary changes
- 1 for a preserved pairwise result

This score is a **local heuristic**, not a proven measure of
mathematical originality, scientific significance or universality.
The learned score affects the next search order; it cannot authorize
a proof or change the Lean kernel.

## Two independent finite obligations per iteration

The critical distinction from merely ranking Python-generated
candidates is that a candidate has a *baseline model* and a
*derived model*. The same repository-pinned Lean compiler with
--trust=0 must compile both certificates and their theorem/axiom
inventories. Proof Forge either supplies a shortest separating
word with minimality or proves all finite words preserve the readout.

The source/target comparison is computed from these verified finite
models. **No universal theorem about what the mutation does to
every possible machine is claimed.**

If the two Lean artifacts or their input/model SHA-256 hashes fail
to match the deterministic generator, no strategy receipt is
published. Stale upstream data, altered source code, unknown
grammar operations, missing proofs and repeated UTC days also fail
closed. All proof logs survive a failed workflow.

## Data and privilege isolation

The current Finite Discovery branch is always read-only to Strategy
Evolution. New strategy receipts belong to the separate branch
autonomy/strategy-evolution-state at the single path
docs/autonomy/strategy-evolution-state.json.

On a PR, the dedicated workflow runs only offline tests and actual
Lean proof attempts with no stored write credentials.

After a reviewed merge into main, GitHub Actions runs the same
trusted controller daily at **05:23 UTC / 14:23 Japan time** and
on qualifying pushes to main. It reads both state branches as
data, checks the controller SHA, and proves one strategy.

Only a separate, post-success job holds contents:write. It
downloads artifacts, repeats the proof audit, reconstructs the
exact source and generated Lean bytes, reconciles upstream and
strategy-state revisions, and commits **only the verified JSON
receipt** to the strategy branch. A concurrently changed upstream
will cause the proposed plan to be rejected, not silently rebased.

State entries are append-only in normal operation, form a
SHA-256-linked audit sequence, and include the source snapshot,
strategy parent, full typed program, both finite models, shortest
witnesses, recorded kernel identity and bounded score. Hash chaining
detects accidental/unannounced modification on read; it is *not*
a cryptographic signature or access-control substitute.

The workflow performs no main auto-merge, PR opening,
automatic code execution, branch force-push, external paid
inference or arbitrary theorem injection.

## Resource bounds and replication

- Each model: 2–12 finite states, 1–4 deterministic operations and
  at most 8 observation labels, inherited from Proof Forge.
- Program length: at most three approved operations.
- At most 64 verified strategy experiments in this generation.
- At most eight recent upstream verified models plus four pinned
  seeds are selected as live roots.
- Up to 800 candidate strategies are ranked per search step,
  16 previously verified strategies considered for extension.
- At most one new receipt per UTC calendar day, no hidden retries
  that manufacture an extra verified result.
- GitHub Actions capacity and runner quota may affect execution.

Offline testing on the exact source head:

~~~sh
python -m unittest discover -s tests -p test_strategy_evolution.py -v
python -m tools.autonomy.strategy_evolution prepare \
  --root . \
  --upstream tests/fixtures/strategy_evolution_upstream.json \
  --state tests/fixtures/strategy_evolution_empty.json \
  --head "$(git rev-parse HEAD)" \
  --day 2026-11-23 \
  --output /tmp/strategy-test
~~~

This emits two **unverified** Lean files. Only Actions
compilation/audit and the write-isolated receipt job may record a
successful experiment.

## What remains outside this design

This is research into *strategies for generating finite experiments*.
It does not yet create genuinely new mathematical vocabularies,
axiomatizations, semantics for arbitrary code, or interpreters for
the entire literature. Those operations require another explicit
trusted checker and more sophisticated novelty/utility objectives.

There is no general algorithm that decides all mathematical
statements; neither this controller nor a larger LLM can promise
that. Removing humans and GPT from the **routine bounded research
cycle** is practical. Eliminating all human choice of scientific
objectives, security policy and physical validation is a different,
much stronger claim.
