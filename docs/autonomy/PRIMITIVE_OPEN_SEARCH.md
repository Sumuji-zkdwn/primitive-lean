# Primitive Open Search: from a fixed candidate set to a verified model graph

The first primitive-autonomy had 84 hard-coded finite witnesses. Primitive V2
used a fixed catalog of 123 candidates. **Primitive Open Search** changes
what is selected: it generates parameterized mutations of previously
Lean-certified finite models, so each successful cycle supplies possible new
parents and new experiments for subsequent cycles.

It remains **a bounded, finite, typed synthesis engine**, not an unrestricted
mathematical research agent. It does not invent arbitrary semantics, axioms,
physics, or executable code. It does not use ChatGPT, Codex or a paid LLM API.

## Scientific object

A model is a finite deterministic transition system with:
- 2–12 states;
- 1–4 named actions;
- at most 8 observation labels;
- an ordered pair of initially compared states.

For each parent model, the synthesis engine searches six parameterized rules:

| Rule | Generated hypotheses |
|---|---|
| redirect_edge | Change any selected action/state transition to any target state |
| change_readout | Change one observation label |
| add_single_probe | Add a new action which maps one state to a chosen destination |
| compose_actions | Append a named action formed from two old actions |
| choose_pair | Compare a different pair of states |
| append_state | Add one absorbing state and compare it against an existing state |

Every action is a typed, reviewed **interpreter branch**. Data branch contents
cannot execute shell, Python, Lean tactics or a new mutation handler.

These operators can be **composed across successive verified cycles**:
a newly certified child becomes a potential parent and can be modified again.
Unlike V2, the controller does not enumerate a fixed list of complete
experimental models. Candidate sets are computed fresh from the actual
verified graph on every invocation.

## Verified parent and feedback contracts

The initial parent comes from an actual Lean-verified V2 receipt on
\`autonomy/primitive-v2-state\`, reconstructed by V2's own deterministic
generator and verified against V2's append-only SHA chain. Additional parents
come from prior verified Primitive Open Search receipts.

The currently available last four V2 records and last six open-search
receipts supply up to 10 distinct parent models. For each iteration, at most
1,800 proposed single-edit transitions are evaluated, interleaving parent
lines to avoid exhaustive enumeration of only one model. A proposed model
must have a different finite fingerprint and must not duplicate a previously
certified model in the available receipt ledger.

The controller rewards:
- a distinguishability flip;
- a changed shortest separating-word length;
- state or action growth;
- previously untested rule, result, shortest depth and state count.

These are explicit **heuristics about finite certificates**, not automatic
proofs of originality, general mathematical laws, or physical explanation.
The reward changes after every new verified receipt. A new parent may
introduce models that were not even possible in the preceding cycle.

The controller records each typed mutation, exact source parent identifier,
old and new finite models, shortest words, outcomes, novelty score, and
SHA-256 source hashes. Each accepted entry is linked to its predecessor.
Earlier V2 history can be validated after upstream V2 appends new receipts by
reconstructing the exact prior V2 chain prefix. Unreviewed or altered upstream
receipts cause the run to stop, rather than silently accept them.

## Proof gate and execution

1. GitHub Actions uses trusted main code to read both state branches **as data**.
2. Candidate generation uses only verified history and current typed rules.
3. Existing Proof Forge computes a finite answer and emits Lean proof source
   for **both** the parent and mutated model.
4. The pinned Lean/Mathlib toolchain compiles at \`--trust=0\` and runs the
   theorem-axiom audit. Results and logs are retained even on failure.
5. A separate write-enabled job checks out trusted main code and current
   state, regenerates the candidate source, compares it byte-for-byte with
   first-stage output, re-runs Lean and axiom checks, and validates the
   deterministic next receipt.
6. Only on complete success does it commit **one JSON receipt** to
   \`autonomy/primitive-open-state\`, never executable code or main.

Both unknown transition rules and unverified feedback fail closed.
No untrusted pull request code gains write permission. No automatic PR merge.

## Scheduling and resource controls

- Workflow: \`.github/workflows/primitive-open-search.yml\`
- Controller: \`tools/autonomy/primitive_open.py\`
- State: \`autonomy/primitive-open-state/docs/autonomy/primitive-open-state.json\`
- First trigger on merge: a trusted main \`push\`
- Daily trigger: 08:13 UTC / **17:13 JST**, after V2's nominal 07:37 UTC
- One new receipt at most per UTC day
- At most 1,800 model mutations evaluated per run
- At most 256 verified receipts in this generation (maintenance ceiling)
- Two Lean compilation jobs, each maximum 40 minutes
- No external AI inference cost; GitHub-hosted runner quota still applies
- No unlimited retries; if no new candidate is found, report
  \`BOUNDED_FRONTIER_NO_NEW_MODEL\` instead of inventing progress

GitHub's schedule can be late, missed or quota-limited; this is not an
always-on process.

## Actual guarantee boundary

The **fixed list of whole experimental candidates is eliminated**.
The set of possible models now depends on previously verified models and
parameterized transformations; repeated application grows a research graph.

The **operator vocabulary is still reviewed and finite**. The compiler also
currently caps state count, action count and observation symbols. There is no
theorem that all new model classes, all experimental hypotheses or all
mathematical semantics can be generated in this way. This is a step toward
open-ended synthesis, not completed unrestricted autonomy.

To go further, a next generation should create candidate transformations
as typed symbolic programs and automatically *prove their semantic safety*
before the interpreter admits them, separate from the question whether their
finite experiments are scientifically useful.

## Reproduce a one-step research cycle

~~~bash
python -m unittest discover -s tests -p test_primitive_open.py -v
python -B -m tools.autonomy.primitive_open prepare \
  --root . \
  --upstream tests/fixtures/primitive_open_v2_seed.json \
  --state tests/fixtures/primitive_open_empty.json \
  --head "$(git rev-parse HEAD)" --day 2026-11-24 \
  --output verification/primitive-open/replay
~~~

This generates two **unverified** Lean candidates. The workflow runs the
Lean kernel and audits its axioms before it records any result.

The first implementation remains in a draft PR pending exact-head CI.
The existing V2 workflow and main source are not modified by the draft.
