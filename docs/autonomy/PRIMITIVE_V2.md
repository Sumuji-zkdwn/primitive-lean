# Primitive Autonomy V2 — GitHub-native research feedback

This is a **new main-derived implementation** of the original
[primitive-autonomy](README.md). It preserves the three old verification
receipts and original generated source bytes while avoiding the stale,
diverged legacy growth branch. The original workflow
\`.github/workflows/primitive-autonomy.yml\` remains intentionally **paused**.
No old branch is merged or force-updated.

## Objective and exact meaning of autonomy

A GitHub schedule, not ChatGPT, Codex, an LLM inference endpoint, a local
workstation or a human, performs a bounded research cycle:

1. Read an append-only, verified-receipt ledger.
2. Compute a **deterministic policy** from the actual previously certified
   finite outcomes, prioritizing unseen experimental families, outcome kinds,
   shortest separating-word lengths, and state-space sizes.
3. Construct **one new pair** of finite transition systems from the
   original primitive-autonomy operator-separation question.
4. Compute independent Python predictions, generate Lean source from reviewed
   bounded integer data, and compile both sources with **Lean --trust=0**.
5. Audit the exact theorem names, generated source hashes and allowed axioms.
6. In a separate privileged job, recompile both Lean sources from scratch,
   repeat the axiom audit, independently reconstruct the intended models
   and all source hashes, and append a verified JSON receipt **only to
   autonomy/primitive-v2-state**.
7. The next scheduled run reads that new receipt and chooses another problem.

The system **cannot** unilaterally create new axioms, change its trusted
Python grammar, choose a new mathematical theory or prove physical laws.
Verified finite experiments are not evidence of a general theorem without
an additional argument.

## Legacy data: what is carried forward

The old controller \`tools/autonomy/grow.py\` enumerates 84 separating
models of 3–8 states and proved 5 Lean theorems plus defined 3 primitives
per successful cycle. The historical ledger currently has three
kernel-audited cycles in
\`docs/autonomy/ledger.json\`. V2 verifies each referenced Lean source
against its original SHA-256, rejects any unverified legacy row, and
omits the three already examined \`(n, a, b)\` models.

V2 *does not* redo the legacy integration, re-prove the historical 15
theorems or claim their proof history is a new V2 result. Instead it
derives fresh pairs of exact finite-model certificates, both checked by
the current repository-pinned Lean and Mathlib.

The original 84-case generator remains unchanged.

## Typed experiment grammar

All experiments compare an identity-only baseline system against the same
system with one additional deterministic operator. In all cases initial
states 0 and 1 have the same readout.

| Family | Question | Strict model bound |
| --- | --- | --- |
| \`legacy_split\` | Can a new primitive distinguish two old-equivalent states in one step? | 81 not-yet-tried original models (3–8 states) |
| \`delayed_split\` | Can the *shortest* identifying word be greater than one primitive step? | 36 models (5–12 states; exact depth 2 through n−3) |
| \`inert_swap\` | Does adding an actual nonidentity operator sometimes change **nothing** observable? | 6 negative-control models (3–8 states) |

The complete V2 catalog thus consists of **123 finite proposals**, minus
any verified V2 receipts. A candidate is created only once per verified
date. Only this fixed, typed grammar is evaluated; ledger JSON cannot
add arbitrary Python/Lean source, GitHub workflows or executable scripts.

The \`delayed_split\` example starts with an observation-invisible chain
\`0 → 2 → 4 → ... → observed sink\` and a second state \`1 → 3 → 3\`.
It is designed so that \`d\` fresh steps, but not fewer, distinguish
states 0 and 1. The *actual* shortest word is computed by exhaustive
product-automaton BFS, checked by a separate finite sanity routine,
and proved via generated Lean certificates.

The \`inert_swap\` example adds \`0 ↔ 1\` without changing their
observation. The resulting readout equivalence is not a failure: it
is a negative control against overinterpreting "new operation" as
"new distinction".

## Search policy (controlled feedback)

The policy's coverage reward is 10 for an unseen **outcome kind**, 8 for
an unseen **family**, 6 for an unseen **separating depth**, 3 for an
unseen **state count**, and 2 while a family has been used fewer than
twice. Only previously verified V2 rows affect this reward; the
controller's computed predictions are proposals, never stored as
verified data without Lean.

This reward measures diversity of finite tests, **not** novelty in the
mathematical literature, relevance to real physics, or truth of a
conjecture. It is deliberately simple and inspectable. As certified
results accumulate, the research priority changes without an external
agent deciding the next task.

The state is a JSON object with exact versioned fields and a
SHA-256-linked append-only receipt chain. Each entry stores its exact
source head, old seed SHA-256, typed model spec, two request/source hashes,
finite observation, predicted shortest word, bounded policy reward and
status. Receipt history is independently recalculated from the legacy
seed on every run. Hash chaining detects unexpected changes; it is
not an access-control or cryptographic-signature mechanism.

## Execution / trust boundary

- Workflow: \`.github/workflows/primitive-autonomy-v2.yml\`
- Source: \`tools/autonomy/primitive_v2.py\`
- Persistent data-only branch: \`autonomy/primitive-v2-state\`
- State file: \`docs/autonomy/primitive-v2-state.json\`
- Schedule: daily at **07:37 UTC / 16:37 JST**, once the workflow exists
  on the default branch. Runs may be delayed/dropped by GitHub.
- Manual trigger: main-branch \`workflow_dispatch\` is allowed.
- One new verified state per UTC date; no duplicate completed day.
- Two independent Lean proof obligations per iteration.
- CI limits: unprivileged verify job 40 minutes, separate state-write
  replay job 40 minutes.
- PR jobs are read-only and generate only ephemeral proof evidence.
- The privileged job runs trusted main controller code, reads the state
  branch as data only, recompiles the Lean sources itself, and commits
  **only one allowlisted JSON file**. No main mutation or auto-merge.
- Workflow source, branch names and trust policies are never rewritten
  by generated candidates.
- Exhausting all finite hypotheses exits with
  \`FINITE_GRAMMAR_EXHAUSTED\`, without fabricating novelty or restarting.
- A source change, unverified receipt, stale ancestry, altered proof
  artifact, failed kernel/axiom check or changed target branch fails
  closed. Failure reports remain in the run's 30-day artifact.
- GitHub hosted runner quotas and budget limits still apply.

This architecture deliberately separates **untrusted candidate data**,
**unprivileged Lean checks**, and **the state-write privilege**. The
replay requires a second Lean compilation rather than trusting a
downloaded text log as proof.

## Reproduce the integration rehearsal

Run from the repository root:

~~~bash
python tools/autonomy/grow.py self-test
python -m unittest discover -s tests -p test_primitive_v2.py -v

python -B -m tools.autonomy.primitive_v2 prepare \
  --root . \
  --state tests/fixtures/primitive_v2_empty.json \
  --head "$(git rev-parse HEAD)" \
  --day 2026-11-23 \
  --output verification/primitive-v2/replay

# In the repo-pinned lean directory:
cd lean
for f in ../verification/primitive-v2/replay/proof/*.lean; do
  n="$(basename "$f" .lean)"
  lake env lean --trust=0 "$f" > "../verification/primitive-v2/replay/proof/$n.log" 2>&1
  echo "$?" > "../verification/primitive-v2/replay/proof/$n.exit"
done
cd ..
python -B tools/autonomy/proof_forge.py audit \
  --output verification/primitive-v2/replay/proof
python -B -m tools.autonomy.primitive_v2 receipt \
  --root . --state tests/fixtures/primitive_v2_empty.json \
  --head "$(git rev-parse HEAD)" --day 2026-11-23 \
  --evidence verification/primitive-v2/replay \
  --output verification/primitive-v2/replay/verified-next-state.json
~~~

**Do not treat the Python-generated Lean text as a proof** before both
Lean and the axiom audit pass. Never mix the unverified candidate
artifact with the persistent ledger. After PR review, merging the new
workflow into main is the explicit activation step. The old workflow
remains paused, and all original research branches remain unchanged.

## Next research milestones (not claimed complete)

- Expand the typed grammar by reviewed, kernel-checkable operators from
  Strategy Evolution, with a clear adaptation and source-provenance contract.
- Add independent meta-evaluation for description length, new distinctions,
  and negative controls rather than mere theorem totals.
- Route proof-verified discoveries to an automatically prepared *draft*
  PR only after safe write isolation and clear human/organizational policy.
- Establish external empirical validation separately from Lean truth.
