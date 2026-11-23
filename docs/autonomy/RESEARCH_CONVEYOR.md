# Research Conveyor — finite proof tasks and feedback from retained research

Research Conveyor connects **existing research notes**, the existing
**Research Scout** lead index (for the original Siphon route), reviewed
source-anchored finite adapters, and the **Proof Forge** Lean certificate
generator. It now rotates three bounded research domains: Siphon E,
operator-word observability and Laakso raw-vertex projections. It runs **without a paid AI API call** or a
desktop computer. A previously kernel-verified finite outcome determines
the next task. Nothing is automatically merged into main.

This is intentionally a **bounded prototype**, not a general agent that
understands arbitrary mathematical prose or invents a model without
assumptions. It uses three individually reviewed, source-bound adapters,
and reports when a lead has no safe finite interpretation. The first
real Siphon result in the existing persistent state remains unchanged.

## Actual source and exact finite interpretation

Source: [docs/research/2026-11-17-siphon-predictive-quotient.md](../research/2026-11-17-siphon-predictive-quotient.md).

The mathematical source specifies the polynomial automorphism E on
real pairs (u,v), the quantity r=v+u³, readout K(u,v)=u, and the
fresh operation R(u,v)=(u,v+1). The source's historically marked
"未検証" sentence concerns the then-pending CI state of a larger
Lean theorem; that sentence must **not** be treated as proof that the
original real theorem remains unproved today. Here it serves solely as
a discoverable Research Scout lead.

The reviewed finite adapter takes these **integer-coefficient** formulas
modulo 3. Its state space is F3 × F3 (9 states), with the readout u:

- r = v + u³ (mod 3)
- E(u,v) = (u+r², r-(u+r²)³) (mod 3)
- R(u,v) = (u,v+1) (mod 3)

For each u=0,1,2, the initial pair has the same u and hidden
invariants r=1 and r=2, respectively. The next candidate is determined
by the *previous successfully audited result*:

1. Test the old E-only operator vocabulary. If the two states are
   observationally indistinguishable under every finite word,
   test that same pair with both E and R.
2. If the old model already distinguishes the states, record this
   finite counterexample and proceed to the next u without asserting
   an unwarranted "new operation required" premise.
3. Continue to the next u, until all three finite seeds are handled.
   There are at most **six** total finite proofs in this Siphon family.
Four operator-word examples and three Laakso raw-state examples extend
the combined limit to **13**. One verified finite result per UTC day is
selected across the three families by lowest completed-count (stable
tie order Siphon, operator words, Laakso). A prior result controls
whether a dependent example is attempted.

In the reviewed F3 model, the old E-only case is expected to be
**EQUIVALENT**, and the extended model is expected to have a shortest
separating word [R,E]. The actual proof result, **not the expectation**,
is what gets persisted. This is an exact finite arithmetic analogue
of the real-valued observation issue, **not** a direct proof of the
real/continuous source claim.

Other unresolved research leads remain **unmapped** until a separate
reviewed mathematical adapter is supplied. The newly included
operator-word and Laakso notes are cited as reviewed finite
**source anchors**; the notes are NOT claimed to be newly unsolved
theorems merely because they appear in the repository. This avoids converting
natural-language speculation into unsound formal statements.

## The fully automated bounded path

1. On each daily scheduled run (02:43 UTC / 11:43 JST), a trusted
   main-branch controller checks out the separate
   autonomy/research-conveyor-state branch **as data**.
2. It calls existing research_scout.collect to locate the actual source
   lead and validate source bytes, then selects **one** finite candidate
   based on the prior ledger's Lean-verified outcome.
3. It materializes a bounded JSON request that passes Proof Forge's
   strict integer schema (9 states, 1–2 total operators, one pair).
4. GitHub-hosted Actions runs the **pinned Lean / Mathlib toolchain**,
   compiles the emitted Lean with --trust=0, and audits every theorem's
   dependencies. Every attempt retains logs and provenance as a
   short-lived Actions artifact, including failures.
5. A **different job** holds contents:write, re-audits the artifact,
   validates original source SHA, candidate model, exact controller
   SHA and prior state, and commits **only a JSON receipt** to the
   isolated state branch. It cannot merge or update main. Failure
   stops the feedback transition.
6. On the next run, a previously Lean-certified result selects a new
   task, fairly rotating the three research domains. A completed UTC
   date is never processed twice. Once the finite family is exhausted,
   the job reports FINITE_ROUTES_EXHAUSTED_NEED_REVIEWED_ADAPTER and
   does not fabricate new theorems or spend Lean minutes on an empty queue.

On PRs, the same workflow does offline Python regression tests and
**actual pinned Lean tests of a migrated next-task certificate plus six
observer/Laakso smoke certificates**. A one-step receipt is created in
an ephemeral test artifact and is never written to persistent state. It is
not permitted to run the privileged live cycle on untrusted PR code.

The isolated branch must exist and contain exactly:

~~~json
{
  "schema_version": 1,
  "last_utc_day": null,
  "results": [],
  "last_source_sha": null
}
~~~

at docs/autonomy/conveyor-state.json. It must never be used as an
executable-code checkout by the workflow.

## Reproduction locally

~~~sh
python -m unittest discover -s tests -p test_research_conveyor.py -v
python -B -m tools.autonomy.research_conveyor prepare \
  --root . --state tests/fixtures/research_conveyor_empty.json \
  --head "$(git rev-parse HEAD)" --day 2026-11-23 \
  --output /tmp/research-cycle
~~~

This offline run proposes a finite candidate and emits a generated
Lean file, but **does not prove it**. Actual claims require
pinned Lean compilation and a complete axiom audit. The subsequent
receipt command rejects any unverified candidate.

Once merged into main, the workflow's main-push event runs its first
automatic source-pinned finite verification. An Actions workflow
schedule may run a little later than its nominal minute. GitHub-hosted
Actions usage is subject to the repository's available runner quota.

## Limits and guarantees

- Full, unconstrained natural-language-to-Lean proof generation:
  **not implemented**.
- Source-bearing research notes: untrusted **data** only; no shell
  snippets or generated model text are executed.
- Other mathematical theories: **not automatically reduced** without
  an explicit reviewed adapter.
- Finite proof vs physical theory: kept separate.
- Maximum reviewed state space: 9 states (Siphon); 8 (Laakso/observer).
  Up to 13 finite tasks overall (6 Siphon, 4 observer, 3 Laakso),
  one new receipt per UTC calendar day.
- No external API calls, external AI inference expenses, auto-merges,
  arbitrary branch writes, or changes to the original Lean theorems.
- Fail closed on a source-semantic change, malformed state, failed
  Lean proof, unapproved axiom, altered artifact, stale source SHA,
  or concurrent state update.

This finishes a **limited, auditable research-to-proof feedback loop**.
It is a foundation for additional reviewed finite adapters, not a
claim that arbitrary open problems now solve themselves.

## Expanded source-bound adapter families (2026-11-23)

The runnable routes, exact state encodings and limits are documented in
[RESEARCH_CONVEYOR_ROUTES.md](RESEARCH_CONVEYOR_ROUTES.md). Each route
has a separate research note and expected finite outcomes:

| Route | Exact finite question | Conditional next step |
| --- | --- | --- |
| Siphon E, F3² | Is the hidden invariant's sign visible under E alone? | If all finite words agree, add R and test the shortest word |
| Operator orientation, 4/8 states | Does compiling two primitive actions into one named macro reduce depth without changing predictive equivalence? | Check macro only after a verified primitive witness; then vary the readout of hidden state |
| Laakso first-level RawVertex, 8 states | Are two sheet copies observationally identical under inert updates, and can the original raw rightward update distinguish them? | Only after a verified invisible pair, enable the real first-level raw advance |

The Laakso primitive step is the finite `advanceRightGeneral base`
on the **eight actual raw vertices**, observed by `rawProjection`.
An additional identity action is explicitly stipulated. It does not
claim a global deterministic update on the projected six-vertex
quotient, an inverse-limit flow, or a continuous-time dynamical system.

The observer route checks existing pinned example data in
`proof_forge/requests/orientation_*.json`, then derives only strictly
declared readout refinements or macro compositions; it does not
claim absolute physical time from shortest named-word length.

### Migration of the existing state

No schema reset or historical receipt rewrite is needed. The same
`autonomy/research-conveyor-state` JSON file is read with an
extended allowlist of known finite task IDs. The persisted
`siphon_z3_u0_old` record continues to count toward scheduling.
After it, the first new route is the four-state operator-word
primitive case, followed by the Laakso raw-state case, before returning
to the next Siphon seed. The first exact-head CI replay uses
`tests/fixtures/research_conveyor_one_verified.json`, a copy of the
real initial receipt.

State messages from untrusted research files are never executed.
Finite certificates use the reviewed deterministic generator and their
source bytes are checked again in the separately privileged receipt
job. New source text, altered fixtures, missing source files, or an
unverified proof leave the state unchanged.
