# Meta Forge — certify rules that create reusable operators

**Meta Forge** extends Generic Forge from synthesizing operator *instances*
to synthesizing operator-*generating rules*. It runs entirely in GitHub
Actions with no ChatGPT, Codex, paid model API or permanent workstation.
It does not claim self-originating semantics or unrestricted creativity.

## Exact research object

A meta-rule is **data**, a list of one to four typed word transformations.
For example:

~~~json
[{"op":"append","slot":2},{"op":"reverse"}]
~~~

Given an input operator program, the rule creates a **new** operator
program. This new program runs under Generic Forge's already-reviewed
image/signal interpreter; no generated executable code is used.

The trusted interpreter has a small, explicit repertoire: reverse the
operator word, rotate it, duplicate its first or last step, append/prepend
one domain-specific primitive, replace the first/last step, wrap a
program in a selected primitive, or remove one step.

The *rules themselves* are **not a fixed list of completed candidates**:
each verified rule can become the parent for a longer rule, and the
generator computes these compositions from the actual, previously
evaluated state. This is a bounded typed grammar and remains limited by
the trusted underlying primitives.

## Two domains and independent checks

The same meta-rule is evaluated on both Generic Forge environments:

| Environment | Each generated program executes on |
| --- | --- |
| \`grid3\` 3×3 monochrome image | all **512** bitmaps |
| \`signal4\` four 2-bit samples | all **256** possible signals |

For each environment the evaluator tests **three development seed
programs and three holdout seed programs**. For each generated program:

1. Two separately implemented **meta-rule interpreters** produce the
   operator word, and their exact outputs must agree.
2. Generic Forge executes that word using its separately implemented
   reference/cell and integer/bitwise interpreters, and validates every
   input/output in the finite domain.
3. The evaluator records output-truth-table fingerprints, real behavior
   changes and distinct results.

Each accepted rule is therefore tested on **12 source programs** and
**4,608 environment inputs** across the two domains (both execution
implementations run on those inputs). The number does not imply a
general theorem about every possible operator word or arbitrary
images/signals.

Candidates are rejected if they have no meaningful effect on the
development/holdout probes, if there is no holdout effect in either
domain, if they exceed the maximum program length, or if they duplicate
the complete recorded evaluation fingerprint of an earlier rule.

The program-generation evaluator is independent of the generator's
bounded novelty score. The score rewards source-program behavior
differences, holdout effects, output diversity and reuse of a
previously certified meta-rule; it is **not** an objective measure of
scientific importance.

## Persistence and self-expansion

The persistent state is **data only** at:

- Branch: \`autonomy/meta-forge-state\`
- Path: \`docs/autonomy/meta-forge-state.json\`

Each receipt includes the complete typed rule, optional verified parent
ID, exact source SHA, 12-program evaluation fingerprint, holdout
statistics, versioned evaluator identity, score, timestamp and an
append-only SHA-256 chain. Every historical rule is independently
recomputed when the state is read.

Generation of a new rule may depend on the previously saved rule as
its parent. Thus the **output of the rule generator can itself become an
input of the rule generator**. Yet the underlying trusted interpreter
remains fixed and no self-modifying executable source is accepted.

## Execution and trust isolation

- On an untrusted PR: read-only Python regression, exact-head candidate
  generation, full finite verification, ephemeral receipt transition,
  and **invocation** on an unseen input operator program.
- On a trusted main push or daily schedule: propose one rule from
  already verified history.
- In a **separate write-enabled job**: use main's pinned controller,
  regenerate and byte-compare the candidate, rerun both interpreter
  paths and every finite-domain check, then append **one JSON record**.
- Never execute JSON/state text as Python, shell or Lean code.
- No untrusted PR ever gets a write token. The generator cannot
  rewrite the evaluator, change GitHub Actions, alter main, or merge PRs.
- No silently skipped failed verification or fabricated research result.

The cron is 11:07 UTC / **20:07 JST**, after Generic Forge's nominal
10:19 UTC / 19:19 JST. GitHub schedules can run late or be missed.
Each job has an 18-minute time limit; at most **88 rule proposals**
are considered per cycle, up to 64 verified receipts are retained, and
meta-rule length is at most four edit steps. These are safety/resource
ceilings, not fixed candidate lists.

For PR #234 still under review, this change is **stacked** onto that
branch. It is not yet deployed and must not be considered live before
Generic Forge and this PR are merged into main.

## Reproduce and use a verified rule

Run from the repository root:

~~~bash
python -m unittest discover -s tests -p test_meta_forge.py -v

python -B -m tools.autonomy.meta_forge prepare \
  --state tests/fixtures/meta_forge_empty.json \
  --day 2026-11-24 \
  --head "$(git rev-parse HEAD)" \
  --output verification/meta-forge/proposal

python -B -m tools.autonomy.meta_forge receipt \
  --state tests/fixtures/meta_forge_empty.json \
  --head "$(git rev-parse HEAD)" \
  --evidence verification/meta-forge/proposal \
  --output verification/meta-forge/verified-state.json

python -B -m tools.autonomy.meta_forge apply \
  --state verification/meta-forge/verified-state.json \
  --rule-id mf_ACTUAL_VERIFIED_ID \
  --domain grid3 \
  --program-json '["rotate_cw","dilate","shift_right","mirror_lr"]'
~~~

The last command prints a *generated operator program* and confirms
its finite image behavior using the independent Generic Forge evaluator.
Use an actual ID from the verified state.

## Remaining frontier

The trusted meta-operator vocabulary is still fixed. A following
system would allow proposing **new symbolic operator semantics**
inside a restricted, formally checked language, then require
independent evaluation of semantic safety before upgrading them to
trusted primitives. This work is not claimed here. Evaluator hacking
or dynamic code injection is deliberately prohibited.
