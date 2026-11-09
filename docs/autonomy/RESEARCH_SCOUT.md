# Research scouting: periodic offline discovery, opt-in paid inference

This is a new, **bounded and auditable** complement to the existing finite
operator-witness generator. The scout is **not a theorem prover**, and a
source line containing "unproved" is only a *lead*, not proof that a statement
is true, novel, or genuinely open. No AI output is executed or promoted to a
Lean theorem. The mainline Lean verifier and PR review remain authoritative.

## Architecture and isolation

- `.github/workflows/research-scout.yml`: every six hours in GitHub-hosted
  Actions, or manually via `workflow_dispatch`; the test job runs on PRs.
- `tools/autonomy/research_scout.py`: offline scan of explicit unresolved-
  claim markers in `docs/research/*.md` and `docs/integration/*.md`. Records
  source path, line, exact SHA-256 of source file, candidate fingerprint, and
  the `main` commit SHA. Deduplicates and bounds queue to 32 entries.
- `autonomy/research-scout-state`: isolated data branch containing
  `docs/autonomy/scout-state.json` and optional unverified JSON notes. The
  branch must exist before enabling the workflow. It must never be used as
  an executable-code checkout. GitHub Actions checks out **code from main**
  into `control` and reads this separate branch **only as data**.
- A model call, if enabled, produces one candidate note with a finite
  falsification test or proof obligation; it is clearly marked `UNVERIFIED`.
  Review it separately before implementing or running any generated code.
- The original autonomous Lean cycle uses a different branch and should not
  be accelerated while its base differs from main. The legacy 3 cycles must
  be integrated under pinned Lean and axiom audit first.

## Cost guard / opt-in

**No paid inference is called by default.** To opt in, set repo Actions
variable `RESEARCH_AI_PAID_OPT_IN=true`, variable `RESEARCH_AI_MODEL` to an
API model enabled for your account, and Actions secret `OPENAI_API_KEY`.
The process reserves **at most one API attempt per UTC day** in the persistent
state branch before issuing the HTTP request. Even a failed request uses the
daily reservation, so an automatic retry cannot increase spend. Each call
uses at most **1,024 output tokens** and about 2,800 input characters, with
no tools, no background mode and `store=false`. A reservation is not a proof.

This is a **call and token limit, not a monetary ceiling**: model prices,
tokenization, and GitHub-hosted runners can vary. Configure an external API
**project spend limit** before turning on the opt-in flag. Repository-level
schedules and variables do not themselves authorize spending. No PC needs
remain powered on, and the main branch is never modified by scheduled runs.

## Safety and idempotency

All state updates are serialized with a GitHub Actions concurrency group.
The scan cursor only advances after writing the isolated branch; the paid
reservation is pushed **before** an API call. Failure prevents a repeat on
that UTC day. A duplicate source line is not re-enqueued, and source lines
removed from the current main tree are dropped from the pending queue.
Outbox notes record model usage and the exact observed `main` revision.
Every non-proof is explicitly labelled as such. AI text is never executed.

## Offline checks

```sh
python -m unittest discover -s tests -p test_research_scout.py -v
python tools/autonomy/research_scout.py scan \
  --root . --state /tmp/scout-state.json \
  --head "$(git rev-parse HEAD)" --report /tmp/scout-report.json
```

## Legacy growth migration

The three previously verified witnesses exist on
`autonomy/verified-operator-growth`, which diverged substantially from main.
The integration proposal migrates their unmodified source bytes,
ledger and verifier registrations onto current main. Check the new source
hashes, full exact-head Lean CI and axiom audit before merging it. Until a
new main-derived *working branch* is created from the reviewed merge commit,
the legacy schedule should remain paused; don't force-push or erase the old
branch and its audit history. Once migrated, change `TARGET_BRANCH` in
`tools/autonomy/grow.py` and the workflow checkout/push refs together and
re-enable the schedule only after a fresh trial cycle succeeds.
