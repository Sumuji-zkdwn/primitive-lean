# Forge Watchdog: reliability evidence and capability-growth audit

This is a short, **time-bounded intervention** for Generic Forge and
Meta Forge, not a general-purpose unattended background service.

## Why this exists

On Nov 23, 2026, Generic Forge and Meta Forge each saved two verified
records: an original \`push\` activation and one later timed-slot record.
As inspected, GitHub's \`schedule\` event listing contained **no scheduled
runs from either Forge**, even though their exact main workflows had
10-minute crons. A schedule line in a YAML file does **not** prove a run
actually happened. This watchdog independently measures real
workflow-specific GitHub Actions events and data-only verified receipts.

## Three distinct checks

**1. Scheduler delivery:** A REST-API observation of real \`schedule\`
runs, \`workflow_dispatch\` runs and last observed status for each
workflow. Nominal elapsed cron slots are shown as a benchmark only;
GitHub may delay or drop scheduled events. A mature slot is counted
only after a 20-minute reporting delay. Missing events are marked
\`no_scheduled_runs_observed\`, not silently called success.

**2. Persistence and generational reuse:** Validate **both entire**
hash-chained ledgers and evaluator identities using their own trusted
modules, then count persisted records, Generic Forge use of a \`m:\`
macro as a source token, Meta Forge parent links and maximum verified
meta-rule ancestry depth. A rule whose parent is named but not
reconstructible will fail validation, not count as new work.

**3. Behavioral coverage vs expressive power:** Check stored Generic
Forge full-domain behavior fingerprints against **all** 1- and 2-step
primitive compositions in each finite environment. Report distinct
new behavior explored, number of stored operators outside that
short baseline, flattened program length and macro reuse. A result
outside the two-step baseline is **not** a new primitive operation:
every stored program still expands into the original primitive
vocabulary. The auditor explicitly marks
\`expressive_power_beyond_trusted_primitive_closure=false\`.

For Meta Forge, track the number of distinct 12-program probe
signatures, the number of child rules genuinely using verified parents,
rule length and ancestry depth. This avoids claiming that simply
adding tokens or raising a heuristic score makes a system smarter.

## Bounded recovery, no cron dependency

The workflow \`.github/workflows/forge-watchdog.yml\` runs:
- a **read-only** PR CI job that validates the checker against the
  actual pinned two-receipt seed and synthetic missed-schedule records;
- on main push, \`workflow_dispatch\` or an independent low-traffic
  cron, a narrow privileged job that can only dispatch the two
  **existing reviewed workflows**, not write repository contents.

A main push causes up to **four** serialized checks, spaced ten
minutes apart, using one GitHub-hosted runner for at most 36 minutes.
This is a short-lived relay independent of GitHub's unreliable
scheduled-event delivery, not an always-on machine. A scheduled
watchdog invocation performs **one** check only.

Before *every* dispatch, it freshly fetches both state branches,
the actual workflow-specific GitHub Actions run histories and validates
the entire state using trusted main code. A workflow is dispatched
only when all conditions hold:

1. Actual UTC time is between **2026-11-23 08:00 and 12:59:59 UTC**.
2. The relevant state branch contains fewer than **five** verified
   receipts, including the existing two.
3. The current ten-minute UTC slot has not already been saved.
4. No operational run of the same workflow is currently active.
5. No operational launch of that workflow occurred in the past
   **600 seconds**.

Only \`actions:write\` (to dispatch those named workflows) and
\`contents:read\` (for source and state) are permitted in the relay job.
State branches are **data only**, and no untrusted candidate code is
ever executed with the dispatch permission. Successful dispatch is
not proof of a verified result; only the target workflow's persisted
receipt is evidence of successful research.

Each iteration outputs a JSON report and raw GitHub API run snapshots
in a 30-day GitHub Actions artifact. Read-only PR validation never
fires any dispatch.

The experiment is **self-expiring**: after 12:59:59 UTC Nov 23 the
gate refuses every dispatch. The cron is date scoped to Nov 23,
and per-system five-receipt caps in the original Generic and Meta
engines remain authoritative.

This creates a reliable way to *attempt* a finite sequence even if
no cron event is delivered, but it still depends on GitHub's Actions
service, permissions, runner availability and job execution success.

## Reproduce offline

~~~bash
python -m unittest discover -s tests -p test_forge_audit.py -v
~~~

A real report is generated through:

~~~bash
python -m tools.autonomy.forge_audit \
  --generic-state tests/fixtures/forge_audit_generic.json \
  --meta-state tests/fixtures/forge_audit_meta.json \
  --generic-runs /tmp/generic-runs.json \
  --meta-runs /tmp/meta-runs.json \
  --now 2026-11-23T11:40:00Z \
  --output /tmp/forge-audit.json
~~~

The run JSON files must be genuine workflow-specific REST responses
or strictly shaped fixtures in read-only tests.

## Honest limitations

The watchdog cannot guarantee the hosting platform will run any
particular cron or dispatch. It does not add new operation semantics,
invent mathematical facts or improve the domain-specific objective.
It provides a machine-readable answer to whether any real new work
was saved, whether rules truly reused their ancestors, and whether
the growth represents only expanded **search depth** rather than
expanded **expressive vocabulary**.
