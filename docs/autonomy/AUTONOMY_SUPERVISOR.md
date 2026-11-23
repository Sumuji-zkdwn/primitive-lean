# GitHub-only Autonomous Research Supervisor

This controller makes the **existing bounded research loops operationally
independent of a human, a ChatGPT conversation and Codex**. The repository's
fixed source code runs in GitHub-hosted Actions. No inference service or paid
model API is called. This change does **not** solve unrestricted autonomous
research or create novel mathematical definitions without reviewed semantics.

## Scope

The supervisor runs daily at **18:41 UTC** after the ordinary scheduled runs
of five existing workflows:

| Workflow | Persistent *data-only* state |
| --- | --- |
| Research Conveyor | autonomy/research-conveyor-state |
| Finite Discovery | autonomy/finite-discovery-state |
| Strategy Evolution | autonomy/strategy-evolution-state |
| Definition Foundry | autonomy/definition-foundry-state |
| Research Scout | autonomy/research-scout-state |

The live job:

1. Checks out **main only**, without retained git write credentials.
2. Runs offline controller regression tests.
3. Fetches each fixed state JSON file via GitHub's Contents API, without
   checking out or executing the data branch. A malformed or inaccessible
   ledger causes a **fail-closed** run.
4. Fetches both scheduled and manually dispatched recent runs of each
   workflow, filtering for the default branch.
5. Labels a track as already run, currently running, failed today, or
   missing a run today. A failed today's run is **not retried**.
6. If any track has no run yet today, dispatches at most **one**
   fixed allowlisted workflow via GitHub's native workflow_dispatch API.
   A second invocation normally sees that new queued run and does
   not repeat it. A strict once-per-day transaction is not guaranteed
   against GitHub API eventual consistency; the supervisor's own
   concurrency group prevents overlapping supervisor jobs.
7. Saves a JSON report as a 30-day GitHub Actions artifact and a Markdown
   job summary. Every source branch, daily scheduler, and CI configuration
   remains otherwise unchanged.

The source branches' receipts may already have exhausted their limited
finite candidate catalogs; a successful run with unchanged receipt count
does not authorize a claim of new mathematical work.

The original primitive-autonomy.yml is *deliberately inactive*
(if: false) and is not restarted by this supervisor.

## Security / resource boundary

- No automatic PR merge, code editing, issue creation, untrusted model output,
  external model API, purchased token, or self-modifying workflow.
- No arbitrary workflow names: the five known files and the ref main are
  compiled into the trusted source.
- No privileged PR job: pull-request events only run pure offline tests.
- The supervisor has actions:write but not contents:write; it can only
  dispatch an existing main-branch workflow and retain report artifacts.
- One proposed recovery per invocation, at most an eight-minute supervisor
  job, no retry on known failed workflows, plus the cost of any recovered
  target workflow. Existing workflows retain their own time limits.
- No guarantee of 24/7 platform availability: GitHub may delay or drop
  scheduled runs, cap Actions resources, or disable schedules after public
  repository inactivity.
- Turn the watchdog off via GitHub Actions -> Autonomous Research Supervisor
  -> Disable workflow. The five original scheduled loops are separate.

## Reproduction

Offline tests (no GitHub authentication, model or network needed):

    python -m unittest discover -s tests -p test_autonomy_supervisor.py -v

When installed on main, GitHub Actions runs the live loop automatically.
A manual workflow_dispatch on main is also available. Both read the exact
Github repository indicated by GITHUB_REPOSITORY and use the ephemeral
GITHUB_TOKEN. Reports are in Actions -> selected run -> Artifacts.

## What remains *unsolved*

This is operations supervision, not scientific judgment. Each research
adapter still encodes a bounded, reviewed finite family; the system can
determine verified finite outcomes and next steps within those families.
It cannot autonomously decide that an arbitrary continuum argument is a
valid theorem, conclude that a physical theory is confirmed, or write a
safe new adapter for an unrelated subject.

A future broader loop would require separate sandboxed generation,
machine-checkable acceptance conditions and independent verification
of all new source/assumptions. Such an extension should be a separate
reviewed proposal, not hidden inside a watchdog.
