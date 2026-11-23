# Forge Watchdog — read-only half-hour monitoring

The original November 23, 2026 recovery relay was deliberately short-lived.
Its finite dispatch gate has expired and has **not** been reopened. The
long-running successor checks two reviewed, independent research workflows
without dispatching them, writing repository contents, or using paid APIs.

## Cadence and trust boundary

- Generic Forge runs at **:07 and :37 UTC** each hour.
- Meta Forge runs at **:17 and :47 UTC** each hour.
- Forge Watchdog audits at **:27 and :57 UTC** each hour.
- GitHub Actions cron delivery is best-effort, not a guaranteed 30-minute
  timer. Overlap is controlled by separate, non-cancelling concurrency groups.
- The watcher runs only reviewed code checked out at the exact main commit.
  Both isolated state branches are treated exclusively as untrusted JSON.
- The monitor's token permits `contents:read` and `actions:read` only.
  **There is no dispatch, self-edit, PR merge, or write path in this job.**

## Evidence in each scheduled report

Each watchdog invocation downloads workflow-specific recent GitHub API run
histories and verifies both complete SHA-256-linked operator/rule ledgers.
Its `review/report.json` artifact separately records:

1. **Delivery:** observed scheduled events and nominal slots matured by
   20 minutes, evaluated over a rolling four-hour UTC window. The latest
   100 run records limit completeness during unusually busy periods.
2. **Execution:** separately counts successful and failed operational runs;
   manual dispatches are not passed off as scheduled events.
3. **Actual progress:** total independently verified receipts and the
   number whose saved 30-minute UTC slots fall in the preceding four hours.
   A successful job with no new receipt is not called a new discovery.
4. **Capability:** parent/macro reuse, tested finite behavior diversity,
   comparison against short primitive programs, and the explicit finding
   that finite compositions do not expand primitive expressive power.

If the watchdog's validation or API read fails, the monitor job fails rather
than reporting an invented success. The raw response JSON and audit JSON
are uploaded as a 30-day GitHub Actions artifact, including after failure
when files are available.

## Hard research bounds

The two research engines still have bounded proposal and exhaustive
verification limits. Generic Forge stores no more than 96 verified operator
receipts; Meta Forge stores no more than 64 verified rule receipts. Once one
of those ceilings is reached it may still be scheduled, but its proposal
step records a no-candidate reason and its privileged persistence job
does not run. This avoids silently growing trusted semantics, storing
unbounded state or executing arbitrary generated code.

No fully automatic retention compaction, archive rotation, code mutation
or expansion of the trusted primitive interpreter is enabled here.

## Historical experiment and reproducibility

The earlier watchdog relay could temporarily dispatch reviewed workflows
during **2026-11-23 08:00–12:59:59 UTC** with a five-receipt trial cap and
a ten-minute cooldown. That gate is preserved in the Python auditor only
for historical experiments/tests. The continuous GitHub workflow never
reads its verdict to take an action, and never has `actions:write`.

Run the monitor unit tests with Python 3.12:

```bash
python -m unittest discover -s tests -p test_forge_audit.py -v
```

The retained offline fixtures test missing scheduled events, expired
recovery gates, receipt tampering, and the new rolling 30-minute observation.
