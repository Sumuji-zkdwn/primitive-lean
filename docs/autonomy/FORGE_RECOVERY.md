# Forge scheduler recovery

GitHub cron delivery is best effort. On 2026-11-24, the two half-hourly
producer workflows each received only one observed scheduled run by 07:19 UTC.
Push and pull-request CI success is not evidence of scheduler health.

The original cron schedules remain independent entry points. Each live
producer now selects the oldest still recoverable half-hour slot strictly
after its ledger marker, bounded to the current slot plus the preceding three.
A slot labels a recovery calculation executed now, not a claim that the job
ran in the past. Older gaps behind a certified receipt are never filled.
An empty ledger begins at the current slot. Existing duplicate guards and
independent verification are unchanged.

The recovery controller starts on its offset cron, manual dispatch, reviewed
controller changes on main, or a successful main operational completion of
the named watchdog/supervisor/conveyor/integration workflows. It never consumes
their artifacts or checks out their head. It dispatches only the two fixed
Forge workflows on main, sequentially, with an exact correlation identifier.
At most four rounds (eight child runs), with a 15-minute total polling budget
and three-minute child polling limit. Existing active producers defer recovery.
Failure, ambiguous attribution or timeout halts the invocation. Success without
ledger advancement stops attempts on that track. No direct ledger writes,
new executable generator rules, secret requirements, or automatic merges.

The existing per-workflow concurrency and ledger validation still own
certification; overlapping native deliveries can race but cannot bypass
replay/validation. The relay does not guarantee a wall-clock SLA: if GitHub
suppresses every trigger, an independent external scheduler is required.
The JSON report and child-run logs distinguish successful dispatch, ledger
advancement, exhausted search/no progress, and failed or delayed delivery.
