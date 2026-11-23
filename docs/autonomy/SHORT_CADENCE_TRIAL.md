# Generic Forge + Meta Forge: bounded 10-minute observation trial

This patch temporarily replaces the usual **one receipt per UTC day**
with a **10-minute UTC slot**, to observe the actual verified feedback loop
without incurring unlimited GitHub Actions use. No AI API or external
cloud model is invoked.

## Exact live schedule

**2026-11-23 (UTC) only, 08:00–12:59**:

- Generic Forge: every 10 minutes, at each 10-minute mark.
- Meta Forge: every 10 minutes, with a 2-minute offset.
- This corresponds roughly to **17:00–21:59 JST** on November 23.
- GitHub Actions schedule is *best effort*: jobs may be delayed or
  dropped. The actual UTC time rounded down to a 10-minute boundary,
  not the ideal cron time, identifies a run.

**Hard caps** in both controllers: at most **five total saved receipts per
system**, including the already verified Nov 23 main-merge receipts.
This allows **four additional novel verified artifacts at most for each**,
not a quota of five per hour. Each job has its prior runtime limits.

After 12:59 UTC on Nov 23, 2026 the trusted controller refuses new
10-minute-slot experiments with TRIAL_WINDOW_CLOSED. After its fifth
verified receipt, it refuses with TRIAL_CAP_REACHED.

The calendar-restricted cron itself matches Nov 23 in later years as
well, but any future trigger will produce **no candidate** because of the
hardcoded date window. It can be removed after the experiment by a
reviewed normal PR; it does not create research receipts indefinitely.

## Data preservation

The first live runs already recorded one verified receipt in
each existing state branch:

- autonomy/generic-forge-state/docs/autonomy/generic-forge-state.json
- autonomy/meta-forge-state/docs/autonomy/meta-forge-state.json

The trial **does not reset, overwrite or reinterpret those receipts**.
The existing exact JSON schema and SHA-256 linked history remain intact.
The historical day field may contain YYYY-MM-DD; new trial receipts
use exact YYYY-MM-DDTHH:MMZ UTC slots at minute 00/10/20/30/40/50.
The existing last_utc_day field is retained for schema compatibility
and now means the latest verified UTC date *or slot*. Lexicographic
ordering preserves the relationship between a day and its later slots.

The separately privileged receipt job must use the **same slot from
the first-stage exact proposal**; recomputing date at commit time
could produce a different slot if verification crosses a 10-minute
boundary. The receipt job regenerates trusted data from current state
and compares proposal bytes before saving. A concurrent update, failure,
unknown evaluator or altered source still fails closed.

## What to watch

1. Each workflow's scheduled/main-push run and run conclusion.
2. Count of verified receipts and their timestamps in isolated branches.
3. New operator and meta-rule IDs, parent IDs, generated programs,
   observed output fingerprints and duplicate rejection.
4. Whether the selected Meta Forge rule actually uses a previously
   verified meta-rule as parent (not just a new one-step rule).
5. Any failed job or quota-related skip.

SUCCESS on a workflow means its local finite checks passed,
**not** that a universally useful program or a new physical law was
discovered. The candidate generator and independent evaluator remain
separate. Unique behavior is not a measure of practical usefulness.

## Audit

Run without GitHub access:

    python -m unittest discover -s tests -p test_generic_forge.py -v
    python -m unittest discover -s tests -p test_meta_forge.py -v

The regression covers old-to-new timestamp compatibility, malformed
slot rejection, one receipt per slot, bounded total receipts,
cross-domain evaluator consistency and higher-order rule ancestry.

Existing primitive-lean math research workflows and their schedules
are not modified by this trial.
