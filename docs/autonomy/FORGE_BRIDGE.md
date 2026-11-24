# Forge Bridge: connect the independently growing libraries

Generic Forge and Meta Forge currently persist independent ledgers. This
read-only experiment connects them without changing either production schema
or granting a new write permission.

For each of up to three shadow rounds, the latest eight certified meta rules
are applied to the latest six certified macros per domain (up to 96 rewrite
proposals per round). Two rewrite interpreters must agree, and two existing
environment interpreters must agree on every finite input. The exact
comparison baseline is every valid two-token composition of the original
primitives and the current bounded Generic Forge parent vocabulary.
A candidate is rejected when it is an identity, duplicates any previously
accepted behavior in this experiment, or is reachable by that pair frontier.
The selected shadow operator becomes an eligible seed and pair-frontier
token in the next round; lineage references identify the actual source rule
and seed. A no-candidate result is preserved rather than invented progress.

This is a stronger finite experiment, not a new expressive primitive:
everything still expands to the reviewed eight-step maximum typed program.
The score does not establish usefulness or novelty outside the finite domains.
The shadow experiment itself never writes the live Generic Forge ledger. The
separate production acceptance route described below can promote one result.

The separate daily GitHub schedule reads both live data branches, preserves
exact input snapshots and source SHA in its artifact, and runs the same
deterministic experiment in a fresh process to check the entire report.
PR CI uses snapshots of the actual certified ledgers from 2026-11-24,
rather than requiring a writable state branch. No API inference, generated
source execution, state writes or main writes are introduced. All bounds are
fixed, with a 20-minute job limit.

## Production reentry (reviewed promotion)

Generic Forge now alternates a cross-forge opportunity (odd number of saved
receipts) with ordinary composition. If no rule-derived behavior outside the
bounded pair frontier exists, the ordinary generator is used. The daily
shadow report remains separate and read-only.

A promoted record uses the existing Generic ID and hash chain plus an
`origin` field containing the certified rule ID and chain hash. Its left
parent is a verified Generic macro, and its right token names the certified
Meta rule. An embedded, validated Meta ledger snapshot allows historical
replay even without the live Meta branch. Every previously recorded receipt
is byte-for-byte unchanged; ordinary composition can use a promoted macro
exactly like any other macro. The snapshot must be an append-only extension
of accepted ancestry, and both rewrite interpreters and both environment
interpreters must agree. Duplicate finite behavior remains disallowed.

The existing read-only proposal and separate write-enabled persistence jobs
regenerate the exact candidate from both current state branches, compare
the full plan, and independently audit before appending one JSON receipt.
If either upstream state changes in between, the stale plan fails closed.
No new permission, unbounded retries, generated executable code, or main
write path is introduced. The old 96-receipt cap, one per half-hour slot,
typed program length and execution limits remain in force. A new production
receipt is not a theorem about usefulness, generalization, or expressive
power.
