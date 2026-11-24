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
Shadow operators are not promoted to the live Generic Forge ledger.

The separate daily GitHub schedule reads both live data branches, preserves
exact input snapshots and source SHA in its artifact, and runs the same
deterministic experiment in a fresh process to check the entire report.
PR CI uses snapshots of the actual certified ledgers from 2026-11-24,
rather than requiring a writable state branch. No API inference, generated
source execution, state writes or main writes are introduced. All bounds are
fixed, with a 20-minute job limit.

Next acceptance gate: inspect actual outside-pair and shadow-reentry results.
Only then design a backward-compatible promotion contract with persistent
cross-ledger ancestry.
