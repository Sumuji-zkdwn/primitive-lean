# ERG-Aout R005 handoff for primitive-lean

Status: candidate-only integration; no claims are promoted by this file.

ERG-Aout R005 proposal: https://github.com/Sumuji-zkdwn/ERG-Aout/pull/102
Reviewed R005 head: 7d8be886f7ee8df695b97f9818e707e133d82bfc
R005 formal binding: examples/r005/f0_chat.formal_binding.json (in ERG-Aout).

## Evidence boundary

The exact-head Primitive Lean integration CI runs the existing Lean build,
trust-zero checks, axiom audit and integration verification without changing
their behavior. Only after the preceding checks pass, it exports
verification/erg-formal-evidence.json. This file is uploaded in the existing
primitive-integration GitHub Actions artifact.

The manifest contains the actual checked-out commit, SHA-256 of tracked Lean
source blobs from that commit, and GitHub Actions run identity. It does NOT
assert a finished CI conclusion, proof correctness, semantic correspondence,
or acceptance of an ERG claim.

To use it, independently verify that the exact-head GitHub Actions job finished
successfully, then compare the manifest's source_files entries with the
formal_source.files SHA-256 values of the ERG sidecar. R005 still performs its
own commit, declaration-name and type checks; fidelity_note and non_claims
still require human review. The manifest commit can be newer than a binding's
pinned ancestor, so equality of file digests is a source-identity statement,
not proof that the two commit histories are interchangeable.

## Candidate-only handoff to Research Scout

The two bounded lines below are explicitly retained as hypotheses/leads from
ERG-Aout PR #102. Their presence here does not establish mathematical truth.
Research Scout only reads source notes, marks leads UNVERIFIED_LEAD, and does
not promote them into Lean; paid inference remains disabled by default.

- 未証明: F0 cand.f0.imbalance_monotonicity: strict imbalance monotonicity remains a conjecture; finite checks do not establish its general form. Seek a finite counterexample or state explicit hypotheses for a proof.
- 要検証: F0 cand.f0.drop_b_not_always: formalize the claim that violating condition B does not necessarily restore distinguishability; do not substitute the existing counterexample for failure of condition A.

The candidate cand.f0.period_bound has restricted Lean evidence requiring a
minimal-period/distinct-cycle hypothesis; it must not be read as an unrestricted
period bound. R005 labels this proves_restricted and retains its non_claims.

This handoff reads external ERG state as reference material only. It does not
fetch untrusted executable code, alter mainline proof sources, enable paid
model calls, or auto-promote accepted nodes.
