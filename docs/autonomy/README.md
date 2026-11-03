# Primitive-lean: bounded autonomous proof growth

This is an opt-in GitHub Actions controller for a **finite, auditable** loop:

1. Read the last verified cycle in the dedicated branch
   \`autonomy/verified-operator-growth\`, initially forked from the
   separately verified PR #57 commit \`1f24bc3d082ff64d6972401e96274d5c28586807\`.
2. Choose one never-before-used deterministic finite-state operator witness.
3. Generate five candidate Lean theorems and three definitions in an
   \`AutonomyCycleNNNNN.inc\` supplement.
4. Register its path, namespace, mathematical scope, and exact SHA-256
   source hash. Record the model and parent commit in the ledger.
5. Run the existing complete integration checks with pinned Lean/mathlib
   and \`--trust=0\` plus all-declaration axiom audit.
6. **Only on complete success**, mark the cycle verified, commit the
   small allowlisted change set and push it back to the dedicated branch.
   The next scheduled run reads that new verified state.

The engine never merges, changes \`main\`'s proof sources, rewrites
historical proof files, invokes an untrusted external AI, or silently
retries/commits failed proofs. A failure leaves the source branch
unchanged. CI artifacts retain diagnostics. It generates **finite
counterexample certificates**, not novel general theorems or autonomous
mathematical insight. New models are required to change observational
distinguishability, and duplicate transitions are excluded.

The finite generator enumerates 84 model configurations for
\`Fin n\`, \`3 ≤ n ≤ 8\`, with an identity-only old transition and a
genuinely separating additional transition. After these are exhausted
it exits successfully without generating more. There is exactly one
candidate generated per invocation. Adding new conjecture *families*
requires a reviewed controller update.

## Activation and resource controls

The scheduler lives on the default branch, because GitHub Actions
\`schedule\` triggers only workflows on the repository default branch.
It also runs once on installation and supports manual dispatch.
Its cadence is **Monday and Thursday, 00:17 UTC (09:17 JST)**.
It runs at most one verified cycle per invocation and has a job
timeout of 55 minutes; private repository GitHub Actions minutes
and any applicable billing/quota are consumed. Recurrent work is
performed by GitHub Actions, not by an ongoing ChatGPT session.

The target branch must be present. It may be inspected or compared to
other research branches, but is never automatically merged. Updates
require GitHub Actions \`GITHUB_TOKEN\` to have permission to push to
that dedicated branch. If branch protection disallows writes, the
workflow stops rather than bypassing protections.

Disable the schedule by disabling the workflow in GitHub Actions or
removing the \`schedule\` trigger on the default branch. To advance
the next cycle manually, dispatch the workflow from the Actions tab.

## Artifacts and trust boundary

The independent controller is \`tools/autonomy/grow.py\` on \`main\`.
The research branch is treated as **data**, not as the source of a
privileged generator. The fixed controller only writes a new additive
proof source and its registry, scope, source manifest, and ledger.
Verify the exact GitHub Actions run/commit before citing new counts.
