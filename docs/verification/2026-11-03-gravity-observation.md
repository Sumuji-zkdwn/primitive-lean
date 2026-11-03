# Gravity observation fibers and exact moment hierarchy — 2026-11-03

## Provenance

This proposal extends the proven (unmerged) PR #41 GravityCocycle.inc, which in
turn is stacked on PR #37 ViscousRewrite.inc and the PR #3 research branch.
Previous source files and existing theorems are not rewritten.

## State, observation, forgetting

A finite labelled set A with mass and one-dimensional coordinate maps gives
a scalar observation O_A(R) = sum_{i in A} m_i/(R-x_i), before the physical
factor -G. Samples must have R != 0 and R != x_i.

A forgetting map K on states is idempotent precisely when K(K(s))=K(s).
An observation family descends along K iff equality of K-states forces
equality of ALL observed values at ALL probe locations. The new source
constructively proves the factorization through K under idempotence.

## Exact finite moments

M_n(A) = sum_{i in A} m_i (x_i)^n.

For every finite source set and non-collision observation R,
O_A(R) = M_0/R + M_1/R^2 + M_2/R^3
         + sum_{i in A} m_i*x_i^3/[R^3*(R-x_i)].

This is an EXACT finite identity, not an unqualified infinite asymptotic
expansion. If two configurations have the same first three moments, their
field difference is the difference of these explicit remainders.

Symmetric equal masses m at positions ±a (a>0) have
M_0=2m, M_1=0, M_2=2ma^2; merging into 2m at the origin preserves M_0 and
M_1 but not M_2. For R>a,
O_pair(R) - O_merged(R) = 2ma^2/[R(R^2-a^2)] > 0, if m>0.
Therefore forgetting separation cannot preserve every external probe, even
though it is idempotent and keeps the total mass of this family constant.

## Scope boundaries

The observation is the positive inverse-distance scalar field in 1D; the
Newton potential is obtained by multiplying by -G. General relativity,
continuous mass densities, arbitrary 3D multipole tensors, universal source
reconstruction from finite moments, and the inference of 1/r solely from
2-cocycle associativity are not claimed. The file is a formal proof candidate
until a fixed Lean/toolchain Actions run with no warnings and permitted axioms
completes.

## Verification protocol

A dedicated workflow first assembles the existing GravityCocycle source and
GravityObservation.inc with Mathlib to check all theorem names and axioms,
then runs the full repository integration at the exact proposed commit.
The source registrar is tools/verify_main_result.py, backed by
docs/integration/manifest.json and tools/check_pr_integration.py.
