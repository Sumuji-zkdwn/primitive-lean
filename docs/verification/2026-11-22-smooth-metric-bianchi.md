# Smooth Levi-Civita from a C3 metric: second Bianchi

Date: 2026-11-22 JST. Dependent draft PR built on PR #188, which depends on #187 and #186.

## Upstream provenance

The main regularity proof is from the Apache-2.0 licensed
korbonits/ricci-flow-blueprint repository at immutable commit
c8017e2c26898d11f39cec0dfce89368d5a0506a, file
RicciFlowBlueprint/LeviCivitaSmooth.lean.

The derived file lean/RicciFlowBlueprint/LeviCivitaSmoothPort.lean
retains all smoothness proof bodies and original attributions.
It changes the upstream LeviCivita import to Mathlib's actual
LeviCivita module and omits the final RicciOfMetric/sectional
curvature section because that invokes other upstream modules.
Any additional mathlib API compatibility edits must be recorded in
version control. The original Apache-2.0 license is included
by the dependency PR at licenses/ricci-flow-blueprint-Apache-2.0.txt.

## Theorem

With a C-infinity Riemannian manifold and C3 Riemannian bundle metric,
the upstream theorem
RicciFlowBlueprint.contMDiffCovariantDerivative_leviCivitaConnection
derives the C1 and C2 covariant derivative regularity instances
of Mathlib's actual LeviCivitaConnection.

Then the earlier real manifold-level CovariantDerivative.bianchi_second
proves the cyclic identity for the full smooth Riemann curvature:
  (nabla_X R)(Y,Z)W + (nabla_Y R)(Z,X)W + (nabla_Z R)(X,Y)W = 0
for C2 vector fields X,Y,Z and C3 vector field W.

Unlike the preceding PR #188, this version does not separately
assume smoothness of the constructed Levi-Civita connection; it
derives that property from the metric's own C3 regularity.
All metric and manifold smoothness hypotheses remain explicit.

## Strict remaining boundary

The final RicciFlat -> Yang--Mills theorem directly for a smooth
metric remains incomplete: the indexed contraction theorem in PR #186
must still be connected to smooth curvature tensors, orthonormal
frames, Ricci trace compatibility and pair-exchange curvature symmetry.
The present proof uses RiemannianBundle; Lorentzian pseudo-Riemannian
generalization has not been formally supplied.

These are prior mathematical results, not newly discovered physical
interactions. No standard-model matter or new boson is claimed.

## Exact verification

Dedicated pinned Lean 4.36.0-rc2 + mathlib
2ddf59c8f14245864e6c0ed227a2dab76b9efea2
compiles imported dependencies with --trust=0, checks the
new theorem, and audits foundational axioms.
No main auto-merge. Wait for exact-head CI before success claims.

Source:
https://github.com/korbonits/ricci-flow-blueprint/blob/c8017e2c26898d11f39cec0dfce89368d5a0506a/RicciFlowBlueprint/LeviCivitaSmooth.lean
