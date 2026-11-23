# Actual smooth Ricci-flat Levi-Civita connection and Yang–Mills

Date: 2026-11-22 JST. Proposed dependent DRAFT on PR #194, which depends
on #191, #190, #189, #188, #187 and #186. Never auto-merge main.

## Goal

Close the last *smooth-manifold* gap in the already formalized second
Bianchi -> contracted Bianchi -> source-free Yang–Mills identity.

PR #194 proves real moving-frame trace commutation algebra but does not
instantiate its FrameJet interface with smooth Mathlib Levi-Civita data.
Instead of pretending that an arbitrary vector-space derivative on all
functions is manifold differentiation, this PR ports a prior proof
that already handles the genuine smooth geometric differential
operators and the frame dependence correctly.

## External proof source and licensing

Source repo: korbonits/ricci-flow-blueprint
Immutable upstream commit: c8017e2c26898d11f39cec0dfce89368d5a0506a.
License: Apache-2.0; the original license and attribution are preserved
in licenses/ricci-flow-blueprint-Apache-2.0.txt (in dependency PR #188).

Newly ported source modules include Ricci, Sectional, LeviCivita,
LeviCivitaSmooth (compatibility shim to the already ported smoothness
proof), Variation, MetricTrace, GramSchmidtOrtho, OrthonormalFrame,
GlobalExtension, Scalar, Hessian, TraceCov, CurvaturePointwise,
RicciForm, RicciSymm, CurvatureSymm, CurvatureDeriv, and Divergence.

The copied proofs are *prior results by the upstream authors*.
The only intentional Mathlib API compatibility modification so far is
selecting the global Set.univ connection-law field
isCovariantDerivativeOnUniv in a few locations rather than an
ambiguous polymorphic isCovariantDerivativeOn property.
The LeviCivitaSmooth compatibility shim reuses the prior imported
C2 smoothness theorem rather than re-declaring it.

The dependency closure is large. All ports are considered UNVERIFIED
until the repository's exact pinned Lean/mathlib CI passes. No
nontrivial claims about C2 smoothness or Ricci curvature may be inferred
solely from copying or importing names.

## Crucial genuine smooth-manifold theorem

RicciFlowBlueprint.Divergence defines

  divCurvature(Y,Z,W)(x)

as the trace of the endomorphism on T_x M induced by the covariant
derivative of the Riemann curvature. This trace is independent of an
orthonormal basis. It provides the actual spin-curvature Yang–Mills
divergence, not a finite list of symbolic stand-in matrices.

The theorem CovariantDerivative.divCurvature_eq_covRicci_sub proves

  divCurvature(Y,Z,W)(x)
    = (nabla_Y Ric)(Z,W)(x) - (nabla_Z Ric)(Y,W)(x)

using full second Bianchi, curvature pair symmetries and, crucially,
metric-compatible local orthonormal frame and trace commutation.

The new wrapper Research/SmoothRicciYangMills.lean proves:

  if Ric of the Mathlib-constructed Levi-Civita connection
  vanishes globally, then divCurvature(Y,Z,W)(x)=0

for all sufficiently regular Y,Z,W and every x equipped with a
smooth local orthonormal frame extended to global smooth sections.

The required C1/C2 connection regularity is proved from a C3 metric
by the already verified dependency PR #189; no independently invented
Yang–Mills fields or Bianchi axioms are assumed here.

## Remaining frame-existence question

The new wrapper presently takes
  hs : IsOrthonormalFrameOn I E 1 fr u
  hu : IsOpen u
  hx : x in u
  hfr : all frame sections globally C2
as explicit inputs, exactly as the upstream contraction theorem does.

Upstream OrthonormalFrame.lean proves local Gram–Schmidt
orthonormalization and its local smoothness. GlobalExtension.lean
proves a local C2 section can be extended to a globally C2 section
agreeing near a point via bump functions. An additional Lean
construction must combine them to discharge hs/hfr at every x.
Until that additional construction is kernel checked, the result is
conditional on an available frame and is not unconditional in x.

A further independent generalization to pseudo-Riemannian/Lorentzian
metrics is required; current upstream construction is Riemannian.

## Frame existence formalization added (pending CI)

The new file lean/Research/SmoothRicciFrameExistence.lean assembles the
upstream local orthonormal frame construction and globally smooth
bump-section extension:

1. Apply a C2 Gram-Schmidt procedure to a local trivialization's
   standard model-space basis.
2. For each of finitely many basis indices, obtain a globally C2
   section agreeing with the local frame near the chosen point,
   using GlobalExtension.exists_contMDiff_eventuallyEq.
3. Shrink to a common open neighbourhood using finite intersection
   of all eventual equalities, so the extended frame remains
   orthonormal on this neighbourhood.
4. Apply the frame-dependent smooth divergence theorem to this
   constructed frame.

The resulting intended theorem
SmoothRicciFrameExistence.levi_civita_ricci_flat_yang_mills
has no additional arbitrary local-frame assumption: for any x,
Ricci-flat C3 Riemannian metric yields zero divergence of the actual
Levi-Civita curvature. Source has been added, but this theorem must be
considered **unverified until its own exact-head kernel CI succeeds**.

This does not provide a Lorentzian generalization or a physical
independent gauge-boson theory.

## Verification

Dedicated pinned Lean --trust=0 CI explicitly compiles every required
module in dependency order and audits the genuine smooth divergence
and final wrapper. Independent exact finite tensor checks are also run.
Do not claim CI success, or mathematical completion, until exact-head
checks pass. The full source snapshot and HEAD SHA are retained.

No new physical Standard Model force, gauge boson or quantum matter is
inferred. The result is about the induced Levi-Civita connection.
