# Smooth second Bianchi port from an actual manifold covariant derivative

Date: 2026-11-22 JST.
Depends on PR #187 (and transitively #186). This is a **dependent draft** intended to add tested smooth geometric content without deleting existing proofs.

## Source provenance and license

External upstream source: https://github.com/korbonits/ricci-flow-blueprint
Pinned commit: c8017e2c26898d11f39cec0dfce89368d5a0506a
Upstream files, unmodified at initial import:
- RicciFlowBlueprint/LieBracketDerivation.lean
- RicciFlowBlueprint/Curvature.lean
- RicciFlowBlueprint/Bianchi.lean

They are copied to lean/RicciFlowBlueprint/ and retain the original module names / import dependencies. Copyright and credit remain with the original authors, as covered by the original Apache-2.0 license, copied to licenses/ricci-flow-blueprint-Apache-2.0.txt. Any compatibility changes, if needed, should be itemized in this note and should not be misrepresented as original derivations.

## Pinned mathlib compatibility patch

On the pinned mathlib revision, `CovariantDerivative.isCovariantDerivativeOn` is generalized to an arbitrary, implicitly inferred subset of the manifold. This makes upstream proof calls ambiguous (`Set M` remains a metavariable). The ported `Curvature.lean` therefore replaces **27 occurrences** of `cov.isCovariantDerivativeOn.` by the original bundled global law `cov.isCovariantDerivativeOnUniv.`. The latter has the same `Set.univ` geometric meaning and avoids any extra mathematical premise. This change is confined to the upstream compatibility layer; the source SHA and exact replacement count are recorded for auditing.

Upstream project toolchain at this SHA: Lean 4.34.0-rc2 with mathlib master (not pinned).
Target primitive-lean toolchain: Lean 4.36.0-rc2, mathlib 2ddf59c8f14245864e6c0ed227a2dab76b9efea2.
Port to this target requires exact-head CI verification.

## What the upstream smooth proof actually states

For the mathematically genuine covariant derivative on the tangent bundle, the *external* upstream theorem CovariantDerivative.bianchi_second proves

  (∇_X R)(Y,Z)W + (∇_Y R)(Z,X)W + (∇_Z R)(X,Y)W = 0

under
- torsion-free connection,
- C^1 and C^2 regularity of the connection in the form of ContMDiffCovariantDerivative instances,
- C^2 vector fields X,Y,Z, and C^3 vector field W.

The curvature is *defined by the connection*:

  R(X,Y)W = ∇_X∇_Y W − ∇_Y∇_X W − ∇_[X,Y] W.

Its covariant derivative is defined in the usual 4-term tensor rule. Upstream proves the differential second Bianchi using expansion, torsion-freeness, and the Jacobi identity for vector fields. Unlike the preceding finite-matrix proof, the result includes variable smooth fields and their derivatives.

Our new wrapper Research/SmoothLeviCivitaBianchi.lean imports the actual pinned Mathlib Levi-Civita construction and instantiates its torsion-free theorem. The result levi_civita_second_bianchi is a genuine *manifold-level* second Bianchi theorem for the actual Levi-Civita connection.

### Still conditional on smoothness of the constructed connection

The pinned mathlib Levi-Civita file explicitly notes that it does not yet prove the connection has the appropriate C^n regularity even for a sufficiently smooth metric. The wrapper thus exposes ContMDiffCovariantDerivative (leviCivitaConnection I M) 1 and 2 as additional *explicit assumptions*. It does not assert that these assumptions are automatically solved by arbitrary mathlib RiemannianBundle instances.

### Further remaining bridge to Yang–Mills

PR #186 proves that (i) uncontracted second Bianchi + (ii) the Levi-Civita Riemann tensor symmetries, (iii) metric-commuting Ricci contraction + (iv) globally Ricci-flat conditions give the Yang–Mills divergence equation, in finite pseudo-orthonormal frame components. The actual smooth Bianchi in this PR and that finite contraction live in different tensor representations.

Proving their equivalence requires (1) tensoriality of the covariant-curvature expression and orthonormal frame conversion; (2) smooth pair-exchange curvature symmetry; (3) commutation of Ricci trace with the covariant derivative; (4) the zero Ricci field's derivative. Those statements are **not** automatically inferred from matching mathematical names and are not yet a completed theorem in pinned mathlib.

Therefore the present port should be described as "smooth second Bianchi applied to actual Levi-Civita, conditional on connection smoothness", not yet the full unconditional manifold RicciFlat => Yang--Mills theorem.

## Reproducible entrypoints

- lean/Research/SmoothLeviCivitaBianchi.lean: direct theorem using the actual Mathlib constructed Levi-Civita.
- lean/RicciFlowBlueprint/{LieBracketDerivation,Curvature,Bianchi}.lean: upstream source proofs.
- .github/workflows/smooth-levicivita-bianchi.yml: strict lean --trust=0, axiom audit, dependency SHA record. No changes to main and no automatic merging.

References:
- https://github.com/korbonits/ricci-flow-blueprint/blob/c8017e2c26898d11f39cec0dfce89368d5a0506a/RicciFlowBlueprint/Bianchi.lean
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.html
