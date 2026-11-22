# Second Bianchi -> Ricci-flat Levi-Civita spin connection solves Yang--Mills

Date: 2026-11-22 JST. Scope: **complete algebraic contraction in Lean**, with
standard geometric properties of a Levi-Civita connection stated as hypotheses.
No fully kernel-checked construction of the smooth connection, Riemann curvature,
or its second Bianchi identity from the manifold API is asserted.

## Precise tensor statement and sign conventions

Let (M,g) be a smooth pseudo-Riemannian manifold, with Levi-Civita connection
nabla, Riemann curvature R_{a b c d} in a local pseudo-orthonormal frame, and
inverse-metric weights eps_i=+1 or -1 (so eps_i²=1). Write

  D[e,a,b,c,d] = (nabla_e R)_{a b c d}.

The assumptions are:
1. Differential (second) Bianchi:
   D[e,a,b,c,d] + D[c,a,b,d,e] + D[d,a,b,e,c] = 0.
2. Covariant derivative of Riemann is skew in its final pair:
   D[e,a,b,c,d] = -D[e,a,b,d,c].
3. Pair-exchange curvature symmetry preserved by covariant derivative:
   D[e,a,b,c,d] = D[e,c,d,a,b].
4. Metric compatibility of contraction:
   (nabla_e Ric)_{b d} = sum_i eps_i D[e,i,b,i,d].
5. The covariant derivative of a Ricci *field* is linear, in particular
   nabla(0) = 0. This distinguishes an everywhere Ricci-flat metric from
   a Ricci tensor that happens to vanish at one point.

We prove in Lean (not assumed):

  sum_i eps_i D[i,i,b,c,d]
     = (nabla_c Ric)_{b d} - (nabla_d Ric)_{b c}.

Using pair exchange, this becomes the *properly indexed* gauge-curvature
divergence (base curvature indices c,d, not skew-endomorphism indices a,b):

  YangMills_{a b d} := sum_i eps_i D[i,a,b,i,d]
                    = (nabla_a Ric)_{d b} - (nabla_b Ric)_{d a}.

Consequently, if Ric=0 globally on M, the Ricci-field derivative is zero
by linearity; thus YangMills_{a b d}=0 everywhere. This is the source-free
Yang--Mills equation for the curvature of the Levi-Civita connection viewed
as a connection on the tangent/orthonormal-frame bundle.

The intermediate theorem for a parallel (not necessarily zero) Ricci tensor
also holds. No Einstein equations are required for the *contracted Bianchi*
identity, though Ricci-flatness is a gravitational field-equation condition
in the vacuum Lambda=0 case.

## What Lean checks and what remains an external input

Lean file: lean/Research/RicciFlatBianchiYangMills.lean

- Universal finite rank n, any signature weights eps (the proof does not
  rely on eps_i=1, and a geometric interface records eps_i²=1).
- Proves the nontrivial contraction of the original cyclic second Bianchi.
- Proves pair-exchange of the divergence contraction to the correct YM slots.
- Proves parallel-Ricci => YM.
- Models the covariant derivative on the global Ricci field as a Q-linear
  map, then proves global RicciFlat => YM from d0=0.
- Exhibits a finite **fake curvature derivative** with zero Ricci
  derivative, nonzero first-pair divergence and failing Bianchi, showing
  why the differential identity cannot simply be omitted.

The Lean structure BianchiConnectionData is an *explicit conditional
interface* for the standard Levi-Civita geometric facts. We have not yet
constructed an instance for a manifold's actual
CovariantDerivative.leviCivitaConnection in pinned mathlib, nor formally
proved that connection's 2nd Bianchi identity and all symmetries using
mathlib's bundle/tensor machinery. The claim "full differential geometry
in Lean" is therefore **not** established in this PR. No custom axiom or
sorry is introduced to conceal that gap.

Independent Python oracle: tools/check_ricci_flat_yang_mills.py

- Uses exact integer/fraction arithmetic, constructs third derivatives of
  a metric in normal coordinates and directly verifies original second
  Bianchi, skew, pair exchange, contraction identities for multiple
  signatures and dimensions 2/3/4.
- Tests a nonzero (nabla R) jet with vanishing Ricci derivative, arising from
  a transverse-traceless *linearized* vacuum plane wave perturbation
  h_xx=-h_yy=(t-z)^3/6 at the origin in Lorentz signature.
  This is a nontrivial jet-level witness, **not** a full nonlinear exact
  vacuum gravitational-wave solution.
- Checks the counterexample if Bianchi is dropped.
- Requires only Python stdlib.

CI: .github/workflows/ricci-flat-bianchi-yang-mills.yml pins Lean v4.36.0-rc2
and the repository mathlib revision, verifies source with --trust=0,
audits theorem axioms, and runs the independent Python oracle against the
exact PR head. CI status should be inspected and the PR kept DRAFT.

## Relation to Taub--NUT and gravity-only restoration

Draft PR #185 separately computed, with exact SymPy, the non-Abelian
SU(2)-type holonomy and vanishing Ricci of the Taub--NUT spatial metric.
Combining that Ricci-flat result with the *external* standard
differential-geometric second Bianchi theorem proves that its induced
Levi-Civita/spin connection satisfies YM. However, this logical link is
**not yet fully formalized as a smooth manifold Lean theorem**.

The spin connection here is *determined by* the chosen metric. Solving the
Yang--Mills equation for this induced connection does not produce a new
independent propagating 4D weak SU(2) gauge field, its coupling to chiral
fermions, or observed Standard Model particle content.

## References

- Mathlib Levi-Civita connection API:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.html
- Standard differential Bianchi identity and tensor symmetry conventions:
  https://www.sissa.it/tpp/phdsection/OnlineResources/4037/SISSA_Groups_course_MS_2025.pdf
- Independent Ricci-flow formalization with additional Bianchi developments:
  https://github.com/korbonits/ricci-flow-blueprint
