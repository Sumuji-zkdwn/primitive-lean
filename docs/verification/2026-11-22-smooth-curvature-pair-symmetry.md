# Levi-Civita covariant Riemann pair symmetry in a real frame

Date: 2026-11-22 JST. Dependent DRAFT based on #190 -> #189 -> #188 -> #187 -> #186.

## Concrete target

PR #190 uses the actual smooth Mathlib Levi-Civita connection to construct real-valued components D[e,a,b,c,d] and proves the contracted Bianchi identity, but still requires Riemann pair-exchange and parallel Ricci to conclude the Yang-Mills divergence equation.

This PR targets **only the pair-exchange** condition. It port-adapts a small, trace-independent portion of the existing Apache-2.0 RicciFlowBlueprint formalization to prove:
- curvature skew-adjointness for metric-compatible connections,
- the first algebraic Bianchi identity and Riemann pair symmetry,
- pair symmetry of the actual covariant curvature derivative,
- a real-index tensor representation with literal pair-exchange symmetry.

The exact prior sources (upstream commit c8017e2c26898d11f39cec0dfce89368d5a0506a) are:
- RicciFlowBlueprint/Sectional.lean
- RicciFlowBlueprint/CurvatureSymm.lean
- RicciFlowBlueprint/Divergence.lean, specifically inner_covCurvature_expand and inner_covCurvature_pair_symm.
The original source authors and Apache-2.0 license are retained through the dependency PR #188; proof bodies are adapted and renamed into explicit independent bridge declarations, not presented as original mathematics.

## Important index ordering

The real component tensor in #190 is D[e,a,b,c,d]=inner((nabla_e R)(fr_c,fr_d)fr_b,fr_a). Under the standard Riemann pair-exchange formula, the convenient tensor is the dual component ordering

    Ddual[e,a,b,c,d] = D[e,b,a,c,d]
       = inner((nabla_e R)(fr_c,fr_d)fr_a, fr_b).

Then pair exchange becomes the literal equality:

    Ddual[e,a,b,c,d]=Ddual[e,c,d,a,b].

The uncontracted second Bianchi and last-pair skewness persist under swapping a,b. This is a harmless algebraic reindexing, not an additional physical field.

## Mathematical gain

With second Bianchi, last-pair skew and pair exchange now proved for the *same actual* smooth Levi-Civita component tensor, the standard real tensor contraction gives

    YMdiv[a,b,d]
       = (nabla_a Ric)[d,b] - (nabla_b Ric)[d,a].

The conclusion YMdiv=0 is still conditional on **parallel frame Ricci**. The pair-exchange hypothesis is no longer a free extra premise. The remaining task is identifying this finite frame trace with the smooth Ricci covariant derivative and discharging its vanishing from global Ricci-flatness.

The chosen global smooth family of frame fields is not required to be orthonormal. A genuine Ricci trace requires a pointwise/local orthonormal basis and frame independence; this is the next formalization obstacle. The proof is for Riemannian metrics, not yet pseudo-Riemannian Lorentzian signatures.

## Verification

The exact-head workflow must compile all parent dependencies, the new pair-symmetry proof with Lean --trust=0, print axiom dependencies and run independent rational curvature metric jets. No sorry or custom axioms. Do not claim success until CI confirms it. No main auto-merge.

Prior source:
https://github.com/korbonits/ricci-flow-blueprint/blob/c8017e2c26898d11f39cec0dfce89368d5a0506a/RicciFlowBlueprint/Divergence.lean
