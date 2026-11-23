# Smooth Levi-Civita curvature to real-index Bianchi contraction

Date 2026-11-22 (JST). Dependent draft built on PR #189, which depends on #188, #187 and #186. No main merge.

## New formal bridge

PR #186 proved contracted Bianchi using an abstract rational-component array. PR #189 proved actual smooth second Bianchi for the real Levi-Civita covariant curvature under a C3 Riemannian metric. We must not simply coerce the real curvature tensor to rational coefficients.

The new Lean file constructs a real-valued frame tensor from a chosen C3 family of vector fields fr_i:

    D[e,a,b,c,d](x) =
       inner_R ((nabla_{fr_e} R)(fr_c,fr_d) fr_b at x) (fr_a(x)).

From the established smooth-manifold Bianchi theorem, it proves the **exact original second Bianchi identity** for D, by applying the inner product to the cyclic vector equality. It also proves antisymmetry in the final two slots from the smooth curvature definition and the differentiability of curvature sections; the latter proof is adapted from the Apache-2.0 upstream CurvatureDeriv.lean.

Next the actual real-valued frame tensor obeys:

    sum_i D[i,i,b,c,d]
      = sum_i D[c,i,b,i,d] - sum_i D[d,i,b,i,c].

Finally, if pair exchange D[e,a,b,c,d]=D[e,c,d,a,b] and parallel frame Ricci sum_i D[e,i,b,i,d]=0 hold, the proper Yang-Mills divergence sum_i D[i,a,b,i,d] vanishes. The latter two hypotheses are still stated explicitly, but full second Bianchi and skewness are **derived, not assumed**, from the actual Levi-Civita curvature.

## Boundary

This is a concrete smooth-manifold-to-component contraction, not yet an unconditional theorem that Ricci-flat geometry gives Yang-Mills on a smooth manifold. It requires:

1. Pair-exchange symmetry of the covariant curvature derivative, available upstream as CovariantDerivative.inner_covCurvature_pair_symm in Divergence.lean, with additional dependencies.
2. Identification of the finite real Ricci trace with the derivative of the actual Ricci field. The upstream theorem CovariantDerivative.sum_inner_covCurvature_eq is relevant.
3. Orthonormal local frames and independence from the arbitrary choice of vector fields. The current frame family is globally defined for convenience, and it is not required to be orthonormal; only under such a condition does its trace equal the geometric Ricci trace.
4. Ricci-flat => parallel Ricci from the linearity of the actual field derivative.
5. A separate pseudo-Riemannian/Lorentzian generalization, since current Mathlib input is Riemannian.

## Provenance and verification

Sources: earlier PR #186 and #189. The short smooth curvature regularity/skew argument is adapted from the external Apache-2.0 formalization at immutable commit c8017e2c26898d11f39cec0dfce89368d5a0506a, source:
https://github.com/korbonits/ricci-flow-blueprint/blob/c8017e2c26898d11f39cec0dfce89368d5a0506a/RicciFlowBlueprint/CurvatureDeriv.lean

The license accompanies PR #188 in the transitive dependency.
All proofs require pinned Lean --trust=0 compilation, axiom audit and independent metric-jet oracle. Do not mark as proved until exact-head CI succeeds. The PR remains a draft without auto-merge.
