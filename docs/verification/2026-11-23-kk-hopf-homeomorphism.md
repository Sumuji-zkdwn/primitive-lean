# Attempted topological Hopf quotient equivalence

Date 2026-11-23. This is an independent stacked Draft PR based on #226, whose prior CI has established (a) Hopf S³→S² surjectivity, (b) set-theoretic quotient equivalence with the true diagonal U(1) orbit relation, and (c) explicit north/south pointwise sections and phase uniqueness.

This PR attempts the next known topological result:

  (S³ / U(1), quotient topology) ≅ₜ S².

The proof strategy is to give the set-theoretic orbit quotient the coinduced topology used by Mathlib's Quotient type. Then prove:

1. S³ is compact, by viewing it as the closed polynomial level-set |X|²=1 inside the finite product compact cube [-1,1]^4.
2. The Hopf map is continuous, because all three coordinates are polynomials in four real coordinates.
3. The induced function from the quotient to the Hausdorff sphere S² is continuous by the quotient topology.
4. The prior kernel-checked equivalence upgrades to a homeomorphism by Mathlib's compact-to-T2 continuous-equivalence theorem.

This is a new Lean proof candidate until its actual dedicated pinned trust-zero CI completes. No analytic trigonometric inverse is assumed and the quotient topology is not defined ad hoc on the base.

**Scope:** A homeomorphism of orbit quotient and S² is not a smooth diffeomorphism, a Lean principal-bundle local trivialization, a proof that the Hopf transition has Chern number ±1, or a metric reduction/EMD curvature theorem. The base still uses the concrete polynomial unit sphere rather than Mathlib's abstract sphere bundles.

Keep Draft, no merge. Existing PRs #199, #215, #219, #222, #225, #226 and main untouched.
