# Southern Hopf local homeomorphism by transport from the north

2026-11-23 JST. Stacked on Draft PR #230 (north local Homeomorph); retain Draft, no merge to main or edits to parent PRs.

## Main observation

Write X=(Re z1,Im z1,Re z2,Im z2) on S3. Exchanging the two complex
pairs defines J(X)=(X2,X3,X0,X1). The Hopf base map satisfies

  Hopf(J(X)) = (u,-v,-w) when Hopf(X)=(u,v,w).

In particular J is a polynomial involution preserving the S3 norm,
and J commutes with the diagonal circle action. The base reflection
j(u,v,w)=(u,-v,-w) is a homeomorphism of S2 interchanging the two
open hemispherical chart domains B_N={1+w>0} and B_S={1-w>0}.

Since the existing KKHopfNorthHomeo.northHomeomorph is an actual
Homeomorph E_N ≃ₜ B_N × U(1), transporting it through the induced
homeomorphisms J:E_S ≃ₜ E_N and j:B_S ≃ₜ B_N constructs the genuine

  KKHopfSouthHomeo.southHomeomorph : E_S ≃ₜ B_S × U(1).

No new global topology is assumed: this is a concrete re-use of the
north-chart theorem and Lean's product homeomorphism composition.
The maps are written on the actual subtype patches, not on arbitrary
unconstrained Euclidean space.

## Independent checks

The polynomial SymPy script checks that the pair exchange is an
involution, preserves the S3 norm, interchanges the appropriate Hopf
coordinates, commutes with circle rotations, and swaps north/south
patch conditions. The dedicated workflow compiles the exact dependency
chain with pinned Lean --trust=0, audits each new theorem and the
exported southern and northern Homeomorph definitions, and runs SymPy.

Kernel guarantee is NOT asserted before the exact-head Actions run
reports success.

## Boundaries

This proves the existence of both *topological* local trivializations.
The following are still separate formalization obligations:
- explicit overlap Homeomorph and transition formula over the entire
  equator-complement domain (the earlier PR #227 proved the equator case);
- smoothness in compatible differentiable manifold charts, and a
  Mathlib smooth principal U(1)-bundle structure;
- winding number/Chern class -1 in Lean;
- fully general GH Ricci and 5D->4D EMD tensor reductions in Lean.

The standard principal-bundle picture follows mathematically from
topological trivializations and overlap data, but this file does not
claim a completed differentiable bundle or Chern class theorem.
