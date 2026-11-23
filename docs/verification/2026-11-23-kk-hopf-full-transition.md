# Full north/south Hopf overlap phase — exact local chart identity

Date: 2026-11-23 JST. Stacked on Draft PR #231 (proven north and
south topological Homeomorphs); upstream and main remain unchanged.

## Result under test

For a point (u,v,w) on the unit S², with -1<w<1, let
D_N = sqrt(2(1+w))>0, D_S=sqrt(2(1-w))>0. Define
C=2u/(D_N D_S), S=-2v/(D_N D_S).

The normalized north/south sections from PR #226 satisfy

    C²+S²=1,
    rotate(C,S,northVec(u,v,w))=southVec(u,v,w)

component by component. Since D_N D_S=2 sqrt(u²+v²),
the phase is equivalently

    (C,S)=(u,-v)/sqrt(u²+v²).

This is valid over **the entire intersection**, not only the equator
w=0. On the equator the formula specializes to the prior kernel
certificate KKHopfEquator.equator_transition.

## Formalization boundary

KKHopfTransitionAlgebra.lean proves the rational algebraic rotation
identity under generic nonzero square-root denominators with squared
norm identities and instantiates the actual Real.sqrt expressions.
A pinned trust-zero, individual axiom audit, and independent exact
SymPy polynomial oracle are attached.

Even a successful compile is NOT a winding-number or Chern-class
computation in Lean. The classical transition on the equator is
complex conjugation and has winding degree -1, but that topology
statement remains an explicit open obligation. Neither the
smooth principal U(1)-bundle atlas nor general GH/EMD curvature
reduction is completed by this algebraic overlap calculation.

Keep DRAFT. Do not merge automatically.
