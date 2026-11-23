# Hopf fibre completeness: algebraic proof before global quotient

Parent: draft PR #222. This follow-on is additive and does not change `main`.

## Claim

Let X,Y be unit vectors in R^4. Write

    h(X) = (2(X0 X2+X1 X3), 2(X0 X3-X1 X2),
            X0^2+X1^2-X2^2-X3^2).

Then `h(X)=h(Y)` if and only if there exist real C,S with
`C^2+S^2=1` and `Y=rotate(C,S,X)`, where the rotation multiplies both
complex coordinate pairs by the same unit phase.

Previous Lean code formalized *invariance* (an orbit maps to one base
point), whereas this theorem proves the missing *fibre completeness*
(equal base points are in one orbit) with explicit local witnesses.

## Algebraic reconstruction

If `N=X0^2+X1^2 != 0` use

    C=(X0 Y0+X1 Y1)/N
    S=(X0 Y1-X1 Y0)/N.

The unit norms and equality of third Hopf coordinates imply
`N=Y0^2+Y1^2`. Equality of the first two Hopf coordinates then gives
`C*X2-S*X3=Y2` and `S*X2+C*X3=Y3`. The identity

    (X0 Y0+X1 Y1)^2+(X0 Y1-X1 Y0)^2
      =(X0^2+X1^2)(Y0^2+Y1^2)=N^2

shows that `C^2+S^2=1`. If N=0, the unit sphere condition ensures
`X2^2+X3^2 != 0`, and the same reconstruction works with complex
pairs interchanged. This is entirely algebraic; no choice of arguments,
trigonometric inverse, or local section is needed.

## Verification and boundary

- `KKHopfOrbit.lean` proves `phase_from_first`,
  `same_hopf_implies_unit_rotation`, and `same_hopf_iff_circle_orbit`.
- The independent SymPy script verifies all five polynomial identities
  and the algebraic rotation invariances without random sampling.
- Dedicated repository-pinned `lean --trust=0`, axiom audit and SymPy CI
  must pass before counting these as formally verified.

This is **not** yet a Lean topological quotient/homeomorphism theorem
`S^3/U(1) ≅ S^2`, a smooth principal-bundle atlas, a degree/winding
calculation, or an analytic general GH / EMD curvature identity.
It removes one exact algebraic gap needed for the quotient theorem.

## Free action and orthogonality

KKHopfActionFree.lean adds three algebraic theorems:

- The real inner product of a unit vector and its diagonal-rotated image
  is exactly C*|X|^2;
- Applying the same rotation to both arguments multiplies any real
  four-dimensional inner product by C^2+S^2, so unit rotations
  preserve inner products;
- If |X|^2=1, C^2+S^2=1, and rotate(C,S,X)=X, then C=1 and S=0.
  Thus the diagonal circle action is **free** on S^3.

Together with fibre completeness, these identify Hopf fibres
set-theoretically as free circle orbits. They do **not** by themselves
construct a smooth principal bundle, smooth manifold quotient,
homeomorphism/diffeomorphism to S^2, or transition winding/Chern class.
