# Exact vacuum-to-magnetic-field reconstruction from twisted 5D geometry

Date: 2026-11-22 (JST).
Status: independent SymPy exact-check PASS locally; Lean kernel compilation/axiom audit pending until exact-head CI completes.

## Why this is stronger than the constant-E toy

The earlier model \`-dt²+dx²+(dy+Exdt)²\` gives the Lorentz-force kinematics but has nonzero Ricci scalar \`E²/2\`: it is not a vacuum Einstein solution. The following exact **twisted compactification of flat 5D spacetime** is a nontrivial vacuum example whose 4D reduction carries a nonzero Maxwell-like field. It is an established Kaluza–Klein Melvin construction, not an original discovery.

## Start with only a single 5D metric

Use the locally flat five-dimensional Minkowski metric in cylindrical coordinates \`(t,z,r,phi,y)\`. Define Cartesian coordinates by

    X = r cos(phi + B y),   Y = r sin(phi + B y),   W=y.

The pullback of \`-dt²+dz²+dX²+dY²+dW²\` is

    ds5² = -dt² + dz² + dr² + r²(dphi+B dy)² + dy².

Since it is a local diffeomorphic pullback of Minkowski, the entire 5D Riemann tensor vanishes wherever polar coordinates are regular. Thus it satisfies the **vacuum** Einstein equations exactly. Global helical identifications along a compact y circle are indispensable for the nontrivial quotient description; without specifying the quotient this is just a change of coordinates.

Define \`Lambda(r)=1+B²r²\`. Square completion gives

    ds5² = h_mu_nu dx^mu dx^nu
            + Lambda(r) [dy + C_phi(r) dphi]²,

    h = -dt² + dz² + dr² + [r²/Lambda] dphi²,
    C_phi = B r²/Lambda,   phi_fibre² = Lambda.

In a common physics convention the electromagnetic potential \`A_phi=C_phi/2\`; here we consistently use the geometric connection \`C\` with no factor of 2.

The connection is **not flat** on the four-dimensional quotient:

    F_rphi = d(C_phi)/dr = 2Br/(1+B²r²)².

Thus a vacuum solution of a single gravity-only theory produces a nonzero, gauge-invariant geometric field after reduction. The circle radius also varies with r, so the scalar/radion constraint is included rather than discarded.

## Independently checked reduced equations

For the 4D Jordan metric \`h\`, \`sqrt(|h|)=r/sqrt(Lambda)\` for r>0. Put \`phi=sqrt(Lambda)\`; then

    F^{rphi} = 2B/(r Lambda),
    sqrt(|h|) phi³ F^{rphi} = 2B,

hence \`partial_r[sqrt(|h|) phi³ F^{rphi}]=0\`, exactly the vacuum Maxwell-type field equation in this reduction (up to the conventional normalization of A).

The scalar-curvature identity is independently checked:

    R(h) = 6 B²/Lambda²,
    F_mu_nu F^{mu_nu} = 8 B²/Lambda³,
    Box_h phi = 2B²/Lambda^(3/2),
    R5 = R(h) - phi² F²/4 - 2(Box_h phi)/phi = 0.

The full 5D vacuum Einstein equations follow from the Cartesian pullback; the checked 4D identities are independent cross-checks, not a full 4D tensor-component audit.

## Relation to the user's dual-distance and observer ideas

The observed 4D metric h and the proper circle-fibre radius \`phi=sqrt(Lambda)\` are not a single uniform notion of distance. The 4D observer sees a magnetic field, while the higher-dimensional description is a locally flat metric and a twisted projection. This gives a precise case of **different valid descriptions connected by explicit transformation rules**. It does not imply that the 4D electromagnetic field is an illusory force; it is a genuine, gauge-invariant field of the reduced dynamics.

The surface/field is not yet a reconstruction of elementary matter, spinors, nuclear forces, quantum mechanics, or an observed Standard Model spectrum. The high-dimensional circle and its compactification rules remain additional assumptions. Gravity alone here means one *high-dimensional* metric and Einstein dynamics, not the 4D metric alone.

## Reproducibility and theorem map

- \`lean/Research/TwistedFlatReduction.lean\`: positive \`Lambda\`, exact square completion after clearing denominator, connection and curvature algebra, nonzero curvature at B=r=1, orientation sign reversal.
- \`tools/check_twisted_flat_reduction.py\`: exact 5D Cartesian pullback, 4D connection and its derivative, Maxwell-dilaton divergence, scalar-curvature identity, no floating-point tolerance.
- \`.github/workflows/twisted-flat-reduction.yml\`: Lean kernel verification, axiom audit, independent symbolic checker; exact-head CI result to be checked.
- Existing \`lean/Research/GeometricCharge.lean\` addresses particle-geodesic projection separately.

## References

- F. Dowker, J. Gauntlett, G. Gibbons, G. Horowitz, "The Decay of Magnetic Fields in Kaluza-Klein Theory" (1995), https://arxiv.org/abs/hep-th/9507143 .
- J. M. Overduin and P. S. Wesson, "Kaluza-Klein Gravity", Physics Reports 283 (1997), https://arxiv.org/abs/gr-qc/9805018 .
- For the lower-dimensional dilaton coupling, see the 1995 Dowker et al. paper, eqs. (2.3)-(2.6).

## Next actual barrier

Prove dynamically consistent emergence of nonabelian gauge fields and a chiral fermion sector using **only specified gravitational degrees of freedom and stated topological/quantum assumptions**, while retaining the actual Standard Model couplings and anomaly cancellation. Neither this demonstration nor a holonomy algebra identity proves such a result.
