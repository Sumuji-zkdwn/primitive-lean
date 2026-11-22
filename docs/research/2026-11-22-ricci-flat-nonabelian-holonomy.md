# A Ricci-flat gravitational metric with non-Abelian SU(2)-type holonomy

Date: 2026-11-22 (JST). This is a new exact verification of a known geometry, **not** a discovery of a new physical force.

## Objective

Test the gravity-only program from earlier PR #181 (Ricci-flat Kaluza--Klein magnetic monopole) and PR #182 (multi-centre observer equivalence) against the next hurdle: can a metric alone produce a non-Abelian geometric connection? Distinguish (A) non-Abelian **Levi-Civita holonomy** and a derived Yang--Mills solution, from (B) independent propagating four-dimensional Standard Model SU(2) gauge bosons.

## Single metric and exact point

The 5D Lorentzian metric is -dt² plus the four-dimensional Euclidean Taub--NUT / one-centre Gibbons--Hawking metric,

    ds4² = H (dr² + r² dθ² + r² sin²θ dφ²)
           + H^-1(dψ + cosθ dφ)²,
    H = 1 + 1/r.

At the regular point (r,θ)=(1,π/2), its coordinate metric (r,θ,φ,ψ) is

    G = diag(2,2,2,1/2).

This is locally Ricci-flat, and a standard complete hyperkähler gravitational instanton after the usual period and gauge patches. The independent SymPy oracle differentiates the *original metric* to second order and computes all six Riemann curvature endomorphisms R_cd^a_b using the full Christoffel formula. Nothing about a Yang--Mills connection is independently input.

The three generators X=R_01, Y=R_02, Z=R_03 are

    X = [[0,-1/8,0,0],[1/8,0,0,0],[0,0,0,1/16],[0,0,-1/4,0]]
    Y = [[0,0,-1/8,0],[0,0,0,-1/16],[1/8,0,0,0],[0,1/4,0,0]]
    Z = [[0,0,0,1/16],[0,0,-1/8,0],[0,1/8,0,0],[-1/4,0,0,0]].

The remaining components obey R_12=-2Z, R_13=Y/2, R_23=-X/2, so the six operators span precisely three independent directions.

With the matrix commutator [A,B]=AB-BA, exact rational arithmetic gives

    [X,Y]=Z/4,  [Y,Z]=X/4,  [Z,X]=Y/4

with [X,Y]_0,3=1/64 ≠ 0. Each endomorphism is metric-skew (X^T G+G X=0, etc.). Their real span is a compact three-dimensional non-Abelian Lie algebra isomorphic to su(2) or so(3). This statement is **geometric**, not an independent postulated Yang--Mills gauge symmetry.

The oracle also checks every Ricci component exactly equals 0 while the coordinate-invariant Kretschmann scalar at the chosen point is

    R_abcd R^abcd = 3/8 > 0.

Thus the vacuum condition Ric=0 does not imply flatness or trivial parallel transport.

## What follows (and what doesn't)

The Ambrose--Singer holonomy theorem states that curvature endomorphisms, transported to the reference point, generate the Lie algebra of the restricted holonomy group. Our three noncommuting curvature operators therefore exhibit non-Abelian holonomy. Since the one-centre Taub--NUT metric is hyperkähler, its Levi-Civita holonomy is contained in SU(2); its nonzero three-dimensional curvature span makes the holonomy Lie algebra exactly su(2), assuming the standard global/connectedness premises.

Moreover, the contracted second Bianchi identity implies

    ∇^a R_abcd = ∇_c Ric_bd - ∇_d Ric_bc = 0

when Ric=0. Therefore the Levi-Civita spin connection can be viewed as an induced solution of the source-free Yang--Mills equation on the tangent/spin bundle, with structure algebra so(4) and a nontrivial su(2) sector. This is a **known relation** between Einstein metrics and Yang--Mills connections. We have not formalized Ambrose--Singer, the covariant Bianchi identity, or smooth spin-bundle construction in Lean. Their application here is a mathematical derivation based on established external theorems.

This result does NOT by itself generate an independent dynamical four-dimensional SU(2) gauge field, a local Yang--Mills action with freely variable gauge bosons, or its coupling to chiral weak-interaction fermions. The non-Abelian connection is determined by a fixed metric; the SU(2) is acting on **tangent/spin frames of the four-dimensional internal geometry**, not automatically on the observed Standard Model doublets. Changing these representations, dynamics, and low-energy particle content is precisely the unsolved part of gravity-only reconstruction.

## Reproducible verification

- lean/Research/RicciFlatSU2Holonomy.lean: exact rational 4×4 curvature matrices at a fixed point, three commutators, their nontriviality, positive-metric skewness, and independence of the three generators. It does NOT claim to derive metric derivatives or field equations in the Lean kernel.
- tools/check_gh_holonomy.py: independently computes all derivatives from the explicit original Taub--NUT metric, six curvature endomorphisms, zero Ricci tensor, nonzero Kretschmann scalar, rank-three span, and all commutators in SymPy with no floating-point calculations.
- .github/workflows/ricci-flat-su2-holonomy.yml: pinned exact-head Lean --trust=0 typecheck, axiom audit and independent symbolic oracle.
- Prior implementation: draft PR #181 (Ricci-flat U(1) KK monopole) and #182 (multiple centres); new module is standalone and does not import either draft PR.

## Next sharply scoped test

A proposed "gravity-only weak interaction" would need a map from *variations of this same five-dimensional metric* to independent four-dimensional SU(2) gauge-field fluctuations, with their kinetic term, gauge covariance, and constraints derived from the Einstein--Hilbert action. Absent such a map, the present geometrized SU(2) is a curved-frame effect, not a reconstruction of weak interactions.

## References

- Gibbons--Hawking ansatz and hyperkähler Ricci-flatness: Dunajski, Gundry, https://www.damtp.cam.ac.uk/user/md327/DG_CMP_published.pdf .
- Example of Taub--NUT interpreted as an SU(2) Yang--Mills connection on the tangent bundle: https://link.springer.com/article/10.1007/s00220-025-05311-8 .
- Etesi, classification of 't Hooft instantons on multi-centred gravitational instantons: https://www.sciencedirect.com/science/article/abs/pii/S0550321303003778 .
- Ambrose--Singer holonomy theorem: standard differential geometry theorem; distinct from the finite arithmetic proved in Lean.
