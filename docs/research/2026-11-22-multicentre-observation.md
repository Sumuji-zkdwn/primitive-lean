# Multi-centre vacuum gravity and the observer-dependent number of objects

Date: 2026-11-22 JST. Status: research draft. The standard Gibbons--Hawking construction is prior mathematics. This PR adds an independent symbolic verification of its 2-centre hypotheses and an exact finite/asymptotic observer discrimination certificate; no new field equation is claimed.

## Problem

The user proposes defining a "physical object" by its gravitational effects rather than presupposing material particles. Can one gravity-only solution display a single entity to a coarse external observation but several distinguishable geometric centres to a more sensitive observer?

## One vacuum metric, two distinct centres

The five-dimensional metric is a time factor (-dt²) times a four-dimensional Gibbons--Hawking hyperkähler metric

    ds5² = -dt² + H(x) (dx² + dy² + dz²)
           + H(x)^(-1) (dpsi + A)².

Take positive charge q and distinct centres at (0,0,+a), (0,0,-a), with a>0:

    r_± = sqrt(rho²+(z∓a)²),
    H = 1 + q/r_+ + q/r_-,
    A = q[(z-a)/r_+ + (z+a)/r_-] dphi.

Here rho=sqrt(x²+y²). The one-form A is a local gauge representative away from the axis; multiple patches are necessary globally. The exact symbolic checker establishes all three independent equations

    H_rhorho + (1/rho) H_rho + H_zz = 0,
    Aphi_rho = rho H_z,
    Aphi_z = -rho H_rho.

These are the axisymmetric Laplace equation and dA=*3dH for standard R³ orientation. By the **external Gibbons--Hawking theorem**, the 4D metric is hyperkähler and Ricci-flat away from centres. With equal positive charges and psi period 4pi*q, it extends smoothly over the NUT centres, provided the correct circle bundle and gauge patching are used. The metric is not a direct product of the observed 3D space and the circle. Adding -dt² yields a 5D Lorentzian Ricci-flat solution, Lambda=0, without matter fields.

The independent Python checker does NOT calculate 5D Ricci directly; it checks the exact necessary GH hypotheses. In Lean, only rational algebra and Chern additivity are proved, **not** the GH theorem.

## Coarse and fine observers

Let H_two be the above two-centre harmonic function. Let H_one(x)=1+2q/|x| be the exterior effective single-centre harmonic function.

Both have identical monopole coefficient at infinity:

    lim_{r->infty} r [H(r,theta)-1] = 2q.

This is a coarse observation, not an exact statement that their entire external geometries are isometric.

An observer on the symmetry axis at z=R>a measures exactly

    H_two(R)-H_one(R) = 2q*a² / [R(R²-a²)].

In particular at q=a=1, R=3, the gap is exactly 1/12. As R grows,

    H_two-H_one = [2q a²]/R³ + O(R^-5) along the axis.

At the equator z=0, rho=R, one instead gets

    H_two-H_one = -[q a²]/R³ + O(R^-5).

This directional quadrupole differentiates the two-centre geometry even though the leading 1/R term is the same. If the separation is varied from a=1 to a=2, leading monopole readout is unchanged but quadrupole changes by a factor of four.

The phrase "single object" therefore means an **operational equivalence under a restricted set of far-field measurements**. It does not mean that distinct events are physically identical or that any complete past is destroyed. Allowing more sensitive measurements separates the histories/geometries. In the user's sandpile language, the coarse readout is a quotient; the higher multipole is a distinguishing probe.

### Comparison without a singular effective single centre

An even cleaner witness uses **two genuinely smooth two-centre Gibbons--Hawking solutions** with the same q=1 and common psi period 4pi, but differing centre separations 2a. One solution has a=1, the other has a=2. Both have total charge -2 and leading far-field potential 1+2/r.

At axis distance R=5, direct rational evaluation gives

    H_{a=1}(R=5) = 17/12,
    H_{a=2}(R=5) = 31/21,
    H_{a=2} - H_{a=1} = 5/84.

Thus a coarse observer reading only monopole charge gives the **same answer** for two smooth distinct internal geometries, while a finer observer recovers their separation. This pair is not an exact equality of full external fields, nor a demonstration that the intrinsic histories are physically identical. It is a counterexample to inferring internal geometric individuality from the leading observable.

## A topological invariant, not merely an arbitrary visual pattern

Each centre contributes flux -4pi*q for the local connection A. With normalized circle angle chi=psi/(2q), the small enclosing sphere has first Chern number -1. A large sphere surrounding both centres has first Chern number -2. For N equal centres, the total Chern number is -N (with the same normalization). The gauge bundle itself encodes nontrivial topology.

A WARNING about the single-centre comparison: H_one=1+2q/r with the *same period 4pi*q* has charge -2 and an orbifold singularity at its centre. It is not a globally smooth replacement of the separated two-centre geometry; it is used only as an exterior/coarse effective description. The two-centre metric with separated simple centres and period 4pi*q is smooth.

There are also compact 2-cycles between separated NUT centres in the multi-Taub--NUT geometry. This may offer topological probes beyond the far-field multipole, but the cycle geometry and independent quantum degrees of freedom are NOT derived in this PR.

## Evidence files

- lean/Research/MulticentreObservation.lean: denominator-cleared axis gap identity, rational exact counterexample, quadrupole sign and separation symmetries, coarsened monopole invariance, additive flux and Chern arithmetic.
- tools/check_multicentre_gh.py: exact harmonic/Laplace equation, 2 connection equations, axis/equator asymptotics, finite exact sample, Chern normalization.
- .github/workflows/multicentre-gh.yml: fixed Lean toolchain kernel/axiom audit plus independent SymPy oracle.

## Unsolved physics

This reproduces already-known Abelian Kaluza--Klein monopole geometry and its multi-centre extension, NOT non-Abelian SU(3)/SU(2) gauge dynamics, chiral Standard Model fermions, quantum mechanics, observed masses, or cosmological stability. The operational observer equivalence does not prove that nature has multiple true pasts.

## Prior references

- V. Minerbe, "Rigidity for multi-Taub-NUT metrics", https://perso.imj-prg.fr/vincent-minerbe/wp-content/uploads/minerbe-pub/Articles/rigidalf.pdf . Standard multi-centre harmonic potential, circle bundles, and completeness.
- Modern Gibbons--Hawking construction and smooth extensions: https://cvgmt.sns.it/document/11018/ .
- H. Nastase, General Relativity: A Graduate Course, Chapter 33 (2025), https://www.cambridge.org/core/books/abs/general-relativity/nontrivial-topologies-gravitational-instantons-taubnut-kk-monopole-and-godel-spacetimes/F69C69A81F4CB61266C1037DB405F278 .
