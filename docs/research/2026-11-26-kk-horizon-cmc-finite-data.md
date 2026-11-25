# 2026-11-26 — Finite Sobolev norm exact vacuum constraint data tangent to singular KK shear

## Result and scope

Follow-up to #275 (localized linear shear) and #277 (exact homogeneous nonlinear family). On the original noncompact H^3 x S^1 exterior, construct a smooth curve of exact vacuum initial data with arbitrarily small global Sobolev perturbation norms. Its first variation is a velocity-only compact TT perturbation agreeing on a ball with the homogeneous logarithmic shear of #277. The first-order tidal curvature along a radial ray is unbounded at the old horizon. The full nonlinear evolution of these finite-norm data to the horizon is NOT proved. Also prove that this simple conformal construction cannot leave the metric exactly unchanged outside the source: its quadratic correction is positive everywhere. This is an obstruction to this particular gluing ansatz, not a general no-gluing theorem.

## Constraint equations

Fix r0>s=sqrt(B)>0 and f=1-B/r^2. Use the diagonal exterior coordinates chi=v-r*(r), r*'=1/f, metric -dr^2/f+f dchi^2+r^2 gamma_H3, chi periodic. Spatial slice M=S^1 x H^3 with g0=f0 dchi^2+r0^2 gamma. Set the sign convention K=+1/2 Lie_n g, n=sqrt(f0) partial_r at fixed chi. Its principal extrinsic curvatures are b=f'(r0)/(2sqrt(f0)) on the circle and a=sqrt(f0)/r0 on the triple. Thus tau=3a+b>0, sigma=K0-(tau/4)g0 is parallel and TT. Let U=|sigma|^2, C=3tau^2/4>0, R0=-6/r0^2. The exact background Hamiltonian constraint reads R0=U-C; the momentum constraint holds. This identity is checked by the oracle.

Take T smooth, compactly supported, trace-free and divergence-free on g0, with only H^3 components and H^3 trace zero, so sigma:T=0 pointwise. For instance use the compact W=z times the Euclidean fourth-order TT construction in #275, extended independently of chi, and multiply by any constant. Nonzero T exists; H^3 balls and the full circle are compact. One may also multiply the H^3 components by a smooth periodic function of chi without violating TT on the product.

For a positive conformal factor phi seek exact data
    g=phi^2 g0,   K=phi^(-2)(sigma+eps T)+(tau/4)g.
This is the CMC conformal method in four spatial dimensions, not a new independent scalar field. In particular the momentum constraint holds identically because the covariant divergence of a rescaled trace-free tensor is phi^(-4) times its old divergence. The scalar curvature is phi^(-3)(-6 Delta phi+R0 phi). Hamiltonian becomes
    F(phi,eps)=-6 Delta phi+(U-C)phi-(U+eps^2 |T|^2)phi^(-5)+C phi^3=0,
where Delta=div grad on g0. All conformal identities were checked with general phi and all four divergence components. No assumption of compact support of phi-1 is made.

## Global finite-norm existence

Write u=phi-1. The product M has bounded geometry (constant curvature factors, positive injectivity radius, complete metric). Fix an integer m>=3. The standard bounded-geometry Sobolev multiplication, embedding, elliptic estimates and the Banach implicit function theorem are analytic inputs here, not newly formalized. The map F(1+u,eps):H^(m+2)(M) x R -> H^m(M) is smooth near (0,0), since the background constants cancel, the compact source lies in every H^m and u is uniformly small. Its linearization in u is
    L=-6 Delta+6U+2C.
The mass 6U+2C is strictly positive. On the complete manifold, the positive quadratic form 6||grad u||_2^2+(6U+2C)||u||_2^2 is coercive on H^1. Lax-Milgram yields a unique weak solution for each H^m source; global elliptic regularity (uniform local charts and partition of unity) gives H^(m+2) with bounded inverse. The implicit function theorem therefore gives a unique small u(eps) in H^(m+2) for sufficiently small eps. Positivity of phi follows from uniform embedding. Elliptic bootstrap gives smoothness. The curve is even in eps by local uniqueness, and
    u(0)=u'(0)=0,    u''(0)=2 L^(-1)|T|^2,
    u(eps)=eps^2 L^(-1)|T|^2+O(eps^4)
in the fixed H^(m+2) norm. Consequently the exact data have ||g-g0||_(H^(m+2))=O(eps^2), ||K-K0||_(H^(m+1))=O(|eps|); all norms measured by g0. For any fixed finite regularity one may run the argument at that regularity. This supplies arbitrarily small *global* finite positive initial perturbation norms, unlike the homogeneous family. This is not a definition of conserved canonical gravitational energy, an ADM charge, or an assertion of finite total background energy.

## Positive tail / obstruction to naive localization

The small solution u tends uniformly to zero at spatial infinity (uniform continuity plus L^2 and bounded geometry). At any negative minimum of u, phi<1 and the algebraic term
    U(phi-phi^(-5))+C(phi^3-phi)-eps^2|T|^2 phi^(-5)
is strictly negative, whereas the PDE requires it equal 6 Delta phi>=0. Thus u>=0. At phi>=1 rewrite the equation
    -6 Delta u+A(x)u=eps^2|T|^2 phi^(-5),
    A=U sum_(j=0)^5 phi^(-j)+C phi(phi+1)>=2C>0.
Strong maximum principle gives u>0 on the connected M for eps!=0 and T not identically zero. The same equation at a positive maximum gives u<=eps^2 sup|T|^2/(2C). The scalar correction is small and has finite norm, but is everywhere nonzero; in this chosen identification of the slice, the conformal metric never agrees exactly with g0 even outside supp(T). Nor is there a proof that a ball of these data agrees with #277's exact homogeneous data. Finite propagation of the nonlinear equations cannot simply be applied to identify their evolutions. This specific obstruction must not be confused with a general obstruction to vacuum constraint gluing with additional geometric degrees of freedom.

## Singular first variation: zero mode, velocity data only

Let p0(r)=log(f(r)/f0)/(2B). Then (r^3 f p0')'=0, p0(r0)=0, n p0(r0)=1/(r0^3 sqrt(f0)). Let W from #275 equal U_H=z^(-2) diag(1,-1,0) on a ball of hyperbolic radius greater than acosh(r0/s). Take T=r0^2 (n p0(r0)) W as H^3 covariant components, zero circle components. The exact-data tangent is delta g=0, delta K=T. With the plus sign convention this is precisely the velocity-only tensor initial data delta g_ij=2r^2 p0 U_H locally. The TT linearized evolution of #274/#275, with circle zero mode, matches that homogeneous shear near the fixed-v radial null ray by the finite hyperbolic causal radius argument in #275. In a smooth linear evolution gauge the parallel-screen tidal split (gauge invariant as in #274) is
    -2(p0''+2p0'/r)=2(r^2+B)/(r^2(r^2-B)^2).
It obeys
    lim_(r->s+) (r-s)^2 tidal=1/B>0.
This is the singular derivative of the exact-data development at eps=0, on every fixed compact interior time interval, by standard smooth dependence of the Einstein Cauchy problem (after gauge fixing). It is NOT legitimate to interchange the eps derivative and the horizon limit or infer that the nonlinear curvature diverges for fixed eps!=0. Exact initial data, linear tidal divergence, and nonlinear horizon instability are three distinct claims.

## Evidence and prior work

The local SymPy 1.14.0 oracle checks background vacuum constraint, conformal Ricci contraction and four divergence identities, Lichnerowicz residual and derivative, positive comparison factor, and exact zero-mode tidal coefficient. All four groups passed. Script SHA256 a1979500642ee73042bce0e2a3e3c9b90892b7dea30c3bab3c2ea3ed7c801d2b, Git blob e477a778b0e35b17765cc64311efbc017ef27776. Reproduce python -B tools/check_kk_horizon_cmc.py. Dedicated Python CI added; no new Lean proof of elliptic existence is claimed. CMC conformal method is classical; see Maxwell, Solutions of the Einstein Constraint Equations with Apparent Horizon Boundaries (2005), https://arxiv.org/abs/gr-qc/0307117, and https://pmc.ncbi.nlm.nih.gov/articles/PMC5256071/ for the general Cauchy problem. Maxwell's asymptotically Euclidean result is not directly used as a theorem on this product end; the positive-mass IFT argument above is specialized to our slice. No claim of general novelty.

Predecessor #277 exact head c567ff3e849758f8c8ad80d385522e330d40f623, run 45718430742: Python job and Lean trust-zero/axiom audit step success when checked, workflow overall still in progress. #275 755d6fac1dc0c6911d06973a247e0decc184511c, run 45717853208 success. Prior blocked CI ledger in #275, not re-audited in this bounded iteration.

## Ledger / next finite problem

A: exact nonlinear constraints with arbitrarily small global Sobolev perturbation norms now PASS, tangent to singular compactly seeded linear data. No canonical conserved energy claim. B: nonlinear homogeneous instability #277 PASS; nonlinear horizon curvature of the same finite-norm data still OPEN. C: universal causal selection OPEN. The conformal tail is a concrete obstacle to an exact interior/exterior matching argument. Next: test whether additional free conformal geometry and/or nonconstant mean curvature can solve a localized constraint gluing problem while accounting for Killing initial data obstructions; alternatively prove a nonlinear comparison/asymptotic theorem for these exact data. No matter fields or topology change; no main merge. Keep chronology-violating exact backgrounds as valid solutions and maintain separate gel branch.
