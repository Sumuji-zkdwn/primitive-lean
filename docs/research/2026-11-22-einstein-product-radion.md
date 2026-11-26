# Einstein-Lambda product and universal breathing-mode instability

Date: 2026-11-22 JST. Status: draft. Reproduce with tools/check_einstein_product.py; the algebraic Lean proof has a separate exact-head CI.

## Mathematical achievement, not physical unification

The previous draft PR #179 considered CP2 x CP1(round) x CP1(axial) to obtain the desired su3+su2+u1 Lie algebra and a canonical Spin-c index. Its last factor has varying Gauss curvature and is not Einstein. Here we instead permit a positive gravitational cosmological constant and positively curved external de Sitter spacetime, but no independent matter fields.

The 6D Einstein-Hilbert action is S6 = integral sqrt(-G) (R-2 Lambda6). Its vacuum equation is Ric(G)=2 Lambda6/(6-2) G. Use:

    ds6² = -dt² + exp(2Ht) (dx²+dy²+dz²)
           + a²(dtheta²+sin²theta dphi²).

SymPy independently checks all 36 Ricci components. They are Ric_tt=-3H², Ric_xx=Ric_yy=Ric_zz=3H² exp(2Ht), Ric_thetatheta=1, Ric_phiphi=sin²theta, with other components zero. Set 3H²=1/a²=lambda and Lambda6=2lambda. Thus for a²=1 and H²=1/3 the metric solves the 6D Einstein-Lambda vacuum field equations with Lambda6=2.

The round S² has three noncommuting Killing fields spanning so3, isomorphic as a Lie algebra to su2. The exact ambient rotation matrices and their brackets were independently checked. The internal isometries create *candidate* Kaluza-Klein non-Abelian gauge potentials; they do not establish a consistent 4D Yang-Mills truncation, a realistic spectrum, or particle physics.

## Connection to the 8D internal Kähler geometry of PR #179

Choose K8 = CP2 x S² x S² with internal metric 6 g_FS + g_round + g_round, with g_FS normalized to holomorphic sectional curvature four and Ric(g_FS)=6g_FS. Let the external dS4 have H²=1/3, so Ric(g4)=g4. Each of the four blocks now has Einstein constant one; their 12D direct product satisfies Ric(G12)=G12 at Lambda12=(12-2)/2=5.

The complex product retains a canonical Spin-c structure of arithmetic index chi(O_K)=1 by standard external HRR and Künneth results (NOT the Standard Model fermion spectrum). Both round S² factors contribute so3, so the connected internal isometry algebra has dimension 8+3+3=14, not the desired 8+3+1=12. The extra gauge directions cannot be silently omitted.

The 12D check uses standard product Ricci and Fubini-Study Einstein theorems as premises; we check factor constants but do not compute all 12D Ricci components.

## New general obstruction: tachyonic volume mode

For internal dimension n>0 and Ric(gK)=lambda*gK with lambda>0, use D=4+n Einstein-Lambda gravity, Lambda_D=(n+2)lambda/2, and the 4D Einstein-frame breathing ansatz:

    ds_D² = exp(-n beta(x)) gE_4(x) + exp(2beta(x)) gK_n.

Dimensional reduction of Einstein-Hilbert (up to overall constant) gives

    L4 = R(gE) - [n(n+2)/2](grad beta)² - V(beta)
    V(beta) = (n+2)lambda exp(-n beta)
              - n lambda exp(-(n+2)beta).

At beta=0, exact symbolic differentiation gives

    V(0)=2lambda, V'(0)=0, V''(0)=-2n(n+2)lambda.

With canonically normalized chi=sqrt(n(n+2))*beta, the mass squared is

    m_chi²=-2lambda=-6H²,  H²=lambda/3.

This is strictly negative for all n>0 and lambda>0: the unwarped Einstein-product stationary solution has an unstable breathing mode. This establishes an obstruction *for this family*; it is NOT a no-go for all high-dimensional pure-gravity theories.

## Inspectable verification limits

- Lean module: algebraic equalities and rational normalization of Einstein-factor coefficients, potential Taylor coefficients, universal mass ratio, and examples. Full differential-geometric Einstein-Hilbert reduction is an external input.
- Python: direct 6D Christoffel/Ricci tensor, analytic beta-potential derivatives, 12D block-constant checks, so3 Killing brackets.
- Standard math inputs: Ricci(CP2,FS)=6g_FS in chosen normalization, standard product Ricci, HRR index of the canonical Spin-c operator.

Next: seek a non-product geometric mechanism that removes both the extra so3 gauge symmetry and the negative radion mass without importing independent matter fields. Positive Lambda remains an extra parameter in the gravitational action and is not determined here.

## Sources

- https://georgedouzas.github.io/posts/kaluza-klein-theories/part-vi-01-consistent-reductions.html
- https://georgedouzas.github.io/posts/kaluza-klein-theories/part-iv-01-isometries-gauge-fields.html
- https://math-terek.github.io/texts/projective_space.pdf
- https://doi.org/10.1088/1126-6708/2009/11/094
- https://arxiv.org/abs/hep-th/0005172
