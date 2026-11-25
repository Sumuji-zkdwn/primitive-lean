# 2026-11-26 — Tensor-sector smooth uniqueness on the chronology-violating side of the curved 5D horizon

## Result and scope

Follow-up to #286. On the **fixed original** Ricci-flat #270 geometry, on the chronology-violating side of its compact-circle horizon, a linear vacuum tensor-sector perturbation Q with zero horizon value and global Sobolev regularity on H^3 times S^1 is zero. If instead its horizon value is independent of the circle variable, Q is circle invariant. No analyticity or infinite-order vanishing is required. The proof uses bounded spectral projections on the complete noncompact screen rather than the exterior's moving-ball energy. This does not prove local uniqueness without the global regularity assumption, uniqueness for arbitrary linear metric components, or general two-sided nonlinear smooth rigidity.

## 1. Exact interior equation and why the exterior proof does not transfer

The background is
    g=-2 dr dv+f dv^2+r^2 gamma, f=1-s^2/r^2, v mod L,
with s>0, gamma the unit hyperbolic metric on H^3. Fix an interior collar s-d<r<s with 0<d<s. In the tensor sector of the warped-product linear vacuum equations (#275, Ishibashi and Kodama, arXiv:1103.6148), h_AB=2 r^2 Q_AB, with all other metric components zero and Q transverse-traceless on the screen. Its equation is
    f Q_rr+(f'+3f/r)Q_r+2 Q_rv+(3/r)Q_v-(Delta_gamma Q+2Q)/r^2=0.
The tensor equation applies on either side: the original EF metric and the equation's coefficients are smooth at r=s. The rough connection Laplacian has negative spectrum convention. No matter field is introduced.

In the inner collar let
    t=sqrt(s^2-r^2), r=sqrt(s^2-t^2),
    r*=r+(s/2)log((s-r)/(s+r)), chi=v-r*, eta=log(t/s).
Here t is a radial variable, **not** proper time. The tortoise derivative is r*'=1/f. The metric in diagonal coordinates is +dt^2-(t^2/r^2)dchi^2+r^2 gamma. Thus the chi circle is timelike. For the screen tensor P(t,chi,x)=Q(r(t),chi+r*,x), the differential operators satisfy
    partial_r|v=-(r/t)partial_t-f^(-1)partial_chi,
    partial_v=partial_chi.
The exact tensor equation becomes
    P_tt+(1/t-2t/r^2)P_t-(r^2/t^2)P_chichi+(Delta_gamma P+2P)/r^2=0.
Equivalently
    P_etaeta-2b P_eta-a P_chichi+b(Delta_gamma P+2P)=0,
    a=r^2=s^2-t^2, b=t^2/r^2>0,
    a'=-2ba, b'=2(1+b)b.
The screen term has the **opposite sign** to #284. Treating eta as a hyperbolic evolution coordinate with a positive gradient energy as on the exterior fails: after integrating by parts, the screen cross term has the wrong sign for cancellation. This is an obstruction to that particular estimate, not to all unique-continuation estimates. We instead use the fixed exact metric's circle symmetry and screen spectral theorem.

## 2. Regularity and spectral decomposition

Let H=L²(H³; Sym² T*H³) with the positive gamma-induced fiber norm. The Friedrichs self-adjoint realization A=-Delta_gamma on this complete Riemannian tensor bundle is nonnegative by connection integration by parts; use its spectral projections Pi_M=1_[0,M](A). The spectral theorem implies Pi_M converges strongly to identity as M->infinity and A restricted to Pi_M H is bounded by M.

For definiteness assume Q is smooth up to r=s as a function of r into every fixed spatial Sobolev space H^j(S¹ x H³; Sym² T*H³), with all fixed finite radial derivatives continuous there. This stronger global assumption makes all manipulations legitimate; a smaller sufficient set of strong L² derivatives could be used. In particular the screen Laplacian is applied to vectors in its self-adjoint domain. Assume Q(s)=0 in L². Uniformly in L² on the product slice,
    ||Q||+||Q_v||=O(s-r), ||Q_r||=O(1).
The coordinate change to P only shifts the circle by an r-dependent phase, a unitary operation on this Hilbert space. Also
    P_eta=-(t²/r)Q_r+r Q_v,
because d_eta r*=r. Hence ||P||+||P_eta||=O(t²) as eta->-infinity. No assumption about compact support or compactness of the screen; this **is** a global integrability hypothesis, unlike #284/#286.

For each integer circle Fourier mode k=2pi n/L and fixed finite M>=0, set y(eta)=Pi_M P_k(eta). All these projections are bounded, so y and y' obey the same O(t²) bounds. The PDE is diagonal in the circle and its only screen differential term is the fixed A. Thus the projected equation is a bounded-operator ordinary differential equation in Pi_M H:
    y''=2b y'-a k² y+b(A-2)y.
The projection need not be proved to preserve the TT constraint: this calculation concerns a tensor already known to satisfy the displayed equation and the self-adjoint screen operator on the full symmetric bundle. Every estimate is for that projected equation, not for a reconstructed finite-dimensional physical perturbation.

## 3. Positive energy in each fixed spectral band

Set c=1+s² k²>0 and
    E=(||y'||²+c||y||²)/2.
This is a positive estimate norm, not a conserved physical gravitational energy. Differentiation yields
    E'=2b||y'||²+Re <y', [1+t² k²+b(A-2)] y>.
By Cauchy-Schwarz and 2 sqrt(c)||y'|| ||y|| <= ||y'||²+c||y||², we get
    E' <= [4b+(1+t² k²+b(M+2))/sqrt(c)] E.
For each fixed k and M the bracket has limit 1/sqrt(c)<=1 as t->0. Hence there exists a sufficiently small t threshold, possibly depending on k and M, below which E'<=2E. Meanwhile the L² horizon assumptions give
    E(eta0)=O(t0^4)=O(exp(4 eta0)).
For a fixed eta below the chosen threshold, Gronwall gives
    0<=E(eta)<= exp(2(eta-eta0)) E(eta0) ->0
as eta0->-infinity. Thus y and y' vanish on that interval. Ordinary uniqueness for the bounded-operator ODE, whose coefficients are smooth on every compact inner radial interval away from r=0, propagates zero to the whole connected collar. Importantly, no uniform threshold in k or M is required: first prove zero for each fixed pair and propagate, and only afterwards take M->infinity. No limit is interchanged with an unbounded spectral cutoff. Taking M->infinity in the strong Hilbert topology gives P_k=0, then Fourier completeness gives P=0 for every radial value. Smoothness gives pointwise Q=0.

If instead Q(s,v,x) is independent of v, then Q_v has zero boundary value, obeys the same regularity and solves the same equation by background symmetry. Thus Q_v=0 throughout the inner collar. Together with #284 this provides two-sided symmetry **for this fixed-background linear tensor sector and this global regularity class**. It is conditional on the horizon data; it does not derive the existence or persistence of a horizon.

## 4. Literature and limitations

Ishibashi and Kodama, Perturbations and Stability of Static Black Holes in Higher Dimensions, https://arxiv.org/abs/1103.6148, develops the tensor master equation in warped products. Petersen, Extension of Killing vector fields beyond compact Cauchy horizons, https://arxiv.org/abs/1903.09135, DOI 10.1016/j.aim.2021.107953, already proves two-sided smooth vacuum Killing rigidity for compact Cauchy horizons with constant nonzero surface gravity via a Carleman estimate. The theorem for globally compact horizons must not be invoked directly for this H³ screen or a merely local collar. The present spectral estimate is a restricted calculation on the original exact metric; no general novelty claim.

The spectral argument uses an exact translation-invariant background, global Sobolev control and its fixed hyperbolic Laplacian. It does not extend by itself to variable principal coefficients, local screen patches with arbitrary boundary data, general metric gauge components, or smooth nonlinear metrics. In particular, #286's general exterior theorem is not yet two-sided for the noncompact product setting. Next bounded problem: test a localized Carleman estimate on this same inner collar, using the screen cutoff terms explicitly, or derive an estimate for the full fixed-background coupled gauge system under a precisely stated global regularity class. Do not claim the compact-horizon theorem has been localized until the estimates actually close.

## 5. Reproduction and ledger

Actually executed Python 3 / SymPy 1.14.0: tools/check_kk_horizon_inner_tensor.py. All three check groups passed: exact interior master operator and log-time coefficients, regular-coordinate derivative transformation, and bounded-spectral-band energy algebra. Tested SHA256 efa968b20307bad6940d6afed71a39861ef2ce3d908d959501570bb9b647046a, Git blob 463ff33150ad1215072bcf779602fd05709f794c. Reproduce: python -B tools/check_kk_horizon_inner_tensor.py. The spectral and PDE proof is analytic, not a Lean-kernel proof or numerical simulation. Dedicated Python CI added.

#286 head 568fed86bb9f16c8f2c7f778f3a85426b7d3f4f5, run 45722510960 completed success. Previous branches not re-audited in this bounded manual follow-up. No main merge.

A/B: exact small finite-norm data and local nonlinear invariant blow-up (#279). C: coexistence (#280), one-way barrier (#281), formal horizon symmetry (#282–283), exterior smooth rigidity (#286), now conditional inner linear tensor uniqueness under global Sobolev control. General two-sided smooth nonlinear rigidity for the noncompact local horizon OPEN. Universal causality selection, the direction of time, thermodynamic arrow, and physical unification OPEN. Keep separate high-dimensional metric and effective gel branches.
