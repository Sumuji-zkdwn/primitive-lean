# 2026-11-26 — Local smooth uniqueness at the periodic null horizon in the linear vacuum tensor sector

## Result and precise assumptions

Continue #283 (all-order formal rigidity). On the exact unperturbed #270 exterior, let Q(r,v,x) be a smooth symmetric transverse-traceless covariant screen tensor with respect to the unit hyperbolic metric gamma, periodic in v, smooth up to r=s on a product screen patch V. Use the linear vacuum tensor sector of #275, with metric perturbation h_AB=2r² Q_AB and other components zero. Assume Q(s,v,x)=0. We prove Q is identically zero in a local exterior domain, without analyticity, global L² integrability, transverse compactness, or all-order vanishing. In particular, if Q(s,v,x) is generator-independent, then the same proof applied to partial_v Q gives generator-independence of the perturbation in that domain. This is a conditional uniqueness theorem for the linear tensor sector; not an existence or stability theorem for a nonlinear family of horizons.

## 1. Master equation and time change

The exact background is
    g=-2 dr dv+f dv²+r² gamma, f=1-s²/r², v mod L, r>s.
For a transverse-traceless tensor, the linear vacuum tensor equation (#275, Ishibashi–Kodama tensor master formalism) is
    f Q_rr+(f'+3f/r)Q_r+2 Q_rv+(3/r)Q_v
        -(Delta_gamma Q+2 Q)/r²=0,
where Delta_gamma is the rough connection Laplacian with negative spectrum convention. This is a metric degree of freedom, not an extra matter field. Set
    r*=r+(s/2)log((r-s)/(r+s)), chi=v-r*,
    t=sqrt(r²-s²)>0, r=sqrt(s²+t²), f=t²/r².
The background becomes -dt²+f dchi²+r² gamma. Let P(t,chi,x)=Q(r(t),chi+r*(r(t)),x). The derivative at fixed v is D_r=(r/t)partial_t-f^(-1)partial_chi and partial_v=partial_chi. Direct substitution (checked symbolically) gives
    P_tt+(1/t+2t/r²)P_t-f^(-1)P_chichi
       -(Delta_gamma P+2P)/r²=0.
Introduce eta=log(t/s), so partial_eta=t partial_t. Then
    P_etaeta+2b P_eta-a P_chichi-b Delta_gamma P-2bP=0,
    a=r²>0, b=t²/r² in (0,1).
Derivatives with respect to eta satisfy a'=2ba, b'=2(1-b)b. These identities hold for every positive t,s; no near-horizon coefficient truncation.

## 2. A finite screen domain (not a global compact horizon)

Fix a closed gamma-geodesic ball of radius R>0 about x0 lying in V, with a neighborhood of its closure still in V. Use the entire periodic chi circle. The screen propagation speed with respect to eta is c=sqrt(b)=t/r. Define a moving ball B_eta centered at x0 of radius
    R(eta)=R-asinh(t/s).
This is positive for 0<t<s sinh(R), and R'=-c, since d_eta asinh(t/s)=t/r. Its closure lies in the original ball. The total screen propagation from eta=-infinity to finite eta is finite, namely asinh(t/s). Thus no condition on spatial infinity is needed. The circle is compact but the whole horizon H³ x S¹ need not be.

## 3. Positive local energy and exact inequality

Use the fiber inner products induced by gamma, fixed in eta and chi. Let
    e=1/2 (|P_eta|²+a|P_chi|²+b|nabla_gamma P|²+|P|²),
    E(eta)=integral_(S¹ x B_eta) e dchi dvol_gamma.
This is a positive estimate norm, not a conserved gravitational energy. Metric-compatible connection integration by parts for the rough Laplacian gives the exact density identity
    partial_eta e
      = a partial_chi <P_eta,P_chi>
        + b div_gamma <P_eta,nabla_gamma P>
        + S_bulk,
    S_bulk=-2b|P_eta|²+ba|P_chi|²
       +(1-b)b|nabla_gamma P|²+(1+2b)<P_eta,P>.
The chi divergence integrates to zero by periodicity. The pointwise bound S_bulk<=3e follows from the explicit sum-of-squares identity
    3e-S_bulk
      = (1+2b)/2 |P_eta-P|²
        +(1+b)|P_eta|²+(1-b)|P|²
        +(3/2-b)a|P_chi|²+(1/2+b)b|nabla_gamma P|² >=0.
All coefficients are nonnegative because 0<b<1 and a>0. For the moving ball boundary the Reynolds differentiation term is -c e; combined with the outward flux the integrand is
    b <P_eta,nabla_n P>-c e
      = -c/2 (|P_eta-c nabla_n P|²+a|P_chi|²
             +b|nabla_tan P|²+|P|²) <=0,
where n is the unit outward screen normal. The two identities are verified symbolically for scalar components, and extend by summation in an orthonormal fiber and screen frame. Consequently
    E'(eta)<=3 E(eta),
    E(eta)<=exp(3(eta-eta0)) E(eta0) for eta0<eta.
This is a local energy estimate, including the boundary flux, not a formal Fourier-mode calculation.

## 4. Smooth vanishing at the horizon is enough

Assume Q has a smooth extension to r=s in the regular (r,v,x) chart and Q(s,v,x)=0 on S¹ x V. Uniformly on the compact circle times the fixed closed ball, the tensor Q and its tangential derivatives Q_v,nabla_gamma Q are O(r-s), while Q_r is bounded, by smoothness and the zero boundary value. At fixed chi the logarithmic time derivative is exactly
    P_eta=(t²/r) Q_r+r Q_v,
and r-s=t²/(r+s). The potentially unbounded shift r* in v causes no issue because all bounds are uniform in the periodic variable. Therefore P, P_chi, nabla_gamma P, P_eta are all O(t²) on the moving domain. The coefficient functions a,b are bounded near the horizon and the volumes are uniformly bounded. It follows that
    E(eta0)=O(t0^4)=O(exp(4 eta0)) as eta0->-infinity.
For each fixed eta with R(eta)>0, the energy inequality then gives
    0<=E(eta)<=C exp(3 eta) exp(eta0) -> 0.
Hence E(eta)=0 and P vanishes pointwise on the ball by smoothness and positive definiteness. In the original chart Q vanishes for
    0<t<s sinh(R), d_gamma(x,x0)<R-asinh(t/s),
all v. No exchange between a nonlinear parameter limit and the horizon limit occurs. This proves smooth uniqueness from just the zero boundary value for this tensor equation. Infinite-order flatness, assumed in #283's open question, is more than sufficient.

For a tensor-sector solution Q with partial_v Q|_(r=s)=0, use that the master operator, TT constraints and coefficients commute with partial_v. The above theorem applied to partial_v Q yields partial_v Q=0 throughout the local exterior region. In the linear vacuum problem alone, zero shear of a *nonlinear* periodic null horizon must not be inferred from the linearized Raychaudhuri equation, since shear squared is quadratic. Thus generator-independence at the boundary is an explicit hypothesis here, as would hold for the screen variation of a differentiable family preserving the normalized periodic null-horizon conditions of #282 in adapted coordinates, when that variation lies in this tensor sector.

## 5. Literature, limits, next gate

Tensor equation: Ishibashi and Kodama, Perturbations and Stability of Static Black Holes in Higher Dimensions, https://arxiv.org/abs/1103.6148. Related compact-horizon wave uniqueness: Petersen, Wave equations with initial data on compact Cauchy horizons, https://arxiv.org/abs/1802.10057 (Analysis & PDE 14, 2021). His general compact-horizon estimates and smooth rigidity results are prior art. Here the explicit time change and moving-screen-ball estimate specialize uniqueness to our fixed warped-product geometry, without assuming global compactness or integrability. No general originality claim is made.

Only the linear tensor sector, in the exterior r>s, has been treated. The other gauge and coupled components of the linearized Einstein equation, nonlinear metric differences in a common suitable hyperbolic gauge, and unique continuation on the chronology-violating side remain unproved. Neither generic nonlinear stability of a periodic horizon nor emergence of the time direction is implied. A flat function of u with v-dependence is not a vacuum solution merely because its Taylor jets vanish. Next finite task: extend the local energy estimate to the coupled gauge-fixed linearized vacuum system, with attention to singular frame coefficients and gauge constraints; then assess a nonlinear difference estimate. Preserve the high-dimensional vacuum and separate effective gel branches.

## 6. Reproducibility and ledger

Local SymPy 1.14.0 run of tools/check_kk_horizon_smooth_tensor.py passed all three groups: exact coordinate transformation, logarithmic time coefficients and propagation radius, and bulk/boundary square identities. SHA256 bd79ad9a4215169733e14782b6b9f88b06756a088a15860a4394edb640af1d79; Git blob 4c4dd8d4be35738db75fae257118b806baa4f929. Run python -B tools/check_kk_horizon_smooth_tensor.py. The energy integration, estimates and uniqueness limit are analytic proofs, not Lean-kernel proofs or numerical PDE simulations. No local Lean executable was available. Dedicated Python CI included.

#283 exact head a52947af5cee2136f6697d86e5d55e1a9b777bd3, dedicated run 45721141690 completed success. Older approval-blocked branches not re-audited in this bounded manual iteration.

A/B: small finite-norm exact compact vacuum perturbations and nonlinear local curvature blow-up established in #279. C: coexistence with chronology violation (#280), causal separation (#281), local horizon first-jet and all-order rigidity (#282/#283). Smooth local exterior uniqueness in the fixed-background linear tensor sector now established without analyticity, conditional on zero boundary difference; full smooth nonlinear local Killing rigidity remains open. No matter, topology change, canonical energy claim, or main merge.
