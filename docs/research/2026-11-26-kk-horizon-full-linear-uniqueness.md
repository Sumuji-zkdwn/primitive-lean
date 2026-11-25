# 2026-11-26 — Local smooth uniqueness modulo gauge for all linear vacuum components

## Result and scope

Continue #284 and #283 on the **exact unperturbed** five-dimensional vacuum exterior of #270. On a product screen patch V of H^3, take a smooth periodic symmetric metric perturbation h, smooth up to r=s in the regular (r,v,x) coordinates, solving the linearized vacuum Ricci equation D Ric_g[h]=0. Suppose all transverse jets of h vanish at r=s (flatness), uniformly locally in the smooth sense. Then on a smaller exterior domain h is pure gauge: h=L_(xi sharp) g for a smooth periodic covector xi that is itself flat at the horizon. More generally, if every horizon jet of h is invariant under circle translations, h is gauge-equivalent, by a flat gauge vector, to a circle-invariant linear perturbation there. No analyticity, global screen compactness, or global L² condition. This does NOT prove exact symmetry in arbitrary coordinates, full nonlinear smooth rigidity, unique continuation into the chronology-violating side, or existence/stability of a perturbed horizon.

## 1. Regular-coordinate wave systems

The background is g=-2 dr dv+f dv²+r² gamma, f=1-s²/r², r>s>0, v mod L, gamma=(dx²+dy²+dz²)/z². It is Ricci flat and smooth nondegenerate at r=s. Work with the *components in the fixed regular EF coordinate coframe* dr,dv,dx,dy,dz, even when re-expressing those component functions in different independent variables. Do not transform them to components of a singular orthonormal or diagonal-coordinate frame.

Let U denote the vector of these components for a covector (5 entries) or symmetric covariant 2-tensor (15 entries). The rough wave operator plus any smooth background zeroth-order endomorphism has the form
    (Box_g acting componentwise as a scalar) U + A^mu partial_mu U + B U.
Here A,B are matrix-valued smooth functions in the regular chart. In particular they are smooth on a closed collar over a relatively compact screen patch, including the horizon. With D_mu=partial_mu+C_mu the connection on the chosen components,
    A^k=2 g^(k mu) C_mu,
    B=g^(mu nu)(partial_mu C_nu+C_mu C_nu-Gamma^k_(mu nu) C_k)+potential.
The oracle explicitly constructs these matrices for both ranks, including the curvature potential 2 R_(a c b d) h^(cd) for the symmetric tensor. It checks every entry is rational with denominator a constant times powers of r,z only (no 1/f). This is an algebraic check of boundedness at r=s on each compact screen set; the actual estimates below use compactness only of the local patch and circle.

Use t=sqrt(r²-s²)>0, r*=r+(s/2)log((r-s)/(r+s)), chi=v-r*, eta=log(t/s), and write P(eta,chi,x)=U(r(t),chi+r*,x). As in #284,
    -t² Box_scalar = partial_eta²+2b partial_eta-a partial_chi²-b Delta_gamma,
    a=r², b=t²/r², a'=2ba, b'=2(1-b)b.
The prime means eta derivative. For coordinate component functions
    t² partial_r|_v = r partial_eta-r² partial_chi,   partial_v=partial_chi.
Thus after multiplication by -t² the matrix terms have coefficients
    -r A^r on partial_eta,
    (r² A^r-t² A^v)/r on sqrt(a) partial_chi,
    -tr A^A on sqrt(b) partial_A,
    -t² B on P.
Here tr in the third line denotes the product t times r, not a trace. All these coefficients are bounded uniformly as eta->-infinity, together with every fixed finite set of spatial and eta derivatives on compact screen patches. The background coefficients have no v-dependence; r(t), t, and their eta derivatives are bounded on eta<=eta*. If a smooth periodic v-dependent coefficient were used, the eta shift derivative d_eta r*=r would also be bounded. On a compact patch the Euclidean coordinate and hyperbolic screen norms are uniformly comparable.

Consequently both wave systems (and more generally smooth bounded matrix lower-order couplings of this form) reduce to
    P_etaeta+2b P_eta-a P_chichi-b Delta_gamma P
        = M0 P+M1 P_eta+M2 sqrt(a) P_chi+sqrt(b) M^A partial_A P+F,
with bounded coefficient matrices (signs absorbed into M) and F=-t² times the regular-coordinate source.

## 2. Local uniqueness for flat solutions of the coupled wave systems

Fix a closed screen ball B_R(x0) with neighborhood of its closure in V and use the entire circle. Set B_eta=B_(R-asinh(t/s))(x0) for 0<t<s sinh(R). Its radius decreases at rate c=sqrt(b). Use an ordinary positive Euclidean norm on the list of components, not the indefinite Lorentz tensor contraction:
    e=(|P_eta|²+a|P_chi|²+b|grad_gamma P|²+|P|²)/2,
    E(eta)=integral_(S¹ x B_eta) e dchi dvol_gamma.
For the uncoupled principal part and drift 2b P_eta the bulk term is
    S0=-2b |P_eta|²+ba|P_chi|²+(1-b)b|grad P|²+<P_eta,P>.
It obeys S0<=2e by the explicit identity
    2e-S0=|P_eta-P|²/2+(1/2+2b)|P_eta|²
          +(1-b)a|P_chi|²+b²|grad P|²+|P|²/2.
The chi flux integrates to zero by periodicity. On the moving screen boundary the outward flux minus ce is
    -c/2 (|P_eta-c partial_n P|²+a|P_chi|²+
                       b|grad_tan P|²+|P|²) <=0.
The identities are componentwise and their sums are positive. For the bounded matrix terms choose a uniform finite constant K such that their pointwise norm is <=K sqrt(2e), by Cauchy-Schwarz and the coefficient bounds. Their contraction with P_eta is <=2K e. Thus for the homogeneous system E'<=C E (C=2+2K suffices); with source, E'<= (C+1) E+(1/2)||F||²_L². No numerical value of K is needed, and this is a positive estimate norm, not a conserved gravitational energy.

If U is smooth and flat at r=s, every fixed derivative of U in the regular chart decays as O((r-s)^N) for every integer N, on the compact circle times the ball. Since r-s=t²/(r+s) and
    P_eta=(t²/r) U_r+r U_v,
the energy E(eta0) decays faster than exp(m eta0) for every positive m as eta0->-infinity. For fixed eta in the domain, integrate E'<=C E from eta0, choose m>C, and take eta0->-infinity. Then E(eta)=0. In particular U=0 on the local exterior domain, for the full homogeneous 5- or 15-component wave system. Unlike the sharper tensor-sector estimate of #284 we require flatness (or sufficient finite vanishing order relative to C), not just zero horizon value. All circle components of h are included; no TT condition.

## 3. Existence of a smooth flat gauge vector for a flat source

It is not enough to impose de Donder gauge without checking that it preserves flatness. The following solves the inhomogeneous covector wave equation locally with a flat source. Let J be any smooth covector flat at r=s on V. In the above time variables F=-t²J has superexponential decay as eta->-infinity in every fixed spatial Sobolev norm after cutting off in the screen. Choose a smooth compact screen cutoff equal to one on a neighborhood of B_R, with support in V. Extend F and the bounded lower-order coefficient matrices to all H³ by multiplying with a cutoff and extending by zero; leave the scalar principal part and 2b drift unchanged. This extension is solely an auxiliary linear PDE construction; outside the patch it need not represent the physical connection.

For every finite initial eta_j->-infinity solve the extended equation on eta_j<=eta<=eta* with zero Cauchy data at eta_j. On each finite time interval the scalar principal part is normally hyperbolic, with positive a,b and complete spatial slices S¹ x H³; standard smooth linear Cauchy well-posedness and finite propagation apply. The source has compact screen support and the total screen speed integral to eta* is finite, so these solutions have support in a fixed compact screen neighborhood for all j. Alternatively global Sobolev estimates suffice.

For a nonnegative integer k, form E_k as the sum of the positive principal energies over spatial derivatives partial_chi^l and covariant screen derivatives nabla_gamma^j with l+j<=k, now integrated over the whole spatial slice. These derivatives act on the scalar component functions, not on the original spacetime tensor frame. Curvature of gamma is constant; commuting its rough Laplacian with these derivatives yields bounded curvature multiples of derivatives of order at most k. Multiply those by b, and use bounded derivatives of the cutoff matrix coefficients in the weighted form of Section 1. In the commutators with first-order terms all spatial derivatives of the coefficient times a derivative of the unknown are controlled by E_k: the chi derivative is weighted by sqrt(a), and the screen derivative by sqrt(b); commuted orders are at most k+1 with these weights. The eta derivative commutes with the chosen spatial differential operators. Integration by parts for the induced screen tensor connection has the same positive energy identity, with no spatial boundary terms. This gives
    E_k' <= C_k E_k + C_k ||F||_(H^k)^2
for constants independent of eta_j on eta<=eta*. Compact support and smoothness justify integration, or use an exhausting cutoff. For each N with 2N>C_k, flatness gives ||F||_(H^k)<=c_(k,N) exp(N eta), so zero initial data yield
    E_k(P_j;eta)<=c'_(k,N) exp(2N eta),
uniformly in j. The difference of two solutions started at different eta_j solves the homogeneous equation after the later start eta_l; its data energy there is bounded by c' exp(2N eta_l). The same inequality gives convergence in every E_k uniformly on compact time intervals, since 2N>C_k. At finite times b>0, the energies control the ordinary spatial Sobolev norms and time derivative; standard Sobolev embedding and the PDE show the limit is a smooth solution. All these estimates pass to the limit, with N arbitrarily large. In particular the solution and its first eta derivative have every fixed unweighted spatial Sobolev norm decaying faster than every exponential at -infinity (increase k for higher spatial derivatives). Repeated eta derivatives have the same property by the equation, smooth bounded coefficient derivatives, and corresponding derivatives of the flat source.

Transform back to the regular chart. Each r derivative at fixed v introduces at worst powers of t^(-2) from partial_r=(r/t²)partial_eta-(r²/t²)partial_chi; all orders of derivative still decay faster than any power of t by the preceding estimates. Hence the solution extends smoothly by zero at and across r=s, with all jets zero. On the original local patch where the cutoff equals one the equation is exactly Box_g xi=J. Restrict to the smaller local exterior domain of Section 2 if needed. The uniqueness for flat homogeneous solutions makes the local result independent of arbitrary extension choices in that domain. We have used the standard finite-time Cauchy theorem, not assumed a characteristic-data theorem on a noncompact horizon.

## 4. Linear vacuum uniqueness modulo coordinate transformations

On the Ricci-flat background, define D(h)_b=nabla^a h_ab-(1/2)nabla_b tr_g h. The usual linear diffeomorphism identity is
    D(L_(xi sharp) g)_b=Box_g xi_b+Ric_ba xi^a=Box_g xi_b.
For h flat, J=D(h) is a smooth flat covector, because the connection and inverse are regular at r=s. Solve the wave equation from Section 3, and put h0=h-L_(xi sharp)g. Then h0 is flat, D(h0)=0, and D Ric_g[h0]=0 by linearized diffeomorphism invariance and Ric_g=0. In this gauge the linearized vacuum equation is the full normally hyperbolic system
    Box_g h0_ab+2 R_(a c b d) h0^(cd)=0
with the curvature convention R^a_(b c d)=partial_c Gamma^a_(d b)-partial_d Gamma^a_(c b)+... .
By Section 2 h0 vanishes in the local exterior. Thus h is pure gauge, with gauge covector flat at the horizon. If h were already in this gauge, no gauge correction would be needed and it would vanish directly. No extra physical field is added by solving for xi; it is an infinitesimal coordinate choice. The gauge identity and linearized harmonic Ricci formula are classical analytic inputs, not new computer-verified general relativity theorems.

For a general linear vacuum perturbation h whose horizon jets are all generator-independent, take the average over circle translations
    h_av=(1/L) integral_0^L Phi_lambda^* h d lambda.
The background is circle invariant, so h_av and h-h_av solve the linearized vacuum equations. The latter is flat at the horizon, and the result just proved yields h-h_av=L_(xi sharp)g locally. Thus the perturbation is gauge-equivalent to h_av, which is circle invariant, without analyticity. A flat gauge vector can itself produce a non-invariant flat metric perturbation in a fixed chart; e.g. a vector with coefficient exp(-1/(r-s)^2) sin(2pi v/L) cut off on a screen patch. Such pure gauges are exactly why coordinate-wise uniqueness cannot be inferred without a gauge. This theorem is linear on the original exact background, not a proof of a Killing vector for a general smooth nonlinear vacuum metric.

## 5. Evidence and limitations

Actually executed locally in Python/SymPy 1.14.0: tools/check_kk_horizon_full_linear.py. Five check groups passed: all 25 background Ricci entries and regular connection/curvature; exact scalar drift and logarithmic time change; all coefficient matrices of rank 1 (5 components) and rank 2 (15 components); positive energy and moving-ball flux identities. An initial run failed on an incorrect coefficient in the square-completion certificate (1+2b instead of 1/2+2b); corrected and reran, all checks passed. Tested SHA256 3444c12e3749cdb895cb2c32af78b2ad8f002cac0e25b98e85cc19bb40d4eecc; Git blob fb3ee64953f26e898a863553e5cd082387f69d6e. Reproduce: python -B tools/check_kk_horizon_full_linear.py. The estimates, limiting Cauchy construction, and gauge argument are analytic hand proofs; not a numerical PDE evolution or Lean proof. Local Lean executable not available. Dedicated Python CI added.
Predecessor #284 head f0ba8cbf78a55d70e5b9778d992c9af85c5cd796 run 45721464021 success. Older blocked branches not re-audited in this bounded continuation.

Prior work: Petersen, Wave equations with initial data on compact Cauchy horizons, https://arxiv.org/abs/1802.10057 (general bundle wave estimates and existence/uniqueness from all-order compatibility under compact-horizon assumptions); Petersen, On the Cauchy problem for the linearised Einstein equation, https://arxiv.org/abs/1802.06028 (gauge and Cauchy theory). No general novelty claim. Our argument specializes to the explicit warped product exterior and localizes the estimate to a finite screen ball or cutoff extended system, without requiring the full horizon to be compact. A general smooth nonlinear metric with a periodic null horizon need not have this exact principal part; the nonlinear gauge matching and variable-principal-part energy estimate are still missing. No conclusion about general smooth Killing rigidity, physical causality selection, entropy, or quantum theory.

## 6. Ledger and next finite step
A/B remain established for the finite-norm compact exact data and nonlinear local singularity of #279. C: #280–283 establish the coexistence, one-way barrier, and formal jet restrictions in their stated classes; #284 gives smooth tensor-sector uniqueness. Here full linear vacuum uniqueness modulo flat gauge is established on the fixed background exterior, and extends to symmetry modulo gauge for generator-independent jets. Next finite step: derive the logarithmic-time energy estimates for two exact vacuum metrics in a common wave gauge with matching horizon jets, including variable mixed principal terms; separately establish whether the required common gauge can be attained without spoiling flatness, before claiming nonlinear rigidity. Preserve separate high-dimensional and effective gel branches. Draft only; no main merge.
