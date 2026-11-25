# 2026-11-26 — Local inner tensor uniqueness without global Sobolev control

## Result and assumptions

Continue #287. On the fixed original exact vacuum metric of #270, on a connected product collar (s-d,s) x S^1 x V (0<d<s, V an open connected H^3 screen patch), a smooth periodic linear vacuum tensor-sector solution Q with smooth one-sided extension to r=s and Q(s,v,x)=0 vanishes on this collar. No global screen integrability, compactness, or analyticity of the perturbation is assumed. If its horizon value is generator independent, partial_v Q vanishes in the collar. The proof uses an analytic-coefficient Fuchsian uniqueness theorem after an exact scalar lift of the tensor equation, not a Carleman estimate or a nonlinear vacuum theorem. The background coefficients are analytic; this is an essential distinction from the general smooth exact metric of #286.

## 1. Regular Fourier equation

Use the original regular coordinates, with f=1-s^2/r^2, s>0 and v modulo L. The tensor sector h_AB=2r^2 Q_AB with other perturbation components zero obeys
    f Q_rr+(f'+3f/r)Q_r+2Q_rv+(3/r)Q_v-(Delta_gamma+2)Q/r^2=0.
Here Delta_gamma is the rough connection Laplacian on covariant screen tensors, and Q is transverse-traceless in the linear vacuum tensor sector (#275, #287). Work locally in the analytic upper-half-space coordinates x,y,z>0 (only z is restricted positive). Smooth periodicity permits Fourier integration in v on each compact screen subpatch without any spatial integrability assumption.

For an arbitrary Fourier wavenumber k=2pi n/L let T(u,x) be the Fourier coefficient of Q with u=s-r>0. Write r=s-u, F=f(s-u)=-u(2s-u)/(s-u)^2. Multiplying the mode equation by u^2/F gives
    [D^2+(B-1)D+C+H(Delta_gamma+2)]T=0,
    D=u partial_u,
    B=u[-f'(r)-3f(r)/r-2ik]/F,
    C=3ik u^2/(r F),
    H=-u^2/(r^2 F)=u/(2s-u).
All B,C,H are analytic in u near zero, B(0)=1+iks, C(0)=H(0)=0. Signs here are those of the inner collar, not the outer one. The indicial roots are 0 and -iks. Smoothness and the zero horizon value imply T=u S with S smooth up to u=0, by the integral formula for division by a defining function. Therefore S satisfies
    [D^2+(B+1)D+B+C+H(Delta_gamma+2)]S=0.
The shifted indicial polynomial is
    (lambda+1)(lambda+1+iks),
whose roots both have real part -1, also for the zero circle frequency. The shift is essential for using the strict negative-real-part version of Fuchsian uniqueness.

## 2. Exact scalar lift, avoiding an unsupported system extension

The Fuchsian theorem used below is scalar. Do not assume it extends to coupled systems without proof. Introduce auxiliary real tangent-vector variables w^A (A=1,2,3), and encode the covariant symmetric screen tensor by the scalar polynomial
    p(u,x,w)=S_AB(u,x) w^A w^B.
These are auxiliary polynomial variables, not new physical dimensions or fields. Let H_i=partial_i-Gamma^k_ij w^j partial_(w^k), where Gamma is the Levi-Civita connection of gamma. Direct differentiation shows
    H_i p=(nabla_i S)_AB w^A w^B,
    L p=gamma^ij (H_i H_j-Gamma^k_ij H_k)p
       =(Delta_gamma S)_AB w^A w^B.
The exact oracle checks both identities for arbitrary six independent symmetric tensor components, using gamma=z^-2 I. L is a scalar differential operator of order at most two in (x,w), with real-analytic coefficients on the local screen chart times a fiber ball. Ellipticity of L on the lifted variables is neither claimed nor needed. The scalar polynomial satisfies
    [D^2+(B+1)D+B+C+H(L+2)]p=0.

## 3. Apply a published local uniqueness theorem

Use Jose Ernie C. Lope, Existence and Uniqueness Theorems for a Class of Linear Fuchsian Partial Differential Equations, J. Math. Sci. Univ. Tokyo 6 (1999), 527–538, theorem 2 (p.529), https://www.ms.u-tokyo.ac.jp/journal/pdf/jms060304.pdf . This extends the Baouendi–Goulaouic uniqueness theorem (1973), DOI 10.1002/cpa.3160260403. In the notation of Lope's theorem, a monic order-m Euler operator with tangential derivatives weighted by mu(u)^{|alpha|}, coefficients continuous in u down to zero and holomorphic in a common complex neighborhood of the tangential variables, and indicial roots of strictly negative real part, has local uniqueness in C_m^0([0,T],D'(R^n)) for the homogeneous equation on a product neighborhood. The weight mu is positive increasing and integral_0^T mu(u)/u du finite. The regularity C_m^0 means that the Euler derivatives through order m extend continuously as distributions. We use only this published theorem, not its proof.

For our scalar lift m=2 and n=6. Choose mu(u)=sqrt(u): the integral is 2 sqrt(T). A second-order tangential term multiplied by H is mu^2 times an analytic coefficient (H/u=1/(2s-u)); a first-order term is mu times sqrt(u)/(2s-u) times an analytic coefficient, which is continuous at zero. There are no mixed D and tangential derivatives. Zeroth-order terms are continuous in u and analytic in x,w. Locally away from z=0 the coefficients extend holomorphically to a complex neighborhood. The two shifted roots have real part -1 on that neighborhood, independently of x,w. A smooth cutoff in (x,w) equal to one near a chosen base point (x0,0) gives p the required distribution-valued regularity on all R^6 while preserving the PDE on a smaller product patch. No equation is imposed on the cutoff transition region, as theorem 2 is local. Thus every stated hypothesis is satisfied for each fixed k.

The theorem implies p=0 in a smaller product neighborhood of (u=0,x0,w=0), for u>0. A quadratic polynomial vanishing on an open set of w has all its coefficients zero, so S and T vanish in a nonempty open (u,x) neighborhood. This local neighborhood may depend on k; Fourier completeness alone would NOT suffice to take a common neighborhood over infinitely many modes.

## 4. Remove the frequency-dependent neighborhood issue

For each fixed k, on the open inner collar u>0, the original unlifted tensor-mode equation is an elliptic system with analytic coefficients: its second-order principal symbol, up to overall sign convention, is (-F) xi_u^2 + gamma^AB xi_A xi_B/r^2, times the identity on symmetric tensors. Both coefficients are strictly positive there; no assumption of uniform ellipticity all the way to u=0 is needed. Standard interior analytic elliptic regularity for elliptic systems with analytic coefficients (Morrey and Nirenberg, On the analyticity of the solutions of linear elliptic systems of partial differential equations, Comm. Pure Appl. Math. 10 (1957), 271–290) gives analyticity of T in the connected open inner collar for this fixed mode. Complex components can equivalently be split into real and imaginary parts. The identity theorem propagates the zero from step 3 throughout the connected open collar. This is not an assumption of analyticity of Q across the horizon, nor a claim of ellipticity of the full Lorentzian operator before mode separation.

Now every fixed Fourier coefficient vanishes at each interior (r,x); Fourier completeness on the circle implies Q=0 pointwise by smoothness. For invariant horizon values apply the argument to partial_v Q, which solves the same linear equation because the original fixed background is v independent. No uniform estimate in k, spectral projection on H^3, or global L2 condition occurs.

## 5. Scope, evidence and next gate

This removes #287's global Sobolev hypothesis for the **fixed analytic background linear TT sector**. It does not prove inner rigidity for arbitrary linear metric components, which involve coupled gauge equations and possibly non-scalar indicial matrices; nor does it apply to a general smooth v-dependent exact vacuum metric, where modes couple. The next finite task is to obtain local uniqueness for the full gauge-fixed linearized system on this fixed background (e.g. test the indicial matrix and a valid system-level Fuchsian theorem), then separately tackle variable-coefficient two-sided smooth nonlinear rigidity. Petersen, Extension of Killing vector fields beyond compact Cauchy horizons, arXiv:1903.09135, DOI 10.1016/j.aim.2021.107953, proves a broader two-sided result under compact-horizon hypotheses; no direct application to this local noncompact screen or priority claim is made.

Actually run locally: python tools/check_kk_horizon_local_fuchs.py. Three check groups passed (all six arbitrary symmetric component lift identities, shifted Fuchs indicial identities, interior sign). First run failed on a structural rather than simplified equality of the B limit; corrected to simplify the difference and reran successfully. SHA256 1395e4f900bbbe625846a230060ce10b3708c86c65f889062201c961a121deb8; Git blob e797d69faefdd08c589c7b52a6a457a32c638cdc. Symbolic checks do not themselves prove either cited PDE theorem. No Lean kernel proof or numerical PDE simulation in this iteration. Dedicated Python CI added.

#287 exact head 22ebcb1f196f1e736c8346c7063ef1c4772b82c4, run 45722994577 completed success. Older approval-blocked branches not re-audited during this bounded follow-up. No main merge.

A/B: compact small finite-norm exact data and local nonlinear scalar curvature divergence (#279). C: coexistence (#280), one-way barrier (#281), formal rigidity (#282–283), general smooth exact exterior rigidity (#286), inner linear tensor uniqueness now local (#287 and this note). General two-sided smooth nonlinear rigidity on a noncompact local periodic horizon, formation of the horizon, causality selection, physical time orientation and quantum physics remain open. Preserve separate high-dimensional and effective gel branches.
