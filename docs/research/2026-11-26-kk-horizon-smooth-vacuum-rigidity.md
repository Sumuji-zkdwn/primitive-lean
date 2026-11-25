# 2026-11-26 — Local smooth vacuum Killing rigidity on the exterior of a periodic nondegenerate null horizon

## Scope and result

Follow-up to #283–285. Consider an **exact**, smooth, five-dimensional Ricci-flat Lorentzian metric on a periodic Gaussian-null collar of the form
    g = -2 du dv + u F dv² + 2u b_A dv dx^A + q_AB dx^A dx^B,
where v has fixed period L>0, x belongs to a three-dimensional open screen patch, q is positive definite, and H={u=0} has smooth closed null generators. Work in the normalized chart of #282, with F|_H=2 kappa for a positive constant kappa. By the horizon jet theorem of #283 all finite transverse metric jets are v independent. In particular L_Z g, Z=partial_v, is flat at H. The hypotheses about the horizon and the normalization are essential; no existence of such a horizon for arbitrary initial data is asserted.

This note proves that Z is a genuine Killing field on a sufficiently small exterior collar of any relatively compact smaller screen patch, without assuming analyticity, a priori Killing symmetry, or compactness of the entire horizon. The metric being used is nonlinear and exact, not a linearized perturbation of #270. The method solves a linear auxiliary vector wave equation **on that exact metric**. It avoids the unresolved nonlinear coordinate-gauge matching strategy of #285. It does not establish Killing rigidity on the u<0 chronology-violating side, nor horizon formation or generic nonlinear stability.

## 1. Wave principal part for a general smooth Gaussian-null metric

Use regular coordinate components for any finite-rank tensor or covector system. Its normally hyperbolic operator has scalar principal part g^(mu nu) partial_mu partial_nu and smooth matrix-valued lower-order terms. These coefficients are bounded with all fixed finite derivatives on closed subcollars of compact screen sets. No singular orthonormal frame is used.

Write D=F-u |b|_q², B^A=q^AB b_B. The inverse metric satisfies
    g^uu=-u D, g^uv=-1, g^uA=u B^A,
    g^vv=g^vA=0, g^AB=q^AB.
On a sufficiently small collar D=2 kappa+O(u)>0 uniformly on the compact circle and screen set. The exact inverse is verified symbolically with an arbitrary symmetric 3x3 screen matrix.

Choose a fixed positive scale u_* and set
    u=u_* exp(2 eta), v=chi+eta/kappa, chi mod L.
Then partial_u=(partial_eta-kappa^(-1)partial_chi)/(2u), partial_v=partial_chi. Multiplying the wave operator by -4u/D and using independent variables (eta,chi,x), the principal part becomes
    partial_eta² + 2 beta^i partial_eta partial_i - A^ij partial_i partial_j,
where i,j run over chi and x:
    beta^chi=2/D-1/kappa,  beta^A=-2u B^A/D,
    A^chichi=4/(kappa D)-1/kappa²,
    A^chiA=-2u B^A/(kappa D),  A^AB=4u q^AB/D.
This is an exact coordinate calculation, not an approximation. Define d_chi=1, d_A=sqrt(u) and W=diag(d_i). The scaled matrix W^(-1) A W^(-1) tends uniformly as eta->-infinity to diag(1/kappa²,2 q_H^AB/kappa), a uniformly positive definite matrix on the compact patch. Thus for sufficiently negative eta it is uniformly bounded above and below by positive multiples of the identity. beta=O(u). The scaled matrix and its spatial and eta derivatives of every fixed finite order are bounded. In particular partial_i A^ij and partial_eta A^ij are controlled by the corresponding d_i d_j weights before summing over i. This uses smoothness, periodicity, F|_H=2 kappa and the bounded shift rate partial_eta v=1/kappa. No assumption of v independence away from H.

The coordinate Hessians from changing variables contribute -2 partial_eta+2/kappa partial_chi. A regular first-order matrix term C^mu partial_mu becomes
    -2 C^u/D partial_eta
    +(2 C^u/kappa-4u C^v)/D partial_chi
    -4u C^A/D partial_A.
Its coefficients are bounded relative to partial_eta, partial_chi and sqrt(u) partial_A. The zeroth order term is multiplied by -4u/D and is also bounded. All corresponding differentiated coefficients obey the same estimates. Hence any such wave system is
    P_etaeta + 2 beta^i P_etai - A^ij P_ij = L(P,P_eta,W grad P)+f,
with L a bounded linear matrix expression. The four algebraic groups in the accompanying SymPy oracle verify the inverse, transformed principal matrix and scaled limit, lower-order factors, and energy identity below.

## 2. Local positive energy and moving-domain estimate

For component functions use ordinary positive Euclidean inner products, not the indefinite Lorentzian fiber norm. Put y=P_eta, P_i=partial_i P and
    e=(|y|²+A^ij <P_i,P_j>+|P|²)/2.
The exact density identity with fixed coordinate spatial measure is
    partial_eta e = partial_i J^i + S,
    J^i=A^ij <y,P_j>-beta^i |y|²,
    S=<y,L+f+P>-(partial_i A^ij)<y,P_j>
      +(partial_i beta^i)|y|²+(partial_eta A^ij)<P_i,P_j>/2.
Uniform scaled ellipticity and bounded differentiated coefficients give S<=C e + |f|²/2 after increasing C. For example, the coefficient of P_j in the divergence term is bounded by a constant times d_j, and the coefficient of P_i P_j in the last term is bounded by a constant times d_i d_j. The term from the shift is controlled by its bounded divergence. These estimates remain valid for matrix lower-order terms and every finite list of tensor components.

Use the full chi circle and a shrinking Euclidean screen ball centered at x0, radius R-c0 sqrt(u) with its closure contained in the original coordinate patch. Its outward normal n has only screen components. The flux obeys
    J·n <= [sqrt(n^T A n)+2 |beta·n|] e <= c0 sqrt(u) e
for a uniform c0 chosen large enough. The first inequality follows from Cauchy-Schwarz in A and 2ab<=a²+b². Since the radius derivative is -c0 sqrt(u), the boundary motion cancels this upper bound on outward flux. The chi flux integrates to zero by periodicity. Therefore for the integrated energy E on this domain,
    E'(eta)<= C E(eta)+||f||²/2.
The same argument uses only the chosen local screen chart; no transverse boundary conditions or global compactness assumptions. The energy is an estimate norm, not a conserved gravitational energy.

If a smooth solution of the homogeneous system is flat at u=0 in regular coordinates, the transformed solution and all fixed derivatives decay faster than any exponential as eta->-infinity, uniformly on the chosen compact chart. For instance P_eta=2u U_u+kappa^(-1)U_v in terms of the original components U. Hence E(eta0)=O(exp(N eta0)) for arbitrary N. Fix eta and apply Gronwall from eta0<eta, then send eta0->-infinity with N>C. This proves E(eta)=0 and therefore local uniqueness for flat homogeneous solutions. The argument permits nonconstant principal coefficients and mixed time-space second derivatives.

## 3. Existence of a flat solution of a forced linear wave system

We also need existence, not just uniqueness. For any smooth source flat at H, construct a flat solution on a smaller local exterior as follows. In transformed coordinates extend coefficients and the source to a large auxiliary screen torus, using a smooth cutoff supported inside the original coordinate patch and identically one on a neighborhood of the chosen screen ball. For the principal spatial coefficient extend the **scaled** matrix W^(-1)AW^(-1) by a convex combination with a constant positive matrix, then multiply back by W on both sides. Extend shift and weighted first-order coefficients by cutoff, and extend the flat source by zero after cutoff. These extensions are auxiliary for the linear PDE and do not modify the physical vacuum metric or its topology. The uniform coefficient bounds, scaled ellipticity and spatial derivative bounds hold on the auxiliary torus for all sufficiently negative eta. The normalized principal symbol has one positive and four negative eigenvalues (Schur complement -A-beta beta^T); the time slices are spacelike. On each finite interval this is a smooth strictly hyperbolic scalar-principal system on compact spatial slices.

For eta_j->-infinity solve the ordinary linear Cauchy problem with zero value and eta derivative at eta_j. Standard finite-time smooth linear hyperbolic well-posedness applies. For integer k>=0 sum the positive energies for all spatial derivatives through order k. On the torus, periodic integration removes the flux. The commutators have no loss relative to this weighted energy: a commuted second spatial derivative has at most k+1 spatial derivatives in total and its coefficient has weights d_i d_j; one of these supplies the weighted top derivative, the other is bounded. A commuted mixed term has at most k spatial derivatives of P_eta and bounded coefficient. Differentiated lower-order coefficients obey their respective weights. No differentiation of the coefficient of P_etaeta is needed because it is 1. The same estimates yield
    E_k' <= C_k E_k + C_k ||f||_(H^k)^2,
uniformly in eta_j. Flatness gives ||f||_(H^k)<=c_(k,N) exp(N eta) for every N. Integration with zero data for 2N>C_k gives E_k<=c'_(k,N) exp(2N eta). Differences of solutions started at distinct eta_j solve the homogeneous equation after the later start, with data bounded by the same estimate. They converge in every E_k on compact finite time intervals by Gronwall; ordinary Sobolev embedding there (u>0) and the wave equation give a smooth limit. All of the superexponential bounds pass to the limit, and increasing k and repeatedly applying the equation gives the bounds for all eta derivatives. Transforming back to the regular chart introduces at worst finite inverse powers of u for each fixed derivative; thus the resulting covector or tensor is smooth and flat at H and extends smoothly by zero to u<=0. It solves the desired equation where the cutoff equals one. Section 2 gives local independence of extension choices where two solutions have the same source. This is a linear Cauchy limit argument on an auxiliary space, not a nonlinear PDE existence theorem or numerical simulation.

## 4. Killing propagation on the exact nonlinear vacuum metric

Define the gauge divergence D_g(h)_b=nabla^a h_ab-(1/2)nabla_b tr_g h. The standard differential identity is
    D_g(L_Y g)=Box_g (Y_flat)+Ric_g(Y,.).
On the exact vacuum metric Ric_g=0, the initial asymptotic symmetry Z=partial_v has L_Z g flat by #283. Hence J=-Box_g Z_flat=-D_g(L_Z g) is a smooth flat covector. Apply Section 3 to obtain a flat covector xi solving Box_g xi=J locally. Put X=Z+xi^sharp, so Box_g X_flat=0.

The tensor h=L_X g is smooth and flat at H and satisfies D_g(h)=0. Also D Ric_g[h]=L_X Ric_g=0 by diffeomorphism covariance, using **exact** Ricci flatness. Therefore the standard linearized Ricci identity in harmonic gauge gives
    Box_g h_ab + 2 R_(a c b d) h^(cd)=0,
with the same curvature convention as #285. The curvature potential and connection matrices are smooth regular-coordinate coefficients on the exact metric. Section 2 therefore forces h=0 in a local exterior domain. This proves that X is a genuine Killing field, not a first-order approximation to one. The vector wave equation is an auxiliary construction, not an independent physical field. No assumption about a common wave gauge for two nonlinear metrics is needed.

In fact X=Z on a smaller Gaussian-null exterior collar. To see this, extend the flat correction by zero across H. The local flow of X on H is translation in v; its differential at H is the translation differential (identity in these coordinates), since X-Z and its first derivatives vanish there. By shrinking to a compact smaller screen patch and a short collar, the flow is defined for small parameter values and preserves the exterior (H is invariant under the flow). It is an isometry there because L_X g=0. The curves with v,x constant and u the affine parameter are null geodesics, since Gamma^mu_uu=0 identically in the Gaussian-null chart. An isometry maps such a geodesic to a geodesic; its initial point at H is translated and its initial tangent is again partial_u, by the boundary differential. Smoothness and uniqueness of the geodesic equation up to H imply that the image is exactly the corresponding constant-v,x radial geodesic. Thus the flow is v translation on the smaller collar. Differentiating at zero flow parameter yields X=partial_v there. The chart includes the entire circle, so these orbits are periodic with period L. It follows that the **exact** metric is independent of v on the exterior collar in the normalized chart.

The use of an isometry here is confined to the side u>0; extension of X as a smooth vector field across H is not a claim that it is Killing on u<0.

## 5. Prior art, limitations, and next question

The auxiliary-vector-wave strategy is the established method of Petersen and Racz, *Symmetries of Vacuum Spacetimes with a Compact Cauchy Horizon of Constant Nonzero Surface Gravity* (2023), DOI 10.1007/s00023-023-01335-9, https://arxiv.org/abs/1809.02580. Their theorem is more general in generator structure but assumes a compact Cauchy horizon. Petersen's *Wave equations with initial data on compact Cauchy horizons*, https://arxiv.org/abs/1802.10057, gives general compact-horizon wave existence and uniqueness results. The contribution here is the explicit weighted local energy proof for the periodic-product chart, including an auxiliary Cauchy limit and an exterior radial-geodesic identification; no claim of priority for smooth horizon Killing rigidity or its vector-wave method. Petersen's *Extension of Killing vector fields beyond compact Cauchy horizons*, https://doi.org/10.1016/j.aim.2021.107953 (2021), uses a Carleman unique-continuation estimate to obtain two-sided rigidity under compact-horizon hypotheses. Do not apply that theorem to the noncompact/transverse-local setting without verifying its assumptions.

This local argument requires the smooth periodic product chart, positive normalized nonaffinity and vacuum. It says nothing about degenerate horizons or dense nonclosed generators, and does not prove the existence, stability, genericity, or dynamical selection of such horizons. No claim of derivation of the time orientation, entropy arrow, observable particle physics, canonical energy or quantum theory. The earlier exact singular/CTC coexistence remains a counterexample to a simple universal chronology-protection claim. The next finite question is whether the flat-wave unique-continuation argument can be adapted to the u<0 side (where u is not a time coordinate), or whether a genuine flat nonsymmetric vacuum remainder can exist there. Investigate localized Carleman estimates or explicit counterexamples before claiming two-sided rigidity. Preserve separate higher-dimensional vacuum and effective gel branches.

## 6. Reproducibility and ledger

Actual local Python/SymPy 1.14.0 run of tools/check_kk_horizon_smooth_rigidity.py passed all four check groups. The first local copy and uploaded copy differed only in the name of the integer dimension variable (n versus nn); reran the exact uploaded version and verified matching Git blob 1985bc0918a1bdbe926ebda76f47c9a65667ca09, SHA256 dc5ec5e9c60a1f5402130b44fc0b507a8eb6a221fa784edb51d35f49626374ad. Reproduce with python -B tools/check_kk_horizon_smooth_rigidity.py. These checks certify algebraic identities, not the complete PDE estimates or general Einstein identities by machine proof. Those are hand arguments using standard finite-time hyperbolic Cauchy theory; no Lean kernel proof in this iteration. Dedicated exact Python CI added.

Predecessor #285 head d7714f7718fbbeb03d601b14769dd7dec5e65693, dedicated run 45721982693 completed success. Other previous gates not re-audited during this bounded follow-up; no main merge.

A/B: exact finite-norm compact vacuum data and nonlinear local singularity (#279). C: coexistence and causal separation (#280–281), all-order formal rigidity (#282–283), linear smooth uniqueness (#284–285), and now genuine local smooth exterior Killing rigidity under the stated periodic nondegenerate horizon assumptions. Two-sided smooth rigidity and universal causal emergence remain open.
