# 2026-11-26 — All-order vacuum horizon jet rigidity and analytic circle symmetry

## Result and assumptions

Continue #282 on the same local periodic null hypersurface. Assume a smooth five-dimensional vacuum Lorentzian metric in a periodic Gaussian-null collar
    g=-2 du dv+u F dv^2+2u b_A dv dx^A+q_AB dx^A dx^B,
where v has period L>0, u=0 is a smooth null hypersurface, the screen coordinates x label the closed generators, q is positive definite, and the mean nonaffinity is positive as in #282. Do not assume any Killing field, compactness of the entire horizon, or existence of a smooth horizon for generic initial data. Use the normalized chart of #282, with F(0,v,x)=2 kappa for a positive constant kappa, and all metric coefficients and their first transverse jets independent of v at u=0. The proof in #282 uses vacuum, periodic Raychaudhuri and the horizon Ricci equations. Its dedicated Python CI now passes.

We prove by induction that every finite transverse metric jet at u=0 is independent of v. If the metric coefficients in this normalized chart are additionally real analytic in u on a neighborhood of u=0 (for each fixed v,x), this implies an actual local circle Killing field, not merely a formal one. No unique continuation assertion for arbitrary smooth vacuum metrics is made.

## 1. Leading difference of two exact vacuum metrics

For an arbitrary fixed generator translation lambda modulo L, let g_tilde be the pullback by (u,v,x) -> (u,v+lambda,x). Both g and g_tilde solve the exact vacuum equations and have the same Gaussian-null gauge. Suppose all jets of g through order m-1 are v independent, with integer m>=2. Thus the difference delta g=g_tilde-g has the Taylor expansion
    delta g_vv=u^m a+O(u^(m+1)),
    delta g_vA=u^m w_A+O(u^(m+1)),
    delta g_AB=u^m H_AB+O(u^(m+1)),
    delta g_u*=0.
The coefficients a,w,H are smooth periodic functions of v,x. Here Taylor coefficients include division by m!, not raw derivatives. All error estimates below are smooth Taylor orders locally in v,x, so tangential derivatives preserve order and radial derivatives lower order by one. No small-amplitude expansion or linearized-vacuum hypothesis is imposed: we compare two exact solutions and isolate their first possible difference.

The inverse of g has
    g^uv=-1, g^vv=g^vA=0, g^AB=q^AB,
    g^uA=u b^A, g^uu=-u F+u^2 |b|_q^2.
At any horizon point take normal screen coordinates for Q=q|_H. This change of screen coordinates is independent of v, since Q is v independent by #282. At the point g^uv=-1, g^AB=delta^AB, all other inverse entries vanish. All background first metric derivatives there vanish except
    partial_u g_vv=F0=2 kappa, partial_u g_vA=B_A, partial_u g_AB=S_AB.
No restriction on B,S is imposed.

For clarity, the exact Ricci formula used (with the sign convention of #282) is
    R_bd = (1/2) g^ac (g_ad,bc + g_bc,ad - g_ac,bd - g_bd,ac)
            + g^ac g^ef (C_ebc C_fad - C_ebd C_fac),
    C_abc=(g_ac,b + g_ab,c - g_bc,a)/2 .
The inverse changes by O(u^m); products with bounded background derivatives are thus O(u^m). Products of two first-derivative differences are O(u^(2m-2))=O(u^m) for m>=2, and the cross terms are O(u^(m-1)). Therefore at order m-2 only the second radial derivatives of the leading differences, contracted with the horizon inverse, can contribute.

The exact algebra oracle computes those coefficients for arbitrary a,w,H:
    delta R_uv= -(m(m-1)/2) a u^(m-2)+O(u^(m-1)),
    delta R_uA= -(m(m-1)/2) w_A u^(m-2)+O(u^(m-1)),
    delta R_uu= -(m(m-1)/2) tr_Q(H) u^(m-2)+O(u^(m-1)).
Since both metrics are Ricci flat and m>=2, a=0, w_A=0 and tr_Q H=0. The first two eliminate the nonscreen components at order m; the trace equation is a consistency check, not necessary for the next step. The AB equations have no term at order m-2.

## 2. All-order recurrence for the screen difference

After eliminating a,w, the only possible order-m difference is in the screen. For delta R_AB at order m-1 the contributions are precisely:
- the inverse component g^uu=-u F0+O(u^2) contracted with the second radial derivative of the screen difference gives (m(m-1)/2) F0 H_AB;
- the inverse g^uv=-1 contracted with the mixed u,v derivative gives m partial_v H_AB;
- the cross term in the quadratic Christoffel expression gives (m/2) F0 H_AB. All terms involving B_A and S_AB cancel, as checked in all nine screen entries for arbitrary symmetric H,S and arbitrary B.
All other terms are O(u^m). In particular, tangential derivatives of delta g_v* are O(u^(m+1)), and their mixed u/tangential derivatives are O(u^m); their pure second radial derivatives cannot appear at this order in R_AB. The unknown order-(m+1) screen term would enter pure second radial derivatives multiplied by g^uu=O(u), also at O(u^m). In the second derivative contraction, g^uA=O(u) multiplying mixed u/screen derivatives contributes O(u^m); in the quadratic contraction inverse differences and products of two differences were already bounded. Thus there are no suppressed higher jets in the stated recurrence.

Adding yields
    delta R_AB = m u^(m-1) (partial_v H_AB + m kappa H_AB)+O(u^m).
Both Ricci tensors vanish. Hence on the whole horizon screen patch
    partial_v H_AB + m kappa H_AB=0.
For fixed x, each component solves H(v)=H(0) exp(-m kappa v); because H is periodic with period L and m kappa L>0, H(0)=0. This eliminates the full order-m metric difference. All component identities were established in normal screen coordinates at an arbitrary point; the screen coordinate changes do not depend on v, so the same homogeneous transport equation holds in the original screen chart.

The base m=2 follows from #282's equality of the metric and first transverse jet for every translation. As lambda was arbitrary, induction gives
    partial_u^j g_ab(0,v+lambda,x)=partial_u^j g_ab(0,v,x)
for every finite j>=0. Equivalently partial_u^j Lie_(partial_v) g=0 on H for all j. Tangential derivatives of these zero tensor-component functions vanish as well. This is an infinite-order Killing equation at the horizon, derived without assuming a Killing field. It applies on the periodic generator product patch, not to arbitrary dense or nonclosed generators.

## 3. Analytic conclusion, smooth gap and degenerate limit

If for fixed v,x the coefficients are real analytic in u on a common connected transverse interval containing zero, their equality of Taylor series implies equality throughout that interval by the identity theorem. Apply this separately to each translated pair. The metric is v independent, so Z=partial_v is a nonzero periodic Killing field in the collar. Equivalently joint real analyticity in the normalized Gaussian-null coordinates suffices. We do not assume an arbitrary smooth vacuum metric is analytic, nor claim that an unspecified analytic structure automatically makes this particular normalized chart analytic. The result imposes symmetry on any analytic vacuum collar satisfying the stated hypotheses.

The smooth case is distinct: a function such as exp(-1/u^2) sin(2 pi v/L), extended by zero at u=0, has every horizon jet zero yet is not v independent off H. This is an illustration of the gap, not a vacuum counterexample or a permissible exact metric perturbation. The nonlinear vacuum equations may exclude such flat remainders, but an independent unique continuation argument is needed, especially because our transverse screen patch need not be compact. If kappa=0, the m>=2 transport equation would be partial_v H=0 (for a translation difference, its mean is zero and this would eliminate it if the base jets were already equal). However the nondegenerate normalization and first-jet argument of #282 cannot simply be assumed in that case. No degenerate-horizon rigidity theorem is claimed.

The all-order result concerns local geometric circle symmetry, not the emergence of time orientation, the existence of the horizon itself from arbitrary initial data, or generic chronology protection. The earlier one-way causal results remain conditional on the smooth horizon geometry.

## 4. Reproducibility and relation to prior results

Local exact SymPy script tools/check_kk_horizon_all_jet_rigidity.py, run successfully, verifies (i) all leading radial constraints and zero leading screen term, (ii) all nine quadratic cross contractions, (iii) all nine mixed and inverse-radial contributions and the polynomial recurrence for symbolic integer m. It uses symbolic jets, not a truncation at any chosen maximum numerical order. SHA256 03eec65f388dab9be1fd9caa6be5ed116476f3d81f42d3c814661aca649c5d9c; Git blob 9b93db3b39c59992b66f8f3d37101f1f73f4ba14. Reproduce python -B tools/check_kk_horizon_all_jet_rigidity.py. The order bookkeeping, ODE, induction and analytic argument are hand proofs; not a Lean kernel proof or full nonlinear PDE solve. A dedicated Python CI is included.

#282 exact head 4e8a85d546e8748baaabae7c1414259effbe6839, dedicated run 45720755460 completed success. Older unresolved branches were not audited again in this bounded follow-up. No main merge.

Petersen and Racz, Symmetries of Vacuum Spacetimes with a Compact Cauchy Horizon of Constant Nonzero Surface Gravity (2023), https://doi.org/10.1007/s00023-023-01335-9 (preprint https://arxiv.org/abs/1809.02580), already establish infinite-order Killing data and, using a wave-equation theorem for compact Cauchy horizons, a genuine smooth Killing field on the globally hyperbolic side. Moncrief and Isenberg's earlier analytic closed-generator rigidity results are discussed in https://arxiv.org/abs/1807.10141. Our explicit local periodic-generator coordinate proof is a specialization/alternative calculation, not a priority claim for all-order Killing rigidity. It does not need global compactness for the jet recurrence, but it does require a product chart of closed generators and does not recover their full smooth theorem. Do not invoke the compact-horizon continuation theorem on the noncompact H^3 screen without checking its hypotheses.

## 5. Research ledger and next finite problem

A: exact small finite Sobolev norm vacuum data (#279).
B: local nonlinear invariant curvature divergence of the same data (#279).
C: coexistence with chronology violation (#280), one-way causal separation (#281), conditional horizon symmetry rigidity (#282 and this iteration). Formal all-order rigidity PASS; actual circle symmetry PASS under stated analyticity; smooth local unique continuation OPEN. Next bounded problem: study flat-remainder uniqueness for the periodic characteristic PDE on a noncompact/transverse-local screen, starting with a scalar wave or gauge-fixed linear tensor equation and a precisely stated support/regularity class. Separate counterexamples from pure-vacuum claims. Do not infer universal causal selection, time direction, entropy arrow, or physical unification. Preserve other high-dimensional vacuum and effective gel branches.
