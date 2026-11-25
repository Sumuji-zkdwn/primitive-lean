# 2026-11-26 — Flat radial gauge and weighted inner vacuum equations

## Result and scope

Follow-up to #289. Work on the fixed exact five-dimensional vacuum metric
    g=-2 dr dv+f dv^2+r^2 gamma, f=1-s^2/r^2,
where s>0, v has period L and gamma is the unit hyperbolic metric. Let h be any smooth periodic linear vacuum metric perturbation on an inner product collar s-d<r<s, with every regular-coordinate transverse jet zero at r=s. The condition D Ric_g[h]=0 is imposed, but no harmonic gauge, global spatial integrability or perturbation analyticity is assumed.

This iteration proves that the arbitrary-gauge flat perturbation problem reduces to a uniquely normalized radial-gauge problem, with all ten remaining unknowns satisfying an explicit monic second-order weighted Fuchsian system. The normalized indicial operator is diagonal. All ten equations and the non-scalar tangential principal coefficient are verified by exact symbolic calculations. It does NOT yet prove local uniqueness for this coupled system, hence does not claim arbitrary-gauge inner rigidity or full nonlinear rigidity.

## 1. Flat gauge correction by ordinary quadratures

Let Y be a contravariant vector field and h0=h-L_Y g. In the regular coordinates the Lie derivative in the five radial slots is exactly
    (L_Y g)_rr=-2 partial_r Y^v,
    (L_Y g)_rv=-partial_r Y^r+f partial_r Y^v-partial_v Y^v,
    (L_Y g)_rA=r^2 gamma_AB partial_r Y^B-partial_A Y^v.
The script verifies these identities for arbitrary Y, without any field equation or division by f.

Prescribe Y=0 at r=s and integrate in this order:
    partial_r Y^v=-h_rr/2,
    partial_r Y^r=f partial_r Y^v-partial_v Y^v-h_rv,
    partial_r Y^A=r^(-2) gamma^AB (h_rB+partial_B Y^v).
These are explicit integrals from s to r of regular smooth functions, with tangential derivatives under the integral. They define a unique smooth periodic Y in the product collar. Each integrand is flat at r=s, so Y and its derivatives are flat there; no inverse power of f or horizon singularity appears. The resulting h0 is flat and h0_rmu=0 for every mu. Linear diffeomorphism covariance gives D Ric_g[h0]=0. The homogeneous gauge equations also show that any flat Y for which (L_Y g)_rmu=0 must vanish identically, by the same triangular integration. Thus radial gauge is unique among flat gauge changes. In particular h is pure gauge by a flat vector if and only if h0=0. This avoids the unsolved inhomogeneous inner harmonic-gauge wave problem of #289.

If h has generator-independent jets instead of zero jets, subtract its circle average first. The background is circle invariant, so the difference solves the same linear vacuum equations and is flat. The quadratures apply to that difference. The statement about general perturbations is conditional on the prescribed horizon jets, not on arbitrary horizon formation.

## 2. Ten equations and their exact indicial operators

In the following write h for the radial-gauge representative. The unknown slots are (vv,vA,AB), four plus six. Fix a circle Fourier frequency k=2 pi n/L, so partial_v acts by ik. Put u=s-r>0, w=sqrt(u), D=u partial_u. For each Fourier coefficient use the weights
    h_vv=w S_vv, h_vA=w S_vA, h_AB=S_AB.
Since the original coefficient is smooth and flat in u, the rescaled S remains smooth and flat up to w=0 (and in u on the one-sided interval). There is no physical field associated with the rescaling.

Take the four equations delta Ric_rv=delta Ric_rA=0 and the six equations delta Ric_AB=0. These are necessary equations of the full linear vacuum system; proving uniqueness for them would suffice, but not every solution of them is asserted to solve all other Einstein components.

Normalize the first four equations by -2 w^3 and the six screen equations by 2w^4/f(s-w^2). With these factors, the exact coefficients of the weighted system are rational functions of w,s,z,k, regular at w=0 (s,z>0). Each row is monic in D^2 on its own component, with no other second-radial-order term at any w. All lower terms with their coefficients evaluated at w=0 vanish except those in the following diagonal indicial polynomials:
    for the four v-slots: (D+1/2)(D-1/2);
    for the six screen slots: D(D+iks).
The residual coefficients are O(w), analytic in w and the local screen variables, multiplying operators partial_x^alpha D^j with j<=1 and j+|alpha|<=2. There are no inverse powers of w in the normalized system.

Proof/evidence: the oracle differentiates the coordinate Ricci formula with respect to arbitrary metric jets in the ten slots (including the inverse variation delta g^-1=-g^-1 h g^-1). It substitutes partial_v=ik and partial_r^l(w^(2a) S)=(-1)^l w^(2a-2l) product_{j=0}^{l-1}(D+a-j) S, with a=1/2 or 0. For every actual coefficient it checks regularity, its limit at zero, the exact monic D^2 property and the differential order. All ten rows pass. The calculation is symbolic in k,s,z; it is not a grid test.

A flat solution may further be divided by u^2. This replaces D by D+2 and shifts the indicial roots to -5/2,-3/2 and -2,-2-iks, all strictly negative in real part. The shifted residual still has the same vanishing and order structure. This is a candidate for a system-level Fuchsian uniqueness theorem.

## 3. Why the previous scalarization cannot simply be reused

In harmonic gauge (#289), the highest screen principal coefficient was scalar on the component space. Here that is not so for the selected Ricci rows. For example in upper-half-space coordinates, delta Ric_xx contains the term
    -z^2/(2r^2) partial_x^2 h_yy.
The normalized screen equation contains
    [u z^2/(2s-u)] partial_x^2 S_yy,
a nonzero off-diagonal second tangential derivative. The oracle verifies this coefficient exactly. Multiplying the two kinds of diagonal indicial polynomial by monic degree-two row factors to obtain a common fourth-order indicial polynomial does not change this top tangential coupling into a scalar coefficient: it creates a non-scalar term D^2 partial_x^2. Encoding that matrix by an auxiliary-variable derivative as in #289 would raise the total order to five, greater than four. Consequently that direct encoding does not satisfy the order bound in Lope's scalar theorem. This is a limitation of this particular choice of rows/encoding, not an impossibility of all scalarizations; the other Einstein constraints or an alternative first-order formulation might remove the issue.

## 4. First-order system suitable for the next test

The reduction also yields a regular-singular first-order system without derivative loss in its order bookkeeping. Set q=u^(1/4), so w=q^2 and D=(q/4)partial_q. Before the optional indicial shift define V=D S and Z_A=q partial_A S. Then D S=V, D Z_A=Z_A/4+q partial_A V. The equation for D V follows from the ten monic second-order equations: every residual second screen derivative is rewritten as q^(-1) partial_A Z_B, and the O(q^2) coefficient becomes O(q). Mixed D/screen derivatives have O(q^2) coefficients on partial_A V. First screen derivatives may be written q^(-1) Z_A, also with O(q) coefficient. Thus for U=(S,V,Z_A), the augmented system has the form
    D U = M0 U + O(q) U + sum_A O(q) partial_A U
with analytic coefficients in q and x (for each fixed k), and a constant M0 having eigenvalues +1/4 from Z, and the four/six blocks' indicial roots stated above. Divide all components by u^2 to shift M0 by -2 I. The resulting first-order system has strictly negative real-part indicial eigenvalues. Smooth flatness makes the divisions legitimate and extends all new variables smoothly to q=0. This step is algebraic order bookkeeping, not yet a published system uniqueness theorem application.

The remaining proof must justify local smooth/distribution uniqueness for this coupled analytic-coefficient regular-singular system, without silently replacing a scalar theorem by a system theorem. Also, a mode-by-mode argument yielding only a frequency-dependent neighborhood must not use Fourier completeness to claim a common neighborhood before addressing continuation of each mode. These are separate analytic gates.

## 5. Literature and audit

Lope, Existence and Uniqueness Theorems for a Class of Linear Fuchsian Partial Differential Equations, J. Math. Sci. Univ. Tokyo 6 (1999), 527–538, theorem 2, p.529, https://www.ms.u-tokyo.ac.jp/journal/pdf/jms060304.pdf . The theorem concerns a scalar order-m Euler operator with j+|alpha|<=m and weighted tangential coefficients; the order obstruction in section 3 is why it is not used here to claim uniqueness.

Potential system approaches: Mandai and Tahara, Structure of solutions to Fuchsian systems of partial differential equations, Nagoya Math. J. 169 (2003), 1–17, doi:10.1017/S0027763000008436 (holomorphic solution structure); Oaku and Yamazaki, Higher-Codimensional Boundary Value Problems and F-Mild Microfunctions, Publ. RIMS 34 (1998), 383–437, doi:10.2977/prims/1195144513 (system-level uniqueness under its hypotheses). Their applicability to the real smooth flat solutions of this reduction has not yet been established. No claim of general novelty or theorem verification beyond the stated scope.

Actually executed the exact script locally with Python/SymPy 1.14.0. The five radial gauge identities, all ten weighted rows, the off-diagonal coefficient and shifted root checks passed. SHA256 c23a5761fd08134d731195d9401ef51669e917403afbc19444fc91af9fff4bfb, Git blob e421d050b6617014f6e1f059af0a883aff63be15; uploaded blob verified. Reproduce with python -B tools/check_kk_horizon_inner_radial_gauge.py. Dedicated Python CI added. No Lean proof, numerical PDE evolution or proof of local PDE uniqueness in this iteration.

Predecessor #289 exact head 1d3fb72e95592076e3da0ef2d51c4d750d95d790, run 45723697382 completed success. Older branches not re-audited in this bounded continuation; their outstanding approvals are not claimed resolved.

A/B remain established in #279 in their stated finite-norm, local nonlinear sense. C: causal coexistence, one-way barrier, formal symmetry and exact smooth exterior rigidity as recorded in #280–286. Inner fixed-background gauge-fixed linear uniqueness #289 remains established in its stated class. Here flat radial-gauge attainment and the full weighted necessary system are verified; inner arbitrary-gauge uniqueness remains OPEN. Next finite task: prove or find a suitable system-level local uniqueness theorem for Section 4, and check mode continuation. General smooth nonlinear inner rigidity, horizon formation, causality selection, time orientation and physical unification remain open. Keep independent high-dimensional vacuum and effective gel branches. Draft only; no main merge.
