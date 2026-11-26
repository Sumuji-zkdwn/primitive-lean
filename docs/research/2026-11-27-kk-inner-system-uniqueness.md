# 2026-11-27 — Fixed-background inner linear uniqueness modulo flat gauge

## Claim, hypotheses and exact scope

Continue #290 on its exact head ae3cc662cabb7206cd927701092fd68b9c87737b (dedicated run 45725097794, exact-python successful, all steps successful). Let g=-2 dr dv+f dv²+r² gamma, f=1-s²/r², s>0, gamma the unit H³ metric, v periodic of period L. Work on the inner product collar s-d<r<s, 0<d<s, with an open screen coordinate patch. A smooth periodic linear vacuum perturbation h, with all transverse jets zero at r=s, is a pure coordinate perturbation h=L_Y g for a unique smooth periodic vector Y flat at r=s. No harmonic gauge assumption, no spatial integrability and no assumed analyticity of h. The original fixed background is analytic and v independent. If all horizon jets of h are circle invariant, there is a flat gauge correction making h circle invariant throughout the collar. This is linear and conditional on horizon data, not a general smooth nonlinear theorem.

Proof below uses the exact radial-gauge reduction of #290, the published system Fuchsian uniqueness theorem, local interior elliptic solvability and analytic regularity. The new exact Python audit verifies the algebraic hypotheses and residual gauge formulas; it does not prove these external analytic theorems.

## 1. Reduce to the actual weighted system

By #290, the triangular quadratures normalize h to h0=h-L_Y g with h0_rmu=0, preserving flatness, and Y unique among flat corrections. The radial-gauge representative still solves delta Ric=0. Fourier integrate on the v circle, fixing k=2 pi n/L. Put u=s-r, w=sqrt(u), D=u partial_u=(w/2)partial_w. Write h0_v*=w S_v*, h0_AB=S_AB, ten unknowns in S. Smooth flatness in u ensures smooth flatness of S in w, including after division by any fixed power of w.

The four normalized delta Ric_rv,rA rows and six delta Ric_AB rows, as audited in #290, have the form
    D² S + a D S + b S + R S=0,
where (a,b)=(0,-1/4) on four v slots and (iks,0) on six screen slots. R consists of analytic O(w) coefficient matrices multiplying partial_x^alpha D^j, j<=1, j+|alpha|<=2. The second radial coefficient is exactly the identity. The non-scalar second tangential derivatives are included. No additional Einstein equation is dropped from the hypothesis; these necessary rows are enough for the local argument.

## 2. Direct Volevic system; no scalarization

Set V=D S, U=(S,V). Then D U=M0 U+R1(w,x,partial_x) U with analytic O(w) residual. In the row S the only operator is the zeroth-order identity from V; in row V the derivatives on S have order at most two and those on V at most one. Choose Volevic integers n_S=0, n_V=1, for each of the ten components of each kind. The inequalities ord(Aij)<=n_i-n_j+1 hold even for non-scalar second screen derivatives (V from S allows order two; S from V allows order zero). This avoids the scalar-lift obstruction of #290, and also avoids introducing the thirty derivative variables proposed there.

Define W=w^(-4) U. Its first-order Euler equation is
    w partial_w W=A(w,x,partial_x) W,
    A=2 M0-4 I + O(w) differential terms.
All coefficients extend holomorphically near each real screen point and w=0 (the #290 row audit checks rational denominators nonzero at w=0). A(0,x,partial_x) has no tangential derivatives. The 20-by-20 indicial matrix has polynomial
    det(lambda I-A0)=(lambda+5)^4(lambda+3)^4(lambda+4)^6(lambda+4+2iks)^6 .
All roots have real part at most -3 including the zero mode. No assumption about diagonalizability or nonresonance is needed.

Apply Takeshi Mandai and Hidetoshi Tahara, Structure of Solutions to Fuchsian Systems of Partial Differential Equations, Nagoya Math. J. 169 (2003), 1–17, conditions (A-1), (A-2), Theorem 1.2 (pp. 2–3), DOI 10.1017/S0027763000008436. The PDF pages 2 and 3 were inspected, not merely the abstract. The result gives local distribution-valued uniqueness when the growth exponent L0 is strictly above the real parts of all indicial roots, and w^(-L0)W extends continuously as a distribution to w=0. Choose L0=0; smooth flatness implies the required continuity and C¹ regularity for w>0. Complex coefficients are admitted in the stated theorem; one could instead realify. Hence for each fixed k and each screen point x0, h0's mode vanishes in a product neighborhood of w=0,x0. The theorem is local in x and the neighborhood may depend on k. A direct inference of common Fourier neighborhood would be invalid.

## 3. Propagate a mode along each radial line via interior elliptic gauge

We need more than the selected radial-gauge rows to do this step. Use the full linear vacuum equation delta Ric[h0]=0.

Fix k, and any interior point (r0,x0), r0<s. Let D_g(h)=nabla^a h_ab-(1/2)nabla_b tr h. For a gauge vector Z, on this Ricci-flat background D_g(L_Z g)=Box_g Z_flat (up to musical isomorphism). Solve
    Box_g Z_flat = D_g(h0)
locally for the fixed mode on a small ball in (r,x) strictly inside the collar. There is no boundary condition at r=s. In this mode equation the principal operator is elliptic, with scalar positive matrix diag(-f,r^-2 gamma^AB) times the component identity. The coefficients are smooth and analytic, k fixed; complex first-order/zero-order terms cause no local obstruction. For clarity, local solvability follows by taking a sufficiently small ball, writing the principal term in divergence form, and using Dirichlet H^1_0 coercivity for the negative operator. Uniform positive principal part on the ball and the Poincare inequality absorb all bounded lower-order terms (including k-dependent coefficients). Lax–Milgram gives a weak solution for the smooth source, followed by interior elliptic regularity. The argument allows the ball size to depend on k. Raising the index produces a smooth local Z.

Now H=h0-L_Z g satisfies the harmonic gauge condition and full linear vacuum equation. The usual linearized Ricci identity gives a homogeneous Lichnerowicz wave equation for H, with curvature zeroth-order term. After the same mode separation the system is elliptic with analytic coefficients. Interior analytic regularity (Morrey and Nirenberg, On the analyticity of the solutions of linear elliptic systems of partial differential equations, CPAM 10 (1957), 271–290, DOI 10.1002/cpa.3160100204) implies H is analytic in (r,x) on the small ball. This does NOT imply Z or h0 is jointly analytic: residual radial gauges may contain arbitrary smooth screen functions.

The radial-slot identity 0=(h0)_rmu=H_rmu+(L_Z g)_rmu, and the exact #290 gauge formulas, imply
    partial_r Z^v = H_rr/2,
    partial_r Z^r = f partial_r Z^v - ik Z^v + H_rv,
    partial_r Z^A = r^-2 gamma^AB(-H_rB+partial_B Z^v).
These are triangular quadratures with jointly analytic inhomogeneity, on a product subpatch of the ball around r0. Choose the analytic particular solution with zero data on r=r0. Analyticity follows by integrating analytic functions on the short interval, in the displayed order. The difference is the homogeneous solution with smooth arbitrary initial screen functions a,b,c^A:
    Z_hom^v=a(x),
    Z_hom^r=b(x)-ik(r-r0)a(x),
    Z_hom^A=c^A(x)+gamma^AB partial_B a(x)(1/r0-1/r).
This formula is verified in all five radial slots by the new oracle. It is analytic in r at fixed x, and remains analytic in r after every finite screen derivative. The same is true for the analytic particular part. Consequently h0=H+L_Z g is analytic in r at each fixed x, since the metric is analytic and the Lie derivative uses at most one derivative. This argument works at every interior point, establishing real analyticity along every radial line for each fixed Fourier coefficient; it does not require a single interior gauge on the whole collar.

At each x, each mode already vanishes on a nonempty interval adjoining r=s by Section 2. The one-variable identity theorem now propagates zero along the entire connected radial interval (s-d,s). Fourier completeness on the circle gives h0=0 pointwise. Thus h=L_Y g with the flat Y previously obtained by #290. Uniqueness follows from homogeneous radial quadratures with zero horizon data. For invariant horizon jets, subtract the circle average and apply the result to the flat difference. The original analytic background commutes with circle translation, so the average remains a linear vacuum perturbation.

## 4. Scope, falsification and next gate

No independent matter, spinor, flux or additional physical field occurs. The background is Lorentzian, with local vacuum Einstein equations and their usual diffeomorphism symmetry, but its compact time orbits break global ordinary causal structure. This establishes uniqueness modulo coordinate changes of sufficiently smooth flat linear perturbations on a specific analytic vacuum solution with periodic generator, including nonscreen components. It does NOT establish dynamical formation of that solution, stability of the horizon under arbitrary initial data, nonlinear inner rigidity with merely smooth v-dependent coefficients, quantum physics, a global time arrow, or emergent observed interactions. In particular the Fourier and interior ellipticity steps use exact v independence of the background; perturbations need not have it. Do not substitute a general smooth coefficient system into the analytic theorem.

Petersen's Extension of Killing vector fields beyond compact Cauchy horizons (arXiv:1903.09135) proves stronger two-sided symmetry extension in a compact horizon setting; the present proof uses a fixed noncompact screen patch and linear data, not a priority claim. Next finite C task: test a genuinely nonlinear but circle-invariant comparison problem or seek smooth-coefficient inner unique continuation without mode separation. Keep exact A/B evidence and independent high-dimensional and gel branches; no main merge.

## 5. Exact audit and persistent ledger (2026-11-27)

New oracle tools/check_kk_inner_system_uniqueness.py actually executed with local SymPy 1.14.0. Four groups passed: exact indicial polynomial/root real parts, Volevic order and shift, residual radial gauge, interior principal symbol. Initial run failed because SymPy charpoly constructed a distinct symbol with different assumptions; switched to explicit determinant and reran. SHA256 65f32031166992c983adf40ae980af9f8cce984a1e27e76ca5be949299c11336; Git blob 46a6850fa273d44a782d2e775cb0af4e0291ee7b. Reproduce python -B tools/check_kk_inner_system_uniqueness.py. Dedicated CI also reruns the #290 actual row oracle. No Lean kernel proof of this analytic result.

Exact latest heads and run audit:
| PR | head | relevant run | result |
|---|---|---|---|
|176|ba1dc78f9be0ca3867fcaeb5b51dde01687c3ff2|44952037270|action_required, jobs empty|
|177|8a84ab5a623150c1dc2df6f8614e4b5f0df7d485|44953750468|action_required, jobs empty|
|178|5ce3ddc293417ffea43c79b99b16e36ff1594186|44954103336|action_required, jobs empty|
|179|cb0549a92dc2d7297093196788d6936f21418098|44955089236|action_required, jobs empty|
|183|8a6ffd4b9d91a5e3f41238da841b2a64b70a846c|44958061416 (integration)|action_required, jobs empty; own dedicated Lean audit not returned|
|270|a64d9e20dfb7e74ddf7f228bc81573c75d66206d|45500923284|action_required, jobs empty|
|274|160baa4c027728e6a1df1e1de26b8fc9e2dbd976|45710839538|action_required, jobs empty|
|290|ae3cc662cabb7206cd927701092fd68b9c87737b|45725097794|success, exact-python all steps passed|

No source failure established by these older empty-job runs. Do not claim repaired or Lean audits successful; no approval bypass.

A: #279 head 70a470e9019982164f488b4c42f5019a99a94513, compact exact constraint-satisfying arbitrarily small perturbations in each fixed Sobolev norm, not a canonical conserved finite energy theorem. B: #279 protected singular geodesic with invariant curvature blow-up, not generic instability/global inextendibility. #280 head 3bd4773112c9a20bc5b6d618984b8d862d73f02c gives smooth acausal extension coexisting with local blow-up; predecessor #279 trust-zero Lean algebra audit reported successful in #280. C: #281 head 5cd5ece2fbecb3c912e42f379bc09cd0d3402681 one-way barrier; #283 head a52947af5cee2136f6697d86e5d55e1a9b777bd3 all-order formal symmetry; #286 head 568fed86bb9f16c8f2c7f778f3a85426b7d3f4f5 exact smooth nonlinear exterior rigidity under specified horizon conditions; #289 harmonic-gauge inner linear result; #290 and this note now arbitrary-gauge flat linear inner uniqueness on fixed analytic background. All three A/B/C remain partial. Nonlinear inner rigidity, horizon formation/selection, thermodynamic arrow and quantum theory remain open. No new gel or high-dimensional claim this iteration.
