# 2026-11-26 — Exact nonlinear 5D vacuum shear replaces the smooth KK horizon with a curvature singularity

## Decision and bounded result

Continue the time-structure ledger in #275, stacked on #274 and following the geometry of #270. Construct a one-parameter family of *exact* vacuum solutions through the old geometry, with a homogeneous Bianchi V spatial shear and an unchanged periodic circle topology. Test invariant curvature at the past endpoint. The family breaks isotropy, not all spatial homogeneity. This is a local smooth-initial-data nonlinear instability witness (in compact-open C^k or homogeneous parameter topology), not a global finite-energy instability theorem. In particular it uses the circle zero mode, not a nonlinear lift of #275's localized nonzero Fourier mode. No new matter, independent scalar, flux, spinor, higher-curvature term, or topology change.

## Exact metric and integration

Let B=s^2>0, P real, D=sqrt(B^2+4P^2/3)>0, -infinity<tau<0, q=exp(D tau) in (0,1), z>0, chi periodic with the same period L as #270. Set
    C=B tau, p=P tau, w=log(D q/(1-q^2)), A=(w-C)/2,
    a=exp(A), b=exp(C), N=exp(3A+C)=a^3 b.
The metric is
    g=-N^2 d tau^2+b^2 d chi^2+a^2 z^-2 (exp(2p) dx^2+exp(-2p) dy^2+dz^2).
It is smooth Lorentzian throughout the open interval. For P<0 interchange x and y, so the tensor oracle may take P positive without loss of generality. Proper time t measured from the past endpoint obeys dt=N d tau. The intrinsic three-dimensional spatial metric at fixed tau has curvature -1/a^2: the anisotropic x,y rescalings at each fixed time are spatial diffeomorphisms, but their time derivatives create physical extrinsic shear.

For arbitrary smooth A,C,p in this ansatz, the exact 25 Ricci entries are:
    Ric_tau,tau=-3A''-C''+6(A')^2+6 A'C'-2(p')^2,
    Ric_chi,chi/g_chi,chi=C''/N^2,
    Ric_x,x/g_x,x=(A''+p''-2 exp(4A+2C))/N^2,
    Ric_y,y/g_y,y=(A''-p''-2 exp(4A+2C))/N^2,
    Ric_z,z/g_z,z=(A''-2 exp(4A+2C))/N^2,
    Ric_ab=0 for a != b.
Primes are tau derivatives. The vanishing mixed entries include the class-B momentum constraint. Thus all exact vacuum constraint and evolution equations in this family are satisfied, not just a reduced spatial equation.
Writing w=2A+C gives C''=p''=0, w''=4 exp(2w), and the remaining Ricci condition is
    (w')^2-4 exp(2w)=B^2+4P^2/3.
Indeed w'=D(1+q^2)/(1-q^2), w''=4D^2 q^2/(1-q^2)^2, and the first integral equals D^2. Hence the explicit family is exactly Ricci-flat. The spatially homogeneous zero mode requires a backreaction of order P^2 in A: at fixed tau, D-B=O(P^2), A(P)-A(0)=O(P^2), C unchanged. The scalar p is merely shorthand for metric anisotropy, not an independent matter field.

For P=0, q=b, a^2=B/(1-b^2), t^2=a^2-B, b=t/sqrt(t^2+B), dt/dtau=t(t^2+B). Therefore the original #264/#270 geometry is recovered exactly, including its smooth past continuation with closed timelike curves. At fixed interior slice tau_0<0, induced metric and extrinsic curvature vary smoothly with P (all local derivatives); for arbitrarily small nonzero P these data are arbitrarily close on every fixed compact set. Differentiating at P=0 gives the homogeneous circle zero-mode logarithmic shear p/P=tau=log(f)/(2B) in the original r chart, f=1-B/r^2. It is not the nonzero k oscillatory mode in #274/#275.

## Invariant curvature obstruction

Let M=(3D-B)/2>0. At q->0,
    a^2=D q^(1-B/D)/(1-q^2),
    N=D^(3/2) q^(M/D)/(1-q^2)^(3/2),
    t=integral_0^q N(u)/(D u) du ~ N/M.
Hence the past proper time is finite. Define the four Kasner exponents ordered (chi,x,y,z):
    k=(B,(D-B)/2+P,(D-B)/2-P,(D-B)/2)/M.
They sum to one, and their squares sum to one exactly by the vacuum parameter relation. For P!=0, D>B, so 0<k_z=(D-B)/(3D-B)<1.

Use the orthonormal frame from the metric and H_i=F_i'/N, where F_i=(C,A+p,A-p,A). Each comoving worldline is timelike geodesic because the lapse is spatially constant; the normalized spatial coordinate frame is parallel along it. The independent time-plane curvature is R_hat(0,i,0,i)=-(dH_i/dt+H_i^2). For i<j the spatial plane curvature is H_i H_j minus a^-2 if i,j both in the Bianchi V triple (zero intrinsic term for circle planes). The tensor oracle also checks the full pair-index curvature matrix: off-diagonal entries vanish except the two Codazzi terms (0,x),(x,z) and (0,y),(y,z), whose squares are a^-2(H_x-H_z)^2 and a^-2(H_y-H_z)^2. Thus the Lorentzian Kretschmann contraction is 4 times the sum of the ten diagonal plane squares minus 8 times the sum of those two mixed squares; the negative terms are not silently ignored.

Since F_i' tends to M k_i, F_i''=O(q^2), N'/N->M and t/N->1/M, we obtain t H_i->k_i and t^2 dH_i/dt->-k_i. Also a is asymptotic to a positive constant times t^k_z, so t^2/a^2->0 and t^2 H_i/a->0. Therefore
    lim_{t->0+} t^4 R_abcd R^abcd
       = K0 := 4 sum_i k_i^2(k_i-1)^2 + 4 sum_{i<j} k_i^2 k_j^2
       >= 4 k_z^2 (1-k_z)^2 > 0    (P!=0).
The curvature scalar tends to +infinity, not just a coordinate component. A C^2 metric continuation to any boundary point approached with t->0 is impossible. The curvature is spatially homogeneous, so this obstruction is not restricted to one exceptional comoving ray. At P=0, K0=0 and the original curvature 72 B^2/(t^2+B)^4 remains finite; the zero leading term alone would not establish that smoothness, which follows instead from the known explicit continuation. The nonzero-shear family has the time function tau on its exterior, so no closed causal curves exist there; its former smooth past horizon cannot be crossed in C^2. This is one dynamical selection mechanism within the ansatz, not a universal chronology-protection result and not a proof of a thermodynamic arrow.

## Important limitations and related work

H^3 is noncompact and the exact nonzero shear is homogeneous across it. Although data are arbitrarily close on compact subsets (and in local orthonormal component norms), their global perturbation energy / Sobolev norms need not be finite. #275 establishes compact-support arbitrarily small linearized data for the nonzero Fourier branch using a positive initial energy norm; this new exact family uses different initial data and cannot be combined with #275 to claim a nonlinear finite-total-energy result. An exact compactly supported constraint gluing construction and subsequent nonlinear domain-of-dependence argument, or a suitable finite-energy nonlinear PDE analysis, remain necessary. C^0 or other weak extensions are not ruled out by the scalar-curvature obstruction. Genericity, full inhomogeneous stability, universal causality, quantum effects and known particle physics remain open. Lorentzian covariance and vacuum Bianchi identities are maintained; the symmetry-restricted solutions are not globally Minkowski.

Related work: Denaro and Dotti, *Strong cosmic censorship and Misner spacetime* (2015), https://arxiv.org/abs/1505.01092, construct exact singular neighboring families of a flat Misner horizon including pure gravity. Halpern, *Exact Solutions of Five Dimensional Anisotropic Cosmologies* (2002), https://arxiv.org/abs/gr-qc/0203055, studies 5D vacuum Bianchi II/V anisotropic solutions with an additional noncompact coordinate. We give an explicit family and invariant check through this particular curved compact-circle background; we make no general novelty claim for Bianchi V integration or Kasner asymptotics.

## Evidence and gate ledger

Local exact SymPy 1.14.0 run: all five groups passed (25 Ricci components, closed form vacuum relation, orthonormal pair-index Riemann matrix, Kasner algebra and coefficient, background match). The first local run encountered an assertion comparing differently factored but equivalent polynomials, repaired by simplifying the difference; rerun passed. Tested script SHA256 b670b136c3ce6ea99de7581c30b2a60831a52b8c3ff67bce7b4befb92628e236, Git blob f5b4908efe533699194695d90f8d61336107629e; GitHub source fetched and blob matches. Reproduce with python -B tools/check_kk_horizon_nonlinear.py. The mathematical limit argument above uses analytic asymptotics, not just sample evaluations. Five Lean algebraic certificates are candidates until the dedicated trust-zero kernel and axiom audit completes; the full differential-geometric proof is not formalized in Lean.

Current predecessor CI:
- #275 755d6fac1dc0c6911d06973a247e0decc184511c, dedicated run 45717853208 success; exact-python job and reproduction step success. Python only, not Lean.
- #274 160baa4c027728e6a1df1e1de26b8fc9e2dbd976, dedicated run 45710839538 action_required.
- #270 a64d9e20dfb7e74ddf7f228bc81573c75d66206d, dedicated run 45500923284 action_required.
Other PR ledger remains in #275; this iteration is bounded to nonlinear follow-up, not a new audit of all unrelated branches.

A — PASS for compact support and small positive initial norm in linearized theory (#275, now dedicated Python CI verified); exact finite-energy data lifting still OPEN.
B — PASS for exact homogeneous neighboring vacuum family with positive scalar-curvature blowup and no C^2 continuation at past endpoint. OPEN for global finite-energy nonlinear data, genericity, k!=0 branch and weaker regularity.
C — PARTIAL: a specific smooth chronology-violating extension is replaced by a C^2-inextendible past boundary in the nonzero-shear family. Universal emergence/selection OPEN, retain counterexamples and do not assume causality.
Next finite task: test whether exact vacuum constraint gluing can embed this homogeneous interior in finite-energy exterior data on r=r0, with sufficient past domain of dependence; account for Killing initial-data obstructions. Alternatively analyze nonlinear nonzero-mode constraints with explicit norms. Do not infer genericity, do not merge main. Keep the separate effective gel branch.
