# 2026-11-26 — Compactly supported linear vacuum perturbations with divergent KK-horizon tidal curvature

## Scope and result
Follow-up to #270 and #274 (head 160baa4c027728e6a1df1e1de26b8fc9e2dbd976). On the **same** background with noncompact H^3 and periodic circle, there exist smooth, spatially compactly supported initial data for the linearized vacuum Einstein equation, arbitrarily small in every fixed initial Sobolev norm, whose linear gauge-invariant parallel-screen tidal split has unbounded absolute limsup at the horizon. This is an analytic localization argument using finite propagation, not a nonlinear instability proof. No topology replacement, added independent field, or source is used.

## Background, time slice and equation
Let s>0, r>s, f=1-s^2/r^2, v periodic of length L. Background g0=-2 dr dv+f dv^2+r^2 gamma, gamma=(dx^2+dy^2+dz^2)/z^2, z>0. In coordinates chi=v-r*(r), r*'=1/f, this is -dr^2/f+f dchi^2+r^2 gamma. The hypersurface Sigma_0={r=r0>s} is spacelike with induced metric f0 dchi^2+r0^2 gamma and unit normal n=sqrt(f0) partial_r at fixed chi (orientation irrelevant). On any closed r interval in (s,infinity), causal spatial speeds are bounded and the spatial metric is complete; hence inextendible causal curves cross all such slices, and the exterior admits a well-posed linear Cauchy problem.

Use only h_ij=2r^2 Q_ij with all base and mixed components zero, where Q is symmetric and transverse-traceless (TT) with respect to gamma on each slice. The tensor sector of the linearized vacuum equations is
    L Q - (Delta_gamma Q+2Q)/r^2 = 0,
    L=f partial_rr+(f'+3f/r)partial_r+2partial_rv+(3/r)partial_v .
Here Delta_gamma is the covariant rough Laplacian (negative spectrum convention). This follows from Ishibashi–Kodama 2011, eq. (104), with n=3, K=-1, lambda_L=k_T^2+2nK, and the base inverse metric g^{rr}=-f, g^{rv}=-1, g^{vv}=0. The same equation before multiplying by -1 is the base wave operator plus 3/r Dr dot DQ plus (Delta_gamma Q+2Q)/r^2. All other linearized Einstein equations vanish in the TT sector, so this supplies the linearized constraints as well as evolution. The constant curvature rough Laplacian preserves TT (trace commutes, divergence commutator is a linear combination of divergence and derivative of trace). Equivalently one may use the spectral tensor-sector evolution. Standard smooth normally hyperbolic Cauchy existence, uniqueness and domain of dependence apply on r>s. No claim of solving the exact nonlinear constraints is made.

## Explicit compact TT extension
Set D=diag(1,-1,0), U=z^-2 D. Exact connection calculation checks U is gamma-TT and Delta_gamma U=-2U. Thus Q_hom=p(r,v) U is precisely the previous homogeneous tensor shear, with Lp=0.
To avoid the invalid step of simply multiplying a TT tensor by a cutoff, define in Euclidean coordinates P_ij=delta_ij Delta_E-partial_i partial_j and the fourth-order local constant-coefficient operator on symmetric potentials A:
    T_ij=P_ik P_jl A_kl - (1/2)P_ij P_kl A_kl .
Its symbol P(q)=|q|^2 I-qq^T obeys Pq=0, P^2=|q|^2 P, tr P=2|q|^2. Therefore T is exactly symmetric, trace-free and divergence-free for any smooth symmetric A. Let B be a closed hyperbolic ball of radius R about X0 in the upper half-space, and choose a smooth compactly supported cutoff b identically one on a neighborhood of B. Such balls are compact in z>0. Put
    A=b(z log z/2) D .
On B, T=(partial_z^4 (z log z/2)) D=z^-3 D. Globally T is smooth compactly supported and Euclidean TT. Set W=z T. The exact conformal identities
    tr_gamma W=z^3 tr_E T,
    (div_gamma W)_j=z^3(div_E T)_j+z^2 delta_{jz} tr_E T
show W is gamma-TT and equals U on B. Compact support is preserved because the operator is local. No spatial boundary condition is added.

## Domain of dependence and finite energy
For a causal curve in the exterior, r is monotone and
    |dX/dr|_gamma <= 1/(r sqrt(f)) = 1/sqrt(r^2-s^2).
The entire hyperbolic displacement from r to r0 is bounded by
    acosh(r0/s)-acosh(r/s) < acosh(r0/s) = R_* < infinity .
Take R>R_* and use the entire periodic chi circle. Thus the causal past/future footprint on Sigma_0 of every point with X=X0 and s<r<=r0 (and an open neighborhood thereof) lies in B times the circle. Winding around the circle does not matter.

Pick k=2pi m/L, m nonzero, and let p be a real nonregular solution Re[e^(ikv) h(r)] of the previous radial ODE with h(r)=(r-s)^(-iks)(1+O(r-s)), locally convergent Frobenius expansion (extend to r0 by ordinary ODE uniqueness). For any real epsilon nonzero prescribe on Sigma_0
    Q=epsilon p W,  nQ=epsilon (n p) W .
The normal derivative here is at fixed chi, not fixed v. Both data are TT, periodic, smooth, and compactly supported in the full spatial slice H^3 times S^1. For example the positive initial quadratic norm
    E0=1/2 integral [|nQ|_gamma^2+f0^-1 |partial_chi Q|_gamma^2
                    +r0^-2 |nabla_gamma Q|_gamma^2+s^-2 |Q|_gamma^2]
                  r0^3 sqrt(f0) dchi dvol_gamma
is finite and scales as epsilon^2. Every fixed finite-order initial Sobolev norm is finite and scales as |epsilon|. This is an explicit positive perturbation energy norm on the initial slice, not a conserved canonical energy or an ADM mass (no global timelike Killing field in this exterior).
The resulting linear vacuum solution agrees exactly with epsilon p U in an open domain containing the fixed-v, X=X0 null ray, by uniqueness and finite propagation. By #274 the first-order tracefree parallel-propagated tidal split there is -2epsilon(p_rr+2p_r/r). Writing u=r-s, alpha=-iks, its complex leading amplitude is -2epsilon exp(ikv) alpha(alpha-1) u^(-2-iks); |alpha(alpha-1)|^2=(ks)^2(1+(ks)^2)>0. For real p, absolute limsup is infinite; the component oscillates, so there is no pointwise infinite limit. The gauge test is the same local screen identity as #274. No uniform smallness of the evolved derivatives is claimed. Hence finite initial energy and arbitrarily small initial Sobolev norms do not prevent this local linear curvature blow-up.

## Limits and prior literature
This is existence of special smooth linear data on a particular background and not genericity, nonlinear instability, an exact family of nonlinear constraint data, curvature blow-up for a fully evolved perturbed metric, or universal chronology protection. The positive initial norm is not a conserved invariant energy. The background extension with closed timelike curves remains a valid vacuum metric. Local Lorentzian covariance is unmodified; no extra matter/flux/spinor, quantum result, or SM recovery. Global causal order is assumed only in the exterior Cauchy problem; the proof cannot establish its universal emergence. The classical PDE, Frobenius and domain-of-dependence results are analytic inputs, not Lean-kernel theorems.
Prior art: Ishibashi & Kodama, https://arxiv.org/abs/1103.6148 eq. (104); Tafel, https://doi.org/10.1007/s10714-018-2355-7 (local TT constructions and conformal method); Denaro & Dotti, https://arxiv.org/abs/1505.01092 (flat Misner horizon instability). This is an application and explicit localization on the curved 5D geometry, not a claim of a new universal theorem.

## Reproduction and exact-head CI ledger
Local SymPy oracle: python -B tools/check_kk_horizon_localized.py. All four check groups passed (TT symbol and reproduction; conformal divergence and trace; homogeneous rough Laplacian; finite causal radius and leading coefficient). The local SHA256 is d2ab48ac8055b2c2a0b0888db68d563fad13869bd6dafdb9b6ea0df9f5d3ddb3. The dedicated Python workflow reruns the checks; no new Lean proof is claimed (local Lean unavailable).
2026-11-26 exact current heads and dedicated runs rechecked:
- #176 ba1dc78f9be0ca3867fcaeb5b51dde01687c3ff2 — 44952037270, 44952037252
- #177 8a84ab5a623150c1dc2df6f8614e4b5f0df7d485 — 44953750468
- #178 5ce3ddc293417ffea43c79b99b16e36ff1594186 — 44954103336
- #179 cb0549a92dc2d7297093196788d6936f21418098 — 44955089236
- #183 8a6ffd4b9d91a5e3f41238da841b2a64b70a846c — integration 44958061416, no dedicated run returned
- #264 f82fd28d786d4b0b5cdb763f9ea3350aa994882f — 45292820995
- #270 a64d9e20dfb7e74ddf7f228bc81573c75d66206d — 45500923284
- #274 160baa4c027728e6a1df1e1de26b8fc9e2dbd976 — 45710839538
All listed runs completed with action_required and jobs empty, so no failed source step to repair, no latest-head kernel PASS, no #183 dedicated audit confirmation. Keep approval blocker explicit; do not rerun or invent a source fix.

## Three-item time-structure ledger
A — PASS for arbitrarily small compactly supported **linearized** constraint-satisfying data in the initial positive norm above and unbounded tidal limsup. Still open: exact nonlinear constraint data lifting this construction, canonical energy if a suitable definition exists, genericity.
B — OPEN. Next finite task: derive the second-order vacuum constraints/backreaction equations for the local irregular branch (or an exact symmetry-reduced vacuum family), distinguish a singular perturbation expansion from genuine nonlinearity and C^2-inextendibility; check consistency at finite epsilon. Do not infer nonlinear instability merely from linear curvature.
C — OPEN. Compare dynamical and causal structure of exact perturbed solutions; test both causal and acausal branches, distinguish existence of CTCs from hyperbolic Cauchy predictability and thermodynamic arrow. Do not assume universal chronology protection.
Keep older high-dimensional vacuum and independent gel branches. Draft PR only; no main merge.
