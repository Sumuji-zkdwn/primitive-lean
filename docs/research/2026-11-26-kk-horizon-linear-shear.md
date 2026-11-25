# 2026-11-26 — A pure metric Fourier shear has singular tidal curvature at the compact-circle horizon

## Decision and scope

Continue #270, without treating closed timelike curves alone as a contradiction, following the user's correction. The bounded question is whether the smooth horizon is stable in a specific linearized vacuum metric sector. PASS for a mode requires a bounded parallel-propagated, gauge-invariant first-order tidal tensor there. FAIL for this mode does not mean nonlinear instability, generic failure for finite-energy initial data, or a general chronology-protection theorem.

## CI and predecessor ledger

Current exact heads checked on 2026-11-26:
- #176 ba1dc78f9be0ca3867fcaeb5b51dde01687c3ff2, dedicated 44952037270 and 44952037252 action_required.
- #177 8a84ab5a623150c1dc2df6f8614e4b5f0df7d485, dedicated 44953750468 action_required.
- #178 5ce3ddc293417ffea43c79b99b16e36ff1594186, dedicated 44954103336 action_required.
- #179 cb0549a92dc2d7297093196788d6936f21418098, dedicated 44955089236 action_required.
- #183 8a6ffd4b9d91a5e3f41238da841b2a64b70a846c, integration 44958061416 action_required; no dedicated run returned.
- #264 f82fd28d786d4b0b5cdb763f9ea3350aa994882f, dedicated 45292820995 action_required.
- #270 a64d9e20dfb7e74ddf7f228bc81573c75d66206d, dedicated 45500923284 action_required, jobs empty.
Fetched head commit file lists for #176–179, #183 and #270 are generated-document updates. No failed source job was identified; do not invent a repair or label these heads kernel PASS. #183 audit remains unconfirmed. #270 records prior source PASS for #263 (45290183046) and #264 (45292779574); its own source run was not recovered in this execution. The delayed-gel branch remains separate and is not a metric-only theory.

## Exact metric computation

Let s=sqrt(beta)>0, r>0, z>0, v mod L, f=1-s²/r². The unperturbed 5D vacuum metric of #270 is

    g0=-2 dr dv+f dv²+(r²/z²)(dx²+dy²+dz²).

Its determinant remains negative and its curvature invariant is finite at r=s. Introduce a dimensionless *metric component* p(r,v), not a new matter field:

    g=-2 dr dv+f dv²+(r²/z²)(e^(2p) dx²+e^(-2p) dy²+dz²).

Direct Christoffel and Riemann computation gives all 25 Ricci entries, exactly (not just linearized). With a,b∈{r,v}:

    Ric_ab=-2 ∂a p ∂b p,
    Ric_xx/g_xx = Lp, Ric_yy/g_yy = -Lp, Ric_zz=0,
    Lp=f p_rr+(f'+3f/r)p_r+2p_rv+3p_v/r,

all remaining entries vanish. Hence p=epsilon ψ solves linearized vacuum iff Lψ=0. The nonlinear ansatz with *frozen* remaining components forces p constant (Ric_rr=Ric_vv=0). It cannot be promoted to an exact nonlinear wave without backreaction on the other metric components.

## A genuine tidal test, not a coordinate divergence

For each metric in the family, fixed v,x,y,z and varying r is a null ray with affine parameter r (all Γ^μ_rr=0). Its orthonormal transverse frame E_i=(g_ii)^(-1/2)∂i, i=x,y,z, is parallel transported. The exact x-minus-y optical tidal component is

    R(E_x,∂r,E_x,∂r)-R(E_y,∂r,E_y,∂r)
       = -2(p_rr+2 p_r/r).

The background has R_{a r j r}=0 for all a and transverse j and R_{i a j r} proportional to the transverse metric for every a. The script checks these identities, including off-diagonal zeros. Consequently the tracefree screen part of (Lie_ξ R)_{i r j r} vanishes for every smooth infinitesimal gauge vector ξ: differentiating the identically zero background screen components gives zero, and the remaining Lie derivative terms are zero or pure trace. Frame variations add no tracefree term. Thus the first-order tidal split is gauge invariant, not a singularity of an arbitrary metric coordinate component. This assertion is about smooth infinitesimal gauge transformations and the specified background screen.

## Fourier branches

Periodicity gives k=2πn/L, n integer. For k≠0 use the real part of ψ=e^(ikv)h(r), then

    f h''+(f'+3f/r+2ik)h'+(3ik/r)h=0.

Set u=r-s>0. The regular-singular normal form has indicial coefficients P0=1+iks, Q0=0. The indicial polynomial factors as α(α+iks), so α=0 or α=-iks. Their difference is not an integer; by the ordinary Frobenius existence theorem there are local convergent branches

    h_regular=1+O(u),
    h_singular=u^(-iks)(1+O(u)).

The first coefficients computed exactly are -3k/(2ks-2i) and 3k²s/[2(iks-1)], respectively. Both solve the same linearized vacuum equation outside the horizon. For a nonzero coefficient of the second branch the complex first-order tidal split behaves as

    -2 e^(ikv) α(α-1) u^(-2-iks) [1+O(u)].

Its magnitude diverges as u^-2, since |α(α-1)|²=(ks)²[1+(ks)²]>0. The corresponding real perturbation oscillates with logarithmic phase and has unbounded absolute limsup along every fixed-v radial ray. Do not say the real component has a pointwise limit of infinity. The regular branch has bounded curvature; smoothness at this horizon removes one local solution coefficient for each nonzero Fourier mode. The metric perturbation itself is bounded, but the tidal component measured in a parallel frame is unbounded. It reaches the horizon at finite affine parameter. This is a genuine local linear obstruction even though the exact background is smooth.

## Prior art and boundary

Denaro & Dotti, *Strong cosmic censorship and Misner spacetime* (2015), https://arxiv.org/abs/1505.01092, study neighboring solutions near the flat Misner horizon, including pure gravity. Petersen, *Wave equations with initial data on compact Cauchy horizons* (2018), https://arxiv.org/abs/1802.10057, treats regularity and existence for nondegenerate compact horizons. Related higher-dimensional horizon fragility: https://doi.org/10.1103/PhysRevD.109.084053. We independently computed this specific curved five-dimensional metric sector, not a claimed new general theorem. H³ is noncompact; this shear has no compact spatial support and is not shown to have finite total perturbation energy. No genericity, nonlinear stability, singularity of the full perturbed spacetime, quantum effect, or experimental result is inferred. The smooth unperturbed extension with closed curves remains an exact vacuum solution. Local Lorentzian covariance is maintained; global causal predictability is not assumed. The pure gravitational sector still provides no observed SM spectrum, chirality, couplings or quantum theory.

## Reproduction and next task

Python SymPy 1.14.0 local exact run: all 25 nonlinear Ricci entries, affine and parallel-screen identities, background gauge test, indicial roots, both first coefficients and leading tidal coefficient passed. Local script SHA256 2075d58af3846b153ec3d7ce950a8411d4960d498961bd4d3766a510bdfe6e8c. Reproduce: python -B tools/check_kk_horizon_shear.py. Five candidate Lean certificates only cover algebraic subclaims; dedicated workflow asks for pinned Lean --trust=0, theoremwise axiom audit, and the independent Python oracle; local Lean executable unavailable. Do not claim kernel PASS before actual CI success.

Next bounded task: replace the spatially homogeneous shear by an admissible finite-energy or compactly supported hyperbolic tensor perturbation and examine which nonregular coefficients are excited. Alternatively test a pure-gravity spacelike circle cap (KK bubble) without imposing spatial homogeneity. Keep the causal-loop branch as a mathematically valid exact background; no automatic main merge. Resume outstanding CI verification where access permits.
