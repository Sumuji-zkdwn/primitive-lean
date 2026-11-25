# 2026-11-26 — One-way causal barrier and nonunique extensions of the perturbed 5D vacuum

## Result and scope

Follow-up to #280 (and #279). For the particular smooth Hausdorff extension E of the maximal globally hyperbolic vacuum development M, identify its full chronology-violating set and determine causal reach between it and M. The old globally hyperbolic region is a future set in the strong causal sense: every future-directed causal curve starting there stays there. Its causal and chronological relations are therefore exactly unchanged by the extension. The added chronology-violating region is one chronological equivalence class, can send signals across the horizon to the old region, but cannot be reached by future-directed signals from it. The horizon itself is achronal, with closed null orbits, and contains no point on a closed timelike curve. Also prove two opposite circle-chart attachments cannot coexist in any Hausdorff extension fixing M pointwise, although circle reflection exchanges them. This is a classical causal-geometry result on these exact vacuum metrics, not derivation of time orientation, entropy increase, a physical transmitter model, or universal chronology protection.

## 1. Geometry and exact cone inequality

Use the extension constructed in #280 with M open, U=(s-d,s+d) x S^1 x V an attached collar, 0<d<s, V a connected open hyperbolic ball, and period L>0. The overlap is exactly r>s in U. Write
    A = {r<s} in U,   H = {r=s} in U.
As subsets of E, A and M are open, H is closed, and E is their disjoint union. The metric in U is
    g = -2 dr dv + f(r) dv^2 + r^2 gamma,   f=1-s^2/r^2.
The future time orientation is fixed by W=partial_r+partial_v, which is timelike because g(W,W)=f-2<0 and agrees with the exterior future direction of increasing r. The vector ell=partial_r is future null because g(W,ell)=-1. For any nonzero future causal tangent Y along a curve,
    g(ell,Y)=-v'<=0, hence v'>=0.
Here prime denotes the derivative with respect to the curve parameter, and v' is defined by the circle one-form dv (or a local lift). If v'=0 then Y is a positive multiple of ell, so X'=0 and r'>0. For v'>0, g(Y,Y)<=0 gives
    r' >= (f/2)v' + r^2 |X'|_gamma^2/(2v') >= (f/2)v'.
For a timelike tangent both inequalities needed for r'>(f/2)v' hold (the first is strict), and v'>0.

Set u=r-s and a(r)=(r+s)/(2r^2)>0, so f/2=a(r)u. The inequality, including the v'=0 case, is
    u' >= a(r)v' u.
On any compact parameter segment in the collar, let B(lambda)=integral a(r)v' d lambda. Then
    (exp(-B) u)' >= 0.
This holds almost everywhere for locally Lipschitz future causal curves with nonzero tangent almost everywhere, and integration yields
    u(lambda_2) >= exp(B(lambda_2)-B(lambda_1)) u(lambda_1).
All coefficients are bounded on compact local segments, with finite variation of the local circle lift, so the exponential is finite and positive. Thus u>0 cannot reach u=0 or u<0 in a future-directed segment, and u=0 cannot enter u<0. This integrating-factor argument is necessary at the horizon; the sign of a derivative at a single crossing point alone would not suffice. For a future timelike segment starting at H the inequality is strict at later parameter values, so it enters r>s if it remains in U. The symbolic oracle checks the precise norm identity, factorization, and null orientation, not the global integration argument.

## 2. Global future invariance and causal convexity

If a future causal curve starting in M ever leaves it, its first exit point belongs to H: a boundary point of M in E must be in the attached chart U with r=s, since A is open and disjoint from M. Immediately before the first exit the curve lies in U with r>s. The preceding inequality contradicts reaching r=s. A first exit exists on a compact parameter segment reaching the complement, since M is open. Thus J_E^+(M)=M (with the reflexive convention for J), and any causal curve with initial point in M stays in M. In particular, for any p,q in M,
    p <=_E q iff p <=_M q,
    p <<_E q iff p <<_M q.
This excludes causal shortcuts through the added region, not just closed timelike curves. M is causally convex in E. Its global hyperbolicity as an open spacetime with its induced metric remains, and its causal diamonds between points of M are unchanged. Strong causality in E at each point of M follows by taking small causally convex neighborhoods in M, since no future causal curve can leave M. We do not assert that E is globally hyperbolic or admits a global time function.

Similarly, a future causal curve starting on H cannot reach A: locally the integrating-factor inequality forbids it, and a curve that enters M cannot return. More formally a first entry into A would require crossing H; on a small chart segment around the infimum of entry times, the inequality from u=0 contradicts u<0. A timelike curve from H enters M immediately and cannot return. A causal curve lying in H has r'=0, so its norm is s^2 |X'|^2, implying X'=0, and v'>0 for nonzero future tangent. Consequently H is achronal in E, and its only nonconstant future closed causal curves (up to reparametrization and winding) are the closed null circle generators at fixed X. There is no closed timelike curve through H or M.

## 3. Entire chronology-violating set and one-way signals

For r<s the periodic generator partial_v is future timelike since f<0 and g(W,partial_v)=f-1<0. Every point of A lies on a closed timelike orbit, of proper length L sqrt(-f). Therefore the entire chronology-violating set {p:p<<p} in E is exactly A.

For any two points of A, choose a piecewise smooth path in (s-d,s) x V joining their (r,X) values. It has compact image, with f bounded above by a strictly negative constant. Its derivatives in a fixed parameter are bounded on each piece. Traverse it while increasing v by a sufficiently large positive amount T matching the final phase modulo L. In the lifted v parameter, the tangent has v'=1, r' and X' of order 1/T. Its norm is f-2r'+r^2|X'|^2, uniformly strictly negative for sufficiently large T; its inner product with W is also negative, by the uniform limit f-1<0. This constructs future timelike curves in both directions between any two points of A. Thus A is one chronology-violating equivalence class (Carter relation p~q iff p<<q<<p). It is a past set: I_E^-(A)=A, and also J_E^-(A)=A (by the barrier and the horizon statement). No closed causal curve can straddle A and M or H.

Nevertheless a future timelike integral curve of W, with fixed X, crosses from r<s to r>s in finite parameter and finite proper time on a compact segment. Its norm is f-2, with dr/dlambda=dv/dlambda=1. For every q on H or on U intersect M, choose the starting phase v at a smaller interior radius so that the W integral curve reaches q; all of A can reach that starting point. Consequently
    A subset I_E^-(q) for every q in H union (U intersect M).
For the whole exterior,
    I_E^+(A) intersect M = I_E^+(H) intersect M.
Indeed any future timelike curve from A into M crosses H, and each point of H is itself in I_E^+(A). These relations do not assert that every point of M lies in this future. At a fixed interior r,X the closed timelike orbit can be repeated any finite number of times before taking the same exit route. This is a geometrical statement about paths, not a physical clock model with arbitrary internally evolving state on a CTC. An exterior observer at a suitable receiving event can receive a future-directed causal influence from A, but cannot send an influence back there. No round-trip paradox or chronology violation for observers in M arises from this extension. It is not valid to infer that no information from A can be observed.

## 4. Opposite attachment choices and Hausdorff obstruction

In the old exterior diagonal chart chi mod L, define
    r*(r)=r+(s/2) log((r-s)/(r+s)),  r*'=1/f,
    v_+=chi+r*,  v_-=-chi+r*.
Either choice pulls back the same smooth collar metric -2 dr dv+f dv^2+r^2 gamma to the exterior. Both respect the same future orientation of increasing r. Replacing v by v_- in #280 gives another smooth Hausdorff extension E_- of the same M: the global Killing generator changes sign in this chart, but its squared norm and the invariant contraction of its derivative are unchanged, so the no-interior-accumulation proof and quotient argument apply unchanged. Both attachments obey the same one-way barrier. Since the seed data of #279 are chi independent with no mixed circle components, reflection chi->-chi is an initial-data isometry and extends to a time-orientation-preserving isometry of M by Cauchy uniqueness. It exchanges the two constructions as unmarked spacetimes. The following obstruction concerns marked extensions fixing M pointwise, not abstract isometry types.

Suppose a Hausdorff space contains both E_+ and E_- by continuous injective embeddings agreeing on M. Fix X in V, and arbitrary circle phases alpha and beta. For r>s the transition is v_-=-v_++2r* modulo L. Since r* strictly increases and tends to -infinity as r decreases to s, there is a sequence r_n decreasing to s with 2r*(r_n)=alpha+beta-nL for sufficiently large positive integers n. The single sequence of exterior points represented by (r_n,alpha,X) in the plus chart is represented by (r_n,beta,X) in the minus chart. Its image in the purported common space converges to both horizon images (s,alpha,X)_+ and (s,beta,X)_-. Hausdorffness forces them equal. Holding alpha fixed and varying beta over distinct phases contradicts injectivity of the minus embedding. Thus there is no common Hausdorff extension containing both marked extensions, and in particular no isometry between them restricting to the identity on M. This is a Misner-type nonuniqueness mechanism, not a classification of every possible extension.

## 5. Prior work and interpretation

Minguzzi, The boundary of the chronology violating set (2016), https://arxiv.org/abs/1603.08190, gives general chronology-boundary theory; Minguzzi, Lorentzian causality theory (2019), https://doi.org/10.1007/s41114-019-0019-x, reviews chronological equivalence classes, causal convexity and causality hierarchies. Especially relevant: Minguzzi, Chronology violations and the origin of time (2013), https://doi.org/10.1051/epjconf/20135801003, explicitly considers a past null boundary behind which lies a chronology-violating region and an origin-of-time interpretation. The broad idea that chronological and nonchronological regions coexist, separated by tilted light cones, is therefore not new. Our bounded contribution is its explicit verification and marked-extension obstruction for the particular 5D exact vacuum construction with small compact nonlinear perturbations and coexisting invariant curvature blow-up. Do not claim priority for the general causal mechanism, the Misner extension ambiguity, or emergent time.

Time orientation is selected as part of the Cauchy problem and the direction of the one-way horizon depends on it. No statistical mechanics, entropy increase, quantum theory, physical observability beyond geometric signal reach, universal causal selection, or particle-physics recovery has been derived. The model shows that an ordinary causal region can be protected against closed timelike paths even while connected to an acausal past. No proof that generic initial conditions yield this geometry.

## 6. Reproducibility and ledger

Local SymPy 1.14.0 script passed all four groups (exact cone and orientation identities; crossing; slow-path norm; opposite chart and radial integral). First run had a structural equality assertion failure for algebraically equivalent expressions; changed to simplify the difference and reran successfully. SHA256 d60d3bea3a64f370d5cd84527932d0b7cb3826214d197e24f291921bc1e6e060, Git blob 8a30d9c6d106359bde42f0dffb02b786e61d7f07. Reproduce python -B tools/check_kk_horizon_causal_barrier.py. Dedicated Python CI added. The global causal comparison, chronology classes and topology proofs are analytic; no Lean proof of them claimed.

#280 exact head 3bd4773112c9a20bc5b6d618984b8d862d73f02c, dedicated run 45720032506 success. #279 Python and Lean CI success recorded in #280. Older blocked branches not re-audited in this manual iteration. No main merge.

A: PASS for exact compact finite Sobolev perturbation norms. B: PASS for local nonlinear invariant curvature divergence of same data. C: partial result: the extended model is globally nonchronological, but its original exterior is a causally convex future set, with unchanged exterior causal relations and one-way communication from the chronology-violating past. Marked extension choice not unique. Universal emergence of time orientation and arrow remains open. Next finite task: compare stability of this one-way causal separation under perturbations of the regular collar that break the circle symmetry, or derive a necessary causal condition that does not presuppose a chosen temporal orientation; explicitly distinguish Cauchy predictability from thermodynamic arrow. Maintain separate high-dimensional and effective gel branches.
