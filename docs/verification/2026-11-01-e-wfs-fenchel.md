# Polynomial E, WFS gauge and Fenchel duality — additive proof scope
Date: 2026-11-01. Parent is the current PR #3 branch; all earlier proof bodies remain byte-identical.

## Underlying original E (NOT an arbitrary polynomial map)

E(x,y;u,k,λ,a,c) = λx^4/4 + kx^2/2 + ay^2/2 - cxy - ux.

Fix (y,k,λ,a,c) and let (x,u) vary. The old
\`LinearInputVariablePairs.gradXu\` already supplies the analytic derivatives,
and \`gradXu_jacobian\` proves the Hessian determinant = -1.

The new orientation-adjusted update is

H(x,u) = (kx + λx^3 - cy - u, x),
H^{-1}(p,q) = (q, kq + λq^3 - cy - p).

The 2x2 Jacobian matrix is [[k+3λx²,-1],[1,0]],
with determinant 1. Both inverse compositions are proved by ring identities.
This is a special polynomial automorphism; it does **not** settle JC2.

## Three different forms of "forgetting"

1. The full pair H is bijective, so reversible updates preserve state identities.
2. Observing x alone is *not* a deterministic closed update under H:
   (0,0) and (0,1) have identical current x but different next x.
   The obstruction is proved for arbitrary parameters.
3. The stationary equation for k=-3,λ=4,cy=0 reads u=4x³-3x.
   Both x=-1 and x=1/2 yield u=-1, but the full pair H distinguishes them.
   In the quartic E at u=-1, x=1/2 is not a global minimizer:
   E(-1,-1)=-3/2 versus E(1/2,-1)=3/16.
   Hence taking only global minima cannot preserve all stationary branches.

## WFS positive observation gauges

The genuine WFS family is G_p(r)=(r^p-1)/p (p≠0) and G_0(r)=log r,
on strictly positive intensity r=I/I0. This proof supplement proves:
- G_2(r)=(r²-1)/2 is injective for r>0.
- A generic injective gauge never changes full future observational equivalence.
- G_2 preserves the latter for *positive-valued* observations only.
- The Fechner p=0 gauge has an explicit equivalence between R
  and the positive intensity subtype, via exp and log.

Nothing assumes E itself is positive or that a gauge on real energy output is
globally well-defined.

## Fenchel: two distinct pairings

A physical Fenchel score is u*r-V(r), here V(r)=r²/2 over r>0. Rewriting
r=exp(z) is a plain reindexing with the *original* ur pairing, so the
supremum is unchanged (\`physicalLogDual_eq_physicalDual\`).

Conversely, using the new *linear* pairing ξ G_2(r) changes the duality.
At ξ=u=1, the original physical score has maximum +1/2 (attained at r=1),
while the G_2 pairing ξ G_2(r)-V(r) is identically -1/2 on r>0.
The new proof gives exact witnesses and bounds for both scores.
This establishes non-equivalence of pairings even though the gauge
itself is injective. It does not prove a universal noncommutation statement
for all E or all WFS parameters.

## Canonical WFS lift: a second, compatible construction

On positive intensities r, the p=2 gauge has z=(r²-1)/2 and dz=r dr.
Transforming the conjugate variable to xi=u/r yields
xi dz=u dr, so the cotangent lift is canonical (determinant 1).
The physical E coupling is exactly
ur=xi*(2z+1), **not** xi*z. A new Legendre-Fenchel conjugate
which treats xi as a fixed dual variable is therefore a genuinely
different operation. At fixed physical u, the transformed xi=u/r is
state-dependent.

For Fechner p=0, z=log r and the corresponding momentum coefficient is
xi=r*u, giving xi*(dr/r)=u dr. The first-jet and differential identities
are kept separate from geometric symplectic claims in higher dimensions.

Module: \`WFSCanonicalLift.inc\`. No general WFS p-family differentiability
or global contact-geometric equivalence is asserted.

## Verification and limits

New registered supplemental proof source: \`EWFSFenchel.inc\`.
Independent exact-arithmetic tests: \`tools/check_e_wfs_fenchel.py\`.
The existing \`python -B -X utf8 tools/verify.py --proof-only\` is the
only accepted integrated proof verification; it runs Lean --trust=0
and full allowed-axiom/old-source preservation checks.

The source uses genuine lemmas from the existing \`LinearInputVariablePairs\`
family rather than fabricating a new E or guessing a general invertibility
claim. The proof does not establish a WFS-based Laakso topology, optimal
packing, Fourier invariance, or a global Fenchel biconjugacy classification.
These are separate future tasks.
