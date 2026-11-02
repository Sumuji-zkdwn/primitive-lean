# Temporal sampling and E-polynomial future equivalence (2026-11-01)

Source PR: builds on the verified head of the E/WFS future predictive bridge
PR #15, exact base SHA 4bf1c2236a08dea2571806e33b7dc79fad7346ea.
All previously checked proof source bodies remain unchanged. A new additive
module TemporalSampling.inc is inserted *after* all preceding supplement
namespaces. This report distinguishes formal proof scope from the independent
numerical smoke tests and from previously unverified applications.

## Time is an explicit observation schedule

Given a fixed deterministic transition U: α→α and an observer K: α→ω,
a sampling schedule sigma: Nat→Nat defines

  ScheduledEq(K,U,sigma,x,y)
    ↔ ∀n, K(U^[sigma(n)] x) = K(U^[sigma(n)] y).

Full future equivalence implies every sampled equivalence, regardless of
sigma. A surjective schedule loses no observation times.

For a fixed period m define SampledEq(K,U,m,x,y) using sigma(n)=m*n.
The **exact necessary and sufficient condition** for sampling to lose no
predictive distinctions is:

  (∀x y, SampledEq(x,y) → SampledEq(U x,U y))
    ↔ (∀x y, SampledEq(x,y) ↔ FutureEq(K,U,x,y)).

The left side says the sampled equivalence is a right congruence for **one
physical U update**, not merely U^[m]. There is no assumption of
finiteness or reversibility for this equivalence.

For m>0, equality of observations at *all* m phases
(j=0,...,m-1) and times m*n+j is exactly full future equality.
The proof uses Nat division/modulo. One phase alone can lose information.

An explicit block-iterate lemma also proves equivalence between
physical sampling at times m*n and repeated updates of U^[m];
the two descriptions agree, but an ordinary update U and the block
update U^[m] are NOT the same discrete-time model.

## Concrete polynomial E witness: the zero-parameter quarter-turn

Earlier verified module EWFSFutureBridge.inc identifies the original
energy-derived polynomial automorphism

  H(x,u)=(kx+λx³-cy-u,x).

For k=λ=c=y=0, let S(x,u)=(-u,x). Then S²(x,u)=(-x,-u).
Let K(x,u)=x. Directly in the old proof:

  FutureEq(K,S,z,w) ↔ z=w.

The new module proves:

  SampledEq(K,S,2,z,w) ↔ K(z)=K(w).

In particular, z=(0,0), w=(0,1) share **all even-time observations**,
but at time t=1 their x observations differ (0 and -1).
Thus sampling with period 2 fails the one-step congruence criterion.

## Why the WFS gauge does not repair aliasing

Define strictly positive intensity r=exp(x) and the actual WFS p=2 gauge
G₂(r)=(r²-1)/2. Since both exp and G₂|r>0 are injective,

  SampledEq(G₂∘exp∘K,S,2,z,w) ↔ K(z)=K(w),

whereas full-step WFS-gauged observations still distinguish every
state pair. A nonlinear *injective* perception reparameterization
cannot undo temporal aliasing from lost sampling phases.

WFS is not applied to E itself (whose values may be nonpositive),
and this proof does not assert a global cotangent conjugacy of S
on the positive-intensity domain.

## Independent tests

  python -B -X utf8 tools/check_temporal_sampling.py

Exhaustively enumerates all deterministic update and observation functions
on 1,2,3,4 labelled states (1,16,729,65,536 models respectively).
Checks sampling period m=1,2,3, one-step congruence iff exact future
equivalence, and all-phase reconstruction using pair-orbit bounds.
Also checks the E polynomial quarter-turn example and WFS2 observation.
This finite exhaustive check is not a substitute for Lean certification.

## Strict Lean verification

  python -B -X utf8 tools/verify.py --proof-only

The existing verifier assembles the unchanged base Lean source together
with registered supplements and checks them under pinned Lean and mathlib.
Success requires a zero exit code from Lean --trust=0, a complete axiom
audit for every public declaration, no prohibited proof tokens,
and no Lean warnings. Cite an exact GitHub Actions run SHA, not a PR's
status or unverified local arithmetic, to claim Lean verification.

## Boundaries

* Time is still discrete (Nat). Arbitrary schedules are modeled, not
  a continuous clock, Laakso geodesic flow, or a partial order of actions.
* An arbitrary time-dependent policy, stochastic process, or adaptive
  measurement schedule requires separate hypotheses and formalization.
* The previous finite cutoff N-r applies to finite deterministic
  fixed-block dynamics and does not automatically imply a continuous-time
  or real-plane bound.
* The WFS gauge has a positive-domain restriction; it cannot be applied
  to arbitrary signed E outputs.
* No nonlinear Fenchel biconjugacy invariance, Fourier/phase-space
  reconstruction, or all-packing optimum is asserted by these theorems.
