# E/WFS/Fenchel ↔ future-minimal prediction: integrated bridge

Date: 2026-11-01 (JST).
Base: PR #3 at commit \`4615fe466e614ef13ebd25f60c8a49f9a2740623\`.
All old proof sources remain byte-identical. This additive branch imports the
previously independently checked sources of PR #9 and PR #13 unchanged and
adds \`EWFSFutureBridge.inc\`.

## Mathematical data

With the original polynomial

\[
E(x,y;u,k,\lambda,a,c)
=\frac{\lambda}{4}x^4+\frac{k}{2}x^2
 +\frac a2y^2-cxy-ux,
\]

keep y,k,lambda,a,c fixed, and set

\[
H(x,u)=(kx+\lambda x^3-cy-u,\ x).
\]

Its polynomial inverse is already proven. These are actual coordinates of
the original E's signed gradient, not an arbitrary generic polynomial
automorphism or a proof of the Jacobian conjecture.

For a fixed deterministic update U and observer K define

\[
x\sim_{K,U}y\iff \forall n\in\mathbb N,\ K(U^n x)=K(U^n y).
\]

A reversible state coordinate transformation e transports both U and K;
the bridge proves exact equivalence of the old and new future relations.
The full output is a deterministic minimal quotient in PR #9's
\`FutureObservations.inc\`.

## Distinguish three different phenomena

**A. E itself is reversible; x-only instantaneous forgetting fails.**
Observing x at time 0 and at time 1 for the H update recovers

\[
x=x_0,\qquad u=k x_0+\lambda x_0^3-cy-x_1.
\]

Therefore the x-readout future equivalence on the **entire real plane**
is *equality of complete (x,u) pairs*. Every exact deterministic state
representation retaining x readout and respecting this H update must be
injective. This is stronger than the existing one-step counterexample
KHK≠KH for K(x,u)=(x,0).

**B. WFS positive-intensity coordinate changes do not invent
compression.** For all real x, define positive intensity exp(x), then
apply WFS G_2(r)=(r²-1)/2. Injectivity of the positive WFS gauge and exp
implies the future equivalence still equals equality of (x,u).
Here exp(x) is an **explicitly chosen observation**; the polynomial
E's x coordinate itself need not be positive.

**C. A different observer CAN produce a nontrivial exact compression.**
At k=λ=c=y=0, H(x,u)=(-u,x). The observable

\[
R(x,u)=1+x^2+u^2>0
\]

is invariant under H. Its future equivalence is exactly equality of R.
WFS G_2(R) has the same equivalence classes. Distinct states (1,0)
and (-1,0) are future-equivalent with respect to the radial observer,
while remaining distinct as full E states.
This R is not asserted to be the original E potential.

The finite bound N-r from \`FutureFiniteHorizon.inc\` applies only to
finite deterministic state spaces; H lives on an infinite real plane and
is NOT assigned an unjustified finite cutoff.

## WFS canonical lift versus Fenchel pairing

PR #13's original \`WFSCanonicalLift.inc\` proves that on positive
intensity r the WFS p=2 cotangent lift
(z,xi)=((r²-1)/2,u/r) preserves the differential one-form
xi dz=u dr, whereas a *new* xi*z pairing is not the original ur.
This is not a globally valid conjugacy of H because H does not in
general preserve the positive half-plane.

Fenchel's supremum with the original linear pairing ur is invariant under
full reparameterization; taking a new linear pairing xi G_2(r) is a
different duality with a computed counterexample.
These are retained as separate verified declarations, not collapsed
into a single unqualified "gauge" operation.

## Lean modules and verification

Copied verbatim from PR #9:
- \`FutureObservations.inc\`
- \`FutureFiniteHorizon.inc\`

Copied verbatim from PR #13:
- \`EWFSFenchel.inc\`
- \`WFSCanonicalLift.inc\`

New:
- \`EWFSFutureBridge.inc\` — conjugation theorem, complete E x-trace
  observability, WFS2 exp observation, invariant radial quotient
- \`tools/check_e_wfs_future_bridge.py\` — independent exact arithmetic checks

The existing validator (registered supplements in order) runs:

    python -B -X utf8 tools/check_future_observation.py
    python -B -X utf8 tools/check_e_wfs_fenchel.py
    python -B -X utf8 tools/check_e_wfs_future_bridge.py
    python -B -X utf8 tools/verify.py --proof-only

The last check invokes pinned Lean --trust=0 and checks axiom dependencies,
warning-free compilation, old declaration preservation, and forbidden proof
tokens. No assertion of Lean success is made before a matching workflow
run for the exact source commit reports completed/success.

### Out of scope

- WFS arbitrary-p cotangent bundles and global Hamiltonian equivalence;
- global Fenchel biconjugation under non-affine WFS coordinates;
- stochastic, partially controlled, time-dependent, or GPU observation
  updates without an explicitly fixed transition;
- Laakso spaces, Fourier transforms, Lab space, musical Buffon models;
- global Squares in Squares optimum or a dynamical "alien sort" optimum.
