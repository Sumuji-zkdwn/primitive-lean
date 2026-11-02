# WFS projective involution and four-phase Fourier aliasing

2026-11-01. Base: verified PR #17 commit
\`778439784ead915c518e09670898b5d85a57e0d1\`, which in turn builds
on PR #15's verified reversible polynomial E and future-minimal state bridge.

## Exact domain and computation

Take the zero-parameter E update \`spin(x,u)=(-u,x)\`, for which
\`spin^[2](x,u)=(-x,-u)\`. The x observer is sampled after every two
physical updates. With positive perceptual intensity \`r=exp(x)>0\`,
the WFS p=2 coordinate is

    z = G₂(r) = (r²-1)/2,    z > -1/2.

Two physical updates change r to 1/r, so the induced scalar
observation update is

    M(z) = -z/(1+2z).

On the exact physical domain z>-1/2, \`1+2z>0\`, the next coordinate
is again in z>-1/2, and \`M(M(z))=z\`. The 2x2 projective matrix
\`[[-1,0],[2,1]]\` squares to the identity and has determinant -1.
This is a fractional-linear Möbius representation of the **sampled
observer's dynamics**, not a claim that the original H is 1-dimensional
or that this map preserves all full-step x observations.

Proofs are registered in \`WFSMobiusFourier.inc\`.

## A finite 4-point Fourier witness

For x-observation of the four consecutive states of the same spin:

    a₀=x,   a₁=-u,   a₂=-x,   a₃=u.

With DFT convention \`A₁=(a₀-i a₁-a₂+i a₃)/4\`, the exact complex
coefficient is

    A₁ = (x + i u)/2.

The two even-time observations alone are \`(a₀,a₂)=(x,-x)\`.
They contain no u. The two odd-time observations
\`(a₁,a₃)=(-u,u)\` restore the missing quadrature.
In particular, states (0,0) and (0,1) have identical even samples but
different first Fourier coefficient. This is an **exact four-phase
temporal-aliasing example**, not a theorem about arbitrary sampled
functions, continuous Fourier transforms, or Shannon/Nyquist band limits.

## Distinguish three mathematical structures

- The full E map is polynomial and reversible on all of R².
- The time-2 sampled WFS coordinate is positive-domain
  fractional-linear, and changes according to M (an involution).
- The four-point Fourier coefficient records the phase u, whereas the
  stride-2 observation loses it.

Loss of u is caused by dropping observation phases, not by an injective
WFS gauge, nor by an invertible E coordinate transformation.
Fenchel duality is unchanged from PR #15 and is not being conflated
with sampling or the projective transformation.

## Verification scope

Files:
- \`linear_input/lean_check/WFSMobiusFourier.inc\`: additive Lean proofs
- \`tools/check_wfs_mobius_fourier.py\`: exact arithmetic and finite examples
- strict existing verifier registrations and CI

The user's pinned proof-only workflow invokes Lean \`--trust=0\`, all
declaration axiom audits, baseline proof preservation and warning checks:

    python -B -X utf8 tools/check_wfs_mobius_fourier.py
    python -B -X utf8 tools/verify.py --proof-only

New claims are only considered **Lean-verified after** a completed/success
CI run on the exact commit. No main-branch merge is requested.

## Not proved here

- Complex/real general Fourier analysis on arbitrary Laakso spaces
- Gauge invariance for arbitrary p on variable intensity input
- General Legendre-Fenchel exchange formulas with time subsampling
- Probabilistic measurement/aliasing or hardware GPU behavior
- General projective-geometric or topological classification of
  the underlying state space
