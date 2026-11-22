# Five-dimensional vacuum gravity produces a propagating Abelian vector — and requires a dilaton

Date: 2026-11-22 JST. Independent, new draft research branch based on main.
Prior linked gravity-only research: draft PR #181 (Ricci-flat KK monopole),
#185 (Taub–NUT SU(2)-type spin holonomy), #195 (smooth Riemannian
Ricci-flat Levi-Civita curvature solves induced Yang–Mills).

## What is new in the finite verification (not new physics)

The earlier Ricci-flat->Yang–Mills result is a consequence of the Bianchi
identity for a connection **fixed by** the chosen metric. It does not
guarantee *independent, propagating four-dimensional vector degrees of
freedom*. Here we switch to an actual Lorentzian five-dimensional
vacuum Einstein equation and test whether a free 4D U(1) gauge
perturbation emerges as a component of the same metric.

The background is Minkowski_4 x S1 with signature (-,+,+,+,+), and
all fields are independent of the circle coordinate w.
Take a **linearized** metric perturbation h_{mu,w}=h_{w,mu}=A_mu(x),
with h_{mu,nu}=h_{ww}=0 at first order. For a plane-wave profile

    A_mu(x) = epsilon_mu * exp(i k_nu x^nu),

the defining flat-background linearized Ricci formula gives

    Ric^(1)_{mu,w} =
       1/2 [ k² epsilon_mu - k_mu (k.epsilon) ] exp(i k.x),

with k²=-k0²+k1²+k2²+k3², k.epsilon the same Lorentzian pairing.
Other components of Ric^(1) vanish for this pure mixed
perturbation under the cylinder condition. Thus
k²=0 and k.epsilon=0 imply the complete linearized vacuum Einstein
equations. An explicit nonzero solution is

    k=(1,0,0,1), epsilon=(0,1,0,0),

which has F_01=k0 epsilon1-k1 epsilon0=1, so it is NOT pure gauge.
Under epsilon->epsilon+alpha*k both Ric^(1) and F remain unchanged.
This is the classical electromagnetic-wave kinetic equation arising
from **five-dimensional vacuum gravity**. We have not added a separate
fundamental Maxwell field: it is the cross-metric component.

These are established standard Kaluza–Klein results. Lean proves
the exact rational Fourier algebra and gauge covariance; an
independent SymPy oracle explicitly differentiates h twice in all
five coordinates to check the mixed linearized Ricci formula.

## Nonlinear counterweight: circle radius and backreaction

For an Abelian Kaluza–Klein ansatz

    ds5² = g_mu_nu dx^mu dx^nu +
           phi(x)^2 (dw + A_mu dx^mu)^2,

the five-dimensional Einstein–Hilbert Lagrangian reduces, up to
an integration-by-parts total derivative and circle volume, to

    sqrt(-g4) [ phi R4 - (phi³/4) F_mu_nu F^mu_nu ].

The full scalar curvature identity in (-,+,+,+,+) is

    R5 = R4 - (phi²/4) F² - (2/phi) Box_g(phi).

The dilaton/volume field phi is not optional in nonlinear generic
vacuum solutions. The 5D Ricci_ww equation in fixed-radius solutions
requires F²=0; a uniform non-null magnetic field cannot solve
the complete 5D vacuum Einstein equations with phi constant.

We independently calculate the FULL 5D Ricci tensor (25 components)
directly from Christoffels for the deliberately over-restricted
test metric:

    ds5²=-dt²+dx²+dy²+dz²+(dw + B*x*dy)².

It has det(G5)=-1, F_xy=B and F²=2B². Exact SymPy calculation yields

    R5=-B²/2, Ric_ww=B²/2.

So for B != 0 this metric fails 5D vacuum Einstein. The failure
is a physics boundary, not a bug: the U(1) vector may propagate
at linear order, but nonlinear curvature sources the metric/radius
sector. We do NOT infer that all non-null KK magnetic fields are
forbidden: varying phi and backreacting g4 can change the result.
We also do not infer that a gauge vector emerges as an independently
fundamental 4D field; it remains a degree of freedom of the 5D metric.

## Evidence and verification

- lean/Research/KKLinearizedMaxwell.lean:
  gauge covariance of the exact Fourier-space mixed linearized Ricci
  operator, explicit transverse null wave, nonvanishing gauge-invariant
  field strength, exact inverse of the representative 5D KK metric,
  algebraic curvature scalar/F² consistency and nonvacuum witness.
  The module uses measuredScalar5 and measuredRicciWW as definitions
  **whose correspondence to differential geometry is supplied by
  independent SymPy**, not proved in the Lean kernel.
- tools/check_kk_linearized_maxwell.py:
  5D flat-background linearized Ricci derivative calculations, null
  transverse wave and gauge invariance, independent 5D nonlinear
  Ricci tensor and scalar of the constant-B ansatz, circle coordinate
  transformation of A and gauge invariance of F. No floating point.
- .github/workflows/kk-linearized-maxwell.yml: exact-head pinned
  Lean --trust=0 kernel compile, axiom audit, and independent SymPy oracle.

## What remains for the gravity-only reconstruction goal

A dynamical Abelian 4D gauge field is a real intermediate result.
It is not a derivation of non-Abelian SU(2)xSU(3), chiral fermions,
coupling constants, quantum physics, or the correct observed spectrum.

The next controlled mathematical test is to allow a dynamical
phi and curved g4, and verify a fully nontrivial Ricci-flat
5D family beyond linear order that supports a propagating gauge
disturbance. For non-Abelian fields, an independent geometric
compactification and stability analysis are required. As always,
keep verified equations separate from phenomenological claims.

## Independent background sources

- Kaluza–Klein scalar curvature and complete reduction in mostly-plus
  signature:
  https://georgedouzas.github.io/posts/kaluza-klein-theories/part-iii-01-kaluza-klein-reduction.html
- Standard five-dimensional Einstein–Hilbert reduction, dilaton and
  gauge-action kinetic term:
  https://inspirehep.net/files/fcada1ad10a0e67bdfa95b6a74b96847
- General Kaluza–Klein reduced field equations including dilaton equation:
  https://open.metu.edu.tr/bitstream/handle/11511/64581/index.pdf

This is established classical mathematics and physics, not a novel
discovery, and the PR stays DRAFT pending exact-head CI.
