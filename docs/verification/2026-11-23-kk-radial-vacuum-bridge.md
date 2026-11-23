# PR #199 follow-on: general radial KK/EMD bridge

Date: 2026-11-23 (JST). Remote repository: `Sumuji-zkdwn/primitive-lean`, PR #199. **Draft verification artifact uploaded in a separate follow-on PR; PR #199 and main are left unchanged.**

## Outcome and boundaries

An independent symbolic evaluator using SymPy 1.14.0 directly differentiates a five-dimensional metric and a separately constructed four-dimensional Einstein-frame metric. It checks all 25 components of the 5D Ricci tensor, all 16 components of the 4D Ricci-form EMD Einstein residual, all four Maxwell equations, and the nonlinear scalar equation. **Every identity passes in exact symbolic arithmetic with a general differentiable positive `H(r)`**. This is stronger as a family computation than PR #199's specialization `H=1+k/r`, but not a formally verified metric-to-curvature derivation in Lean, nor a new physical law.

The companion `KKRadialVacuumBridge.lean` is a proposed set of eight *rational-polynomial* proof certificates. **has no independently asserted kernel-success status** until the dedicated GitHub Actions job finishes. Its statements are separate from the SymPy calculations and no new Lean CI success is claimed.

## Ansatz and domain

Coordinate order: `(t,r,theta,varphi,psi)`, signature `(-,+,+,+,+)`. Assume a connected coordinate interval with `r>0`, `H(r)>0`, `H` twice differentiable, real constant `b`, and `0<theta<pi` (global circle patching not examined).

```text
G5 = -dt² + H(r)(dr²+r² dtheta²+r² sin²theta dvarphi²)
           + H(r)^(-1)(dpsi + b cos(theta) dvarphi)².
```

Two scalar defects encode the **entire** local vacuum test:

```text
L := r H'' + 2 H',
C := b² - (r² H')²,
Q := C + r³ H L.
```

The 5D Ricci tensor, obtained directly from the metric, has only these possibly nonzero components (with `s=sin(theta), u=cos(theta)`):

```text
R5_rr        = -L/(2 r H)
R5_thetatheta= -Q/(2 r² H²)
R5_varphivarphi = -[(r H s)²-(b u)²] Q/(2 r⁴ H⁴)
R5_varphipsi = R5_psivarphi = b u Q/(2 r⁴ H⁴)
R5_psipsi    = Q/(2 r⁴ H⁴)
```

All remaining matrix entries are exactly zero. It follows immediately that

```text
Ric5 = 0  <=>  R5_rr = R5_psipsi = 0  <=>  L = C = 0.
```

Nonzero denominators follow from `r>0,H>0`. This is a complete **local classification in this fixed ansatz**. From `L=0`, `(r² H')'=r L=0`; hence on a connected interval `r²H'=-a` for a constant `a`, so `H=c+a/r`. From `C=0` follows `b²=a²`, i.e. `b=±a`. The asymptotic choice `H(∞)=1` fixes `c=1`. Conversely these data make the entire Ricci tensor vanish. No uniqueness claim is made for unrestricted 5D vacuum metrics.

## The 4D EMD equations and their exact 5D residual bridge

Use `g4=-H^-1/2 dt² + H^1/2(dr²+r²dΩ²)`, `A=b cos(theta) dvarphi`, and `Phi=sqrt(3)/2 log H`. The action convention is `R4 - 1/2 (dPhi)² - 1/4 exp(-sqrt(3)Phi) F²`. The 4D residual `E_mu,nu` means

```text
Ric4_mu,nu - [ (1/2)d_mu Phi d_nu Phi
        +(1/2) e^(-sqrt(3)Phi) (F_mu,rho F_nu^rho -(1/4)g4_mu,nu F²)]
```

Direct independent differentiation gives:

```text
E_tt         = -Q/(4 r⁴ H³)
E_rr         = (C - r³ H L)/(4 r⁴ H²)
E_thetatheta = -Q/(4 r² H²)
E_varphivarphi = sin²(theta) E_thetatheta
E_other      = 0
Maxwell (all 4 components) = 0
D := Box Phi + (sqrt(3)/4) exp(-sqrt(3)Phi) F²
   = sqrt(3) Q/(2 r⁴ H^(5/2)).
```

The two systems satisfy these **exact componentwise identities** for every positive `H` in the ansatz:

```text
E_tt         = -(H/2) R5_psipsi
E_rr         = R5_rr + (H²/2) R5_psipsi
E_thetatheta = -(r² H²/2) R5_psipsi
E_varphivarphi = sin²(theta) E_thetatheta
D            = sqrt(3) H^(3/2) R5_psipsi.
```

Thus the 5D vacuum equations and the full 4D EMD equations are equivalent **within the radial ansatz**, not as general field-theory statements about arbitrary 5D/4D field configurations. In particular, the two nonredundant 4D Einstein residuals `E_tt=E_rr=0` already enforce `L=C=0`; the other components follow automatically. The angular Maxwell identity is kinematic for this ansatz and does not independently constrain `b`.

## A strong counterexample to scalar-only verification

The full five-dimensional scalar curvature is

```text
R5_scalar = -L/(2 r H²) - Q/(2 r⁴ H³).
```

Set `H=r^-2`, `b=0` (positive for `r>0`). The resulting metric is

```text
G5 = -dt² + dr²/r² + dΩ² + r² dpsi².
```

The scalar curvature is **exactly 0**, but the tensor is not vacuum:

```text
R5_rr=-r^-2,   R5_psipsi=-r².
```

Geometrically the spatial portion is locally a product of a 2D hyperbolic metric (scalar `-2`) with a unit 2-sphere (scalar `+2`). Their scalar curvatures cancel. Therefore substituting a single metric into the Einstein-Hilbert integrand and observing `R=0` does **not** certify the vacuum Einstein equations. Full tensor or equivalent independent residual testing is essential.

## Reproduction and next formalization task

Run from this directory:

```bash
python -B check_radial_bridge.py
```

The oracle derives inverse metrics from the supplied metrics (not from hardcoded inverse formulas), then builds Christoffels and Ricci tensors. It tests all residuals including off-diagonal terms for arbitrary differentiable `H`, then tests explicit on-shell and off-shell substitutions. It assumes smoothness of the symbolic function (not proved). SymPy exact simplification is not a Lean kernel.

The proposed Lean module formalizes polynomial numerators with independent `r, H, H', H'', b, sin(theta), cos(theta)` **as rational indeterminates**. Its 8 theorem declarations are uncompiled and should be treated as proof candidates only. One must next provide a verified coordinate derivative/Christoffel implementation in Lean (or a transparent expression-to-Lean certificate checker) that establishes these numerators equal the actual Ricci and EMD quantities. Only then can a kernel-level bridge be claimed. The analytic integration `(r²H')'=0 -> H=c+a/r` and the smooth global bundle/centre must also be formalized separately if a complete geometric theorem is desired.

## References

- Eguchi, Gilkey, Hanson, *Gravitation, gauge theories and differential geometry* (1980), Gibbons–Hawking metrics: https://empg.maths.ed.ac.uk/Activities/GT/EGH.pdf
- Gibbons–Hawking metric and harmonic-potential conventions: https://s3.cern.ch/inspire-prod-files-0/0fdcc9c7008509c7b76581477df827ce
- Primitive-lean PR #199: https://github.com/Sumuji-zkdwn/primitive-lean/pull/199

All original external formulas remain identified as existing mathematics. This investigation adds a reproducible, more general ansatz-specific verification and an explicit scalar-flat/non-vacuum counterexample, not a discovery of novel physical interactions.


## Follow-on check: can the monopole charge vary with radius?

Relax only the *constant charge* condition, writing \(A=B(r)\cos\theta\,d\varphi\).
This introduces \(F_{r\varphi}=B'(r)\cos\theta\), in addition to
\(F_{\theta\varphi}=-B(r)\sin\theta\).
For the same 4D Einstein-frame metric and dilaton, the separate symbolic
verifier tools/check_kk_radial_charge_profile.py derives:

\[
F_{\mu\nu}F^{\mu\nu}
=\frac{2}{H}\left(\frac{B^2}{r^4}
 +\frac{(B')^2}{r^2}\cot^2\theta\right).
\]

All four dilaton-weighted Maxwell *density* equations vanish except
the azimuthal residual:

\[
\partial_\mu(\sqrt{-g}\,H^{-3/2}F^{\mu\varphi})
=\cot\theta\;\partial_r\bigl(B'/H^2\bigr).
\]

Thus local Maxwell equations alone do **not** force \(B'=0\).
An explicit counterexample is \(H=1\), \(B(r)=b_0+cr\), which satisfies
the *local* Maxwell equations but has an invariant axis pole if \(c\ne0\).
This example is **not** claimed to solve the full Einstein–dilaton system.

If \(B'(r)\ne0\), then

\[
\lim_{\theta\to0^+}\sin^2\theta\,F^2
=\frac{2(B')^2}{Hr^2}>0.
\]

Since the polar axes are regular points of the round 2-sphere at
fixed \(r>0\), the magnetic curvature cannot extend smoothly across
those axes with \(B'(r)\ne0\). Regularity on a full sphere therefore
enforces \(B'=0\) *within this special potential ansatz*. The formal
surface integral from the polar coordinate chart is
\(\int_{S^2}F=-4\pi B(r)\); interpreting this as a global flux when
\(B'\ne0\) is **invalid** without a smooth atlas. The apparent
radius-dependent flux is another indicator of the hidden axis singularity,
not a violation of the global Bianchi identity.

This is an additional **local symbolic and regularity obstruction**,
not a general no-go theorem for variable magnetic fields in KK theory,
nor a global U(1)-bundle construction. The scripts check exact
coordinate expressions but do not formally prove smooth extension in Lean.
