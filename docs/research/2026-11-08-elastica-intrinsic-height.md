# Intrinsic height as a curvature-bearing Elastica quantity

Date: 2026-11-08 (JST). Source: `lean/Research/ElasticaIntrinsicHeight.lean`.
Dependency: existing `Elastica.Geometry` (its actual interval-integral reconstruction
`xCoord`, `yCoord`, and `curvature θ := deriv θ`). No changes to those definitions.

## Choice of meaning

The primitive is **not** absolute vertical elevation `y`. For the existing
unit-speed curve reconstructed from a lifted angle `θ`, the proposed signed
height from base parameter `s` to `t` is the normal displacement in the
curve's own frame:

`Hθ(s,t)=cos(θ(s))(y(t)-y(s))-sin(θ(s))(x(t)-x(s))`.

A parallel quantity is `Tθ(s,t)`, the tangential displacement. They both
arise from the same existing Elastica reconstruction; no new material entity,
physical height correction term, or independent curvature coordinate is added.

## Prose-to-proof mapping

| Statement | Lean declaration | Assumptions |
| --- | --- | --- |
| Height at its own base point is zero | `intrinsicHeight_self` | arbitrary angle |
| Longitudinal displacement at its own base point is zero | `intrinsicTangent_self` | arbitrary angle |
| Derivative of actual normal-displacement function | `hasDerivAt_intrinsicHeight` | continuous angle |
| First derivative of local height vanishes at base point | `deriv_intrinsicHeight_self` | continuous angle |
| Second derivative of local height recovers tangent-angle derivative | `intrinsicHeight_second_deriv_eq_curvature` | continuous angle; derivative exists at base point |
| Signed curvature is recoverable from height | `curvature_from_intrinsicHeight` | everywhere differentiable angle |
| Equality of local height functions implies equality of base curvature | `same_intrinsicHeight_implies_same_curvature` | everywhere differentiable angles |
| Non-additive gluing with intermediate turn and tangent | `intrinsicHeight_compose` | arbitrary angle |

The composition identity is:

`Hθ(s,u) = Hθ(s,t) + sin(θ(t)-θ(s)) Tθ(t,u) + cos(θ(t)-θ(s)) Hθ(t,u)`.

This is an **exact** identity; it does not assume piecewise-smooth gluing,
minimizer existence, equilibrium, or dynamics.

## Independent mathematical check

For the constant-curvature angle `θ(v)=k v` with nonzero `k`,
`Hθ(s,t)=(1-cos(k(t-s)))/k`. Symbolic differentiation gives
`∂²_t Hθ(s,t)|_(t=s)=k`. The exact gluing formula also simplifies to
zero difference under trigonometric identities (independent SymPy check).

## Verification discipline

The *baseline* source `lean/Elastica.lean` is protected by
`docs/integration/manifest.json` as byte-identical; do not modify it to
import this module. The separate GitHub Actions workflow
`elastica-intrinsic-height.yml` builds `Elastica.Geometry` and
runs `lake env lean --trust=0 Research/ElasticaIntrinsicHeight.lean`.

CI evidence on first head `d5be98bc69b72ca12d7cbfb8de9b65a4d59134f0`:
the dedicated run 42484534863 succeeded; the wider integration source audit
failed solely at its source-audit step after the root import was added. The
root was restored in a later commit; check the latest head's CI rather than
assuming the first integration result applies. No `sorry` or axioms added.

## Scope boundary

This proves a rigorous geometric **candidate definition** of intrinsic
height and its curvature information. It does not prove that all possible
uses of physical or gravitational 'height' must follow this definition, nor
that height alone determines a complete curve without initial data.

The joint linear-input checker enumerates `lean/Elastica/*.lean` and audits
those declarations through the byte-locked root import; an unimported module in
that directory gives unknown-identifier errors. For this reason the extension
lives under `lean/Research/` like existing standalone Elastica bridges.


## Reconstruction boundary: height and curvature as two resolutions of one Elastica geometry

**Mathematical interpretation (not a new Lean theorem).** Intrinsic normal height
and signed curvature are *not* two independent quantities that should be added
as a correction. They are finite-displacement and infinitesimal descriptions
of the **same** unit-speed Elastica curve. This statement concerns the *whole
two-point height family* versus the *whole curvature function*, not a single
height value versus a single curvature value.

For a continuously differentiable lifted tangent angle θ on a connected
interval, with the same oriented arc-length parameter on both sides:

$$
\left.\partial_t^2 H_\theta(s,t)\right|_{t=s}=\kappa_\theta(s),
\qquad
H_\theta(s,t)=\int_s^t\sin\left(\int_s^v\kappa_\theta(w)\,dw\right)\,dv.
$$

The first identity is the Lean-proved
intrinsicHeight_second_deriv_eq_curvature (and its differentiable-angle
corollary). The second follows by substituting
θ(v)-θ(s)=∫_s^v κθ(w)dw into the derivative formula for intrinsicHeight
and integrating from s, where Hθ(s,s)=0. It is a mathematical
consequence recorded here, **not** a newly checked Lean declaration.
Consequently the full two-point height family and the signed curvature
function determine one another under these regularity and parametrization
conditions. Absolute position and initial tangent angle are *not*
determined: to reconstruct xCoord and yCoord as an embedded plane curve,
one additionally specifies an initial point and an initial direction.
The quantities above are invariant under translation and global rotation.

**Sharp limits of the statement.** Equality of curvature at *one* base
point does not entail equality of the height functions. For
θ₁(v)=0 and θ₂(v)=v², both have κ(0)=0, whereas

$$
H_{\theta_1}(0,t)=0,\qquad
H_{\theta_2}(0,t)=\int_0^t\sin(v^2)\,dv>0
\quad (0<t<\sqrt{\pi}).
$$

More strongly, even the entire height function from *one fixed base
point* does not always recover the curvature function everywhere.
For example, let θ₊ and θ₋ agree on v≤1 as
(π/2)(2v-v²) and set θ₊(v)=π/2+(v-1)²,
θ₋(v)=π/2-(v-1)² for v>1. These are C¹ angle
functions with the same initial angle θ₊(0)=θ₋(0)=0.
They have equal sin(θ(v)) for every v and hence equal H(0,t)
for every t, yet their curvatures differ for v>1.
The sine-branch ambiguity disappears under an additional local
turning-angle restriction, e.g. |θ(v)-θ(s)|<π/2
throughout the relevant interval. None of these observations
negates the existing same_intrinsicHeight_implies_same_curvature
theorem, which only concerns curvature *at that base point*.

**Local-to-global joining.** The exact intrinsicHeight_compose law is

$$
H_\theta(s,u)=H_\theta(s,t)
+\sin(\theta(t)-\theta(s))\,T_\theta(t,u)
+\cos(\theta(t)-\theta(s))\,H_\theta(t,u).
$$

Thus intrinsic height does *not* compose by simple scalar addition:
the intervening tangent turn mixes the longitudinal and normal
displacements. For independently defined curve segments, geometric
C¹ joining requires matching endpoint positions and tangent directions;
C² joining also requires matching curvature (with the common oriented
arc-length convention). Closedness additionally requires zero net
xCoord/yCoord displacement and a compatible final tangent direction.
No variational extremality, equilibrium, gravity law, or motion equation
follows from these geometric identities alone.

**Short statement for a manuscript:** “Height and curvature are not
independent terms to be summed: intrinsic height records finite normal
displacement, while signed curvature is its second local derivative.
With full arc-length curvature data, the entire intrinsic-height family
is reconstructed by integration; local curvature at a single point
cannot determine global height or global shape.”
