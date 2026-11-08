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
