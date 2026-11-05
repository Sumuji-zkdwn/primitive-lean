# Moving arc-length curve: time and rotation kept independent

Date: 2026-11-05

## Model

For a continuous angle lift θ : ℝ → ℝ, initial point (x₀,y₀), velocity (vₓ,vᵧ), and fixed angle α, the module defines

X(s,t)=x₀+vₓt+x_{θ+α}(s),   Y(s,t)=y₀+vᵧt+y_{θ+α}(s),

where the existing Elastica.xCoord and Elastica.yCoord integrate (cos(θ+α), sin(θ+α)) over arc length s.

Thus s, t, and α are distinct inputs. The model prescribes constant translation and a fixed rotation; it does not give a dynamical law for the curve or identify time with arc length.

## Lean declarations

Source: lean/Elastica/MovingCurve.lean.

- movingX_time_displacement, movingY_time_displacement: time changes the position by exactly vₓ(t₁−t₀) and vᵧ(t₁−t₀); the displacement is independent of fixed α and the arc-length profile.
- hasDerivAt_movingX_arcLength, hasDerivAt_movingY_arcLength: the arc-length derivatives are cos(θ(s)+α) and sin(θ(s)+α).
- movingCurve_unit_speed_squared: the squared speed with respect to s is one.
- hasDerivAt_movingX_time, hasDerivAt_movingY_time: time derivatives equal the prescribed translation velocity components.
- moving_translation_distance_eq_time_sq: if vₓ²+vᵧ²=1, squared translation distance equals squared elapsed time.

## Scope boundary

These statements formalize only the explicit coordinate model used by the curve/surface intersection experiment. They do not formalize general surfaces, intersection completeness, projective transformations, or the research phrase “time = distance.” The final item is a conditional unit-speed identity, not a claim that elapsed time equals arc length along the rod.

## Verification

The repository CI has an explicit lake build Elastica.MovingCurve step. A successful exact-head run is required before treating these declarations as machine-checked; the integration audit also remains required.
