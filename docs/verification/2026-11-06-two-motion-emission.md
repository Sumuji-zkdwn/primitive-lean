# Two-motion emission: conditional energy theorem and its limits

Date: 2026-11-06. PR #88. Base main: `67fdf6b74bbbcb20dc70e7bf98b90471e329aa91`.
This is a separate classical real model, not a continuation theorem for PR #86's
complex-amplitude observation model.

## Definitions and supplied equations

Set

    V = κ/2 * (y-g*x1*x2)^2,
    F = κ*(g*x1*x2-y),
    E_local = (v1²+ω1²*x1²+v2²+ω2²*x2²)/2 + V.

`SolvesAt` assumes actual `HasDerivAt` statements at the indicated time:

    x1'=v1,  v1'=-ω1²*x1-g*x2*F,
    x2'=v2,  v2'=-ω2²*x2-g*x1*F,
    y'=F/(2*c).

The last equation is the **supplied outgoing impedance law** of the reduced
model. This file does not prove a distributional delta-source PDE has this
retarded solution, nor does it infer the direction of radiation from a
time-reversible wave equation. Interval theorems apply to every supplied path
satisfying these equations; global existence/uniqueness is not assumed as a
new axiom and is not proved.

The actual partial derivatives of V are proved via `HasDerivAt`:

    ∂V/∂y=-F, ∂V/∂x1=g*x2*F, ∂V/∂x2=g*x1*F.

This justifies the backreaction terms for the chosen potential, but does not
derive Newton's dynamical rule or the particular coupling from rod geometry.

## Central results

`energy_chain_rule` first proves the derivative for arbitrary instantaneous
velocities and accelerations. Substitution of `SolvesAt` then proves

    dE_local/dt = -F²/(2*c).

`emitted c F T` is the actual real interval integral `∫ t in 0..T, F(t)^2/(2*c)`.
`energy_balance` uses the fundamental theorem of calculus to establish

    E_local(T) + emitted(c,F,T) = E_local(0).

For c>0 and T>0, continuity of F on [0,T] gives

    emitted(c,F,T)>0  iff  ∃t∈[0,T], F(t)≠0.

Continuity is derived from `SolvesAt` when this theorem is applied to the model.
For κ≥0 and c>0, T≥0, the integrated emitted work is between zero and the initial
local energy. This bounds accumulated emission in this unforced model.

### The stronger conditional 'always' theorem

`emitted_pos_iff_product_nonzero` assumes κ>0, c>0, g≠0, T>0, y(0)=0 and
`SolvesAt` at every point of [0,T], and proves

    emitted(c,F,T)>0  iff  ∃t∈[0,T], x1(t)*x2(t)≠0.

Proof intermediate statements:

1. F≡0 implies y'=0, hence y≡0 by FTC; the force formula then implies x1*x2≡0.
2. Zero drive with y(0)=0 gives y≡0: the square y² has derivative
   -(κ/c)y²≤0, so it is nonincreasing from zero and nonnegative. This proves the
   needed special uniqueness fact, rather than assuming it.
3. Combine with positivity of the nonnegative continuous integral.

This is not a statement that all two-body interactions must emit. It depends on
the selected coupling, outgoing law and initial boundary displacement.

## The spatial wave portion actually checked

The two explicitly defined branch profiles are y(t-s/c), y(t+s/c).
The proofs compute their actual time and space derivatives. With two supplied
derivatives of y, each branch satisfies q_tt=c²*q_ss. The same profiles propagate
unchanged along their outward characteristics.

For wave density `(qt²+c²*qs²)/2` and flux `-c²*qt*qs`, substituting their branch
derivatives gives density y'² and fluxes ±c*y'². At the source, y'=F/(2c) yields

    (right flux)-(left flux)=F²/(2c),
    -c²*(right slope-left slope)=F.

The slope-jump identity is algebraic. A theorem about a distribution-valued PDE
at s=0 has **not** been inferred from it. Nor is equality of emitted work with
a full-space integral of wave density formalized here. These missing bridges
must not be presented as already checked by the Lean kernel.

## A checked boundary of the claim

A separate closed unit-frequency oscillator has the polynomial excursion

    q(t)=t²-2t³+t⁴, v(t)=2t-6t²+4t³,
    J(t)=q''(t)+q(t).

Both actual derivatives and the equation are proved. q and v are zero at 0 and 1,
but q(1/2)=1/16 and J(0)=2. Thus a nonzero source can leave zero residual excitation
in a closed oscillator. This is not the outgoing model and does not contradict
its nonnegative accumulated-work theorem.

## Existing-source connection

The CI concatenates the **actual unchanged**
`linear_input/lean_check/Observation.lean` with the new bridge tail, after
importing the two new modules. `native_coupling_as_linear_input` identifies V
with the original `LinearInputObservation.energy A X u y` for

    A(y)=κ*y²/2+κ*g²*x1²*x2²/2, X(y)=y, u=κ*g*x1*x2.

The probe-recovery corollary uses the original `recover_coordinate` theorem.
Probe settings are not substituted for autonomous dynamics. The bridge neither
moves nor silently modifies original proof files.

`shifted_quartic` proves the exact cubic term λ*x0*η³ in a quartic potential
expanded around its specified stationary point. It does not derive spatial
mode-overlap coefficients or prove a specific elastica has nonzero coupling.

## Verification and independence

Pinned Lean: `leanprover/lean4:v4.30.0-rc2`.
Pinned Mathlib: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
The isolated workflow compiles every new module and the actual-source bridge
with `--trust=0`, rejects compiler warnings/errors, and audits all newly added
theorems against {propext, Classical.choice, Quot.sound}. Exact commit, run and
artifact identity are recorded in PR #88; candidate source counts alone do not
establish successful verification.

The independent standard-library Python checker uses exact `Fraction` arithmetic
on 243 states and five parameter sets. Coordinate central differences are exact
because each coordinate has degree ≤2 separately. It checks 6075 coordinate
partials, 1215 energy-rate cases, 1215 flux/jump cases, 625 shifted-quartic cases,
22 closed-mode derivative cases and one endpoint/excursion case. These are finite
regressions, not proofs of ODE existence or continuum integration.

The first run failed on a sign-normalization rewrite, a reserved Lean token and
style/deprecation lints; the subsequent fixes retain the intended mathematics.
New modules remain isolated from the historical all-library integration registry.
No merge into main, no change to PR #86 or pinned dependencies, no claim of
quantization, light speed, Maxwell dynamics, new particles or experimental physics.
