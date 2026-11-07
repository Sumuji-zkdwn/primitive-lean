# Viscous rewrite proof candidate (2026-11-03)

## Source and assumptions

This branch adds `linear_input/lean_check/ViscousRewrite.inc` after the earlier
registered supplemental proofs. It reuses the exact existing polynomial
`LinearInputVariablePairs.energy` and its certified
`hasDerivAt_energy_x` derivative, and the F16 block samples from
`LinearInputF16UnexpectedBridges`.

Its proximal objective is
`Phi(z|old) = E(z,y;u) + alpha/2 * (z-old)^2`.
The source proves an exact polynomial parameter shift, global-minimizer
stationarity under an *explicit minimizer hypothesis*, a strong energy
dissipation inequality and a nonconvex two-minimum counterexample.
No claim that such a minimum exists for arbitrary parameters is made.
The finite F16 rotation block is skew in the Euclidean pairing, but
the separate reflection block is indefinite.

`alpha = eta/h` is the intended interpretation if `eta,h>0`.
Continuous-time limits, existence/uniqueness of trajectories, entropy
production from arbitrary F16 operators, and material viscosity laws
remain outside scope.

## Verification status

At initial upload this is a **proof candidate**, NOT a successful Lean build.
The exact research-branch Lean pin is `leanprover/lean4:v4.30.0-rc2`
with `mathlib4` revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
CI runs `python -B -X utf8 tools/verify.py --proof-only`; that checker
uses `--trust=0` and audits all declarations, rejecting warnings,
`sorry`, and unapproved axioms.

The source is additive to PR #3; no existing theorem is rewritten.
Check Actions logs and commit hash before asserting success.
