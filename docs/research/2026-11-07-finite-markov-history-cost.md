# Finite Markov kernel for history-conditioned action cost

## Model and separation of roles

`lean/Research/FiniteMarkovTransport.lean` is an independent module importing the existing Okanohara–Elastica bridge. It leaves all existing proofs untouched.

- Position and hidden history each have two values. The observation reads position only.
- A past `relax` or `prime` operation updates the history register to 0 or 1 and leaves position unchanged. Thus both paths have observed position 0, while the future transition law can differ.
- A rational controlled Markov kernel on `Fin 2` keeps position 1 absorbing. From position 0, two controls `u,v ∈ {0, 1/6, 1/3, 1/2}` move probability mass to position 1 by `(u+v)/k(h)`, with `k(0)=1` and `k(1)=3`.
- The separate operation cost is the quadratic action `u²+v²`.

For target mass `d=1/3` at position 1, the finite kernel forces `u+v=1/3` when `h=0` and `u+v=1` when `h=1`. Exhaustive Lean case analysis proves that the minimum costs on the finite control grid are `1/18` and `1/2`; equal controls attain them. The past operation therefore changes future minimum action by a factor of 9, despite leaving the observed position fixed.

## Transport and action are distinct quantities

On the unit-spaced two-point position space, the squared ground cost is 1 for a move and 0 for staying. A coupling from source `δ₀` to target `(2/3)δ₀+(1/3)δ₁` is forced, so its finite transport cost is `1/3` under either history. The state marginals alone do not retain the hidden history; controlled action does.

At this target, the two-step action values agree exactly with the existing `Elastica.curvatureTwoStepMinCost` and equal half the existing one-step `requiredAction`: `1/18 = (1/9)/2`, `1/2 = (1)/2`. The factor 9 is obtained from the history-conditioned transition gain, and the finite enumeration certifies its minimum over the specified action grid.

## What is assumed and what is proved

The Lean file proves the row-stochasticity of both rational kernels, the update/readout counterexample, finite-grid optimality, the coupling marginal constraints and their forced transport cost, and the numerical equalities to existing quadratic-action definitions. The Python checker independently enumerates every finite state and control with `fractions.Fraction`; run it with `python -B tests/test_finite_markov_transport.py`.

The transition law itself chooses history-dependent gains 1 and 1/3. The Lean result therefore derives action cost from a specified finite controlled kernel; it does not derive those gains from physical fiber hysteresis or data. Part I's ensemble transport/epistemic-speed-limit setting and Part II's target-dependent reachability are broader claims. Part II also distinguishes geometric transport action from optimizer-input effort and free-energy change; identifying them requires an additional model, which this finite kernel supplies only for its own toy system. This code does not formalize a continuum Wasserstein theorem, entropy production, arbitrary-horizon controllability, or Okanohara's general learning theory. See the primary papers [Part I](https://arxiv.org/abs/2601.17607) and [Part II, revised version](https://arxiv.org/abs/2602.07950v3).

## Remaining proof obligations

1. Derive the history-conditioned transition gains from an explicit microscopic or empirically fitted state-transition model instead of choosing them.
2. Replace the four-level control alphabet by a rational or real control domain and prove the corresponding closed-form minimum for all feasible targets.
3. Extend the two-state endpoint comparison to a general finite coupling problem and a path-space action/controllability-Gramian result.
4. Relate the history register to an observed or inferable physical state, rather than inserting the past operation as an external update.

The source includes `#print axioms` directives for each theorem. The independent verifier runs Lean with `--trust=0` and audits those outputs; its result must be read from CI for the exact checked commit.
