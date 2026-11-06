# Okanohara finite transport / history-cost bridge (2026-11-07)

## Sources and revision

* D. Okanohara, *A Thermodynamic Theory of Learning I: Irreversible Ensemble Transport and Epistemic Costs*, [arXiv:2601.17607](https://arxiv.org/abs/2601.17607).
* D. Okanohara, *A Thermodynamic Theory of Learning Part II: History-Dependent Reachability and Continual Learning*, [arXiv:2602.07950v3](https://arxiv.org/abs/2602.07950v3), September 2026 revision. The current abstract uses controllability Gramians and target-dependent finite-horizon minimum energy, not the abandoned unconditional rank-loss claim in earlier versions.

## Checked mathematical interface

Module: `lean/Research/OkanoharaTransport.lean`, importing the unchanged `Elastica.ExponentialWeight` module.

1. `two_step_speed_limit` proves `(u+v)^2 ≤ 2*(u^2+v^2)`, a discrete two-unit-time scalar quadratic-action bound. `balanced_path_attains_bound` gives equality for constant velocity. This is **not** a theorem about arbitrary measures or Wasserstein-2.
2. `required_action_exact` encodes a one-dimensional **unit-horizon, constant-input** gain of `1/(1+h)`: required input for displacement `d` is `(1+h)*d`, so its action is `(1+h)^2*d^2`. `history_unit_cost_mono` proves monotonicity on nonnegative memory.
3. `same_observation_different_cost` proves two states with exactly the same observable position and different hidden history have different adaptation costs; `adaptation_cost_not_observation_factor` rules out any cost map from observable position alone.
4. `historyAugmentedEnergy` is the **explicit modelling choice** `Elastica.energy ε θ ℓ + (1+h)^2`; `energy_le_history_augmented` and `history_augmented_energy_mono` compare this with the existing, actual Elastica integral energy.
5. `history_weight_le_original` uses the **existing theorem** `Elastica.exp_neg_mul_le_exp_neg_mul_iff` to connect the additive history penalty to `Elastica.exponentialWeight`, which is defined from the whole integral energy, not from a modified curvature density.

## Logical status / limitations

The module demonstrates a genuine formal *interface* to the existing Elastica objects, rather than an identification of physical elastica with learning.

It does **not** prove Okanohara's continuous Epistemic Speed Limit, free-energy identity, general finite-horizon controllability-Gramian optimality, hysteretic constitutive behavior of physical fibers, or any exponential-time lower bound for inverse learning. Nor does `(1+h)^2` arise from a microscopic fiber model.

In particular, the scalar two-segment inequality is symmetric in transport direction. Direction-dependent adaptation cost appears only after extending the state with the hidden, history-dependent variable. A non-invertible observation is different from a dynamically irreversible transport.

## Finite-kernel follow-up

The finite-state transition and action comparison is now in the independent module [`Research/FiniteMarkovTransport.lean`](../../lean/Research/FiniteMarkovTransport.lean), with the exact-rational checker [`test_finite_markov_transport.py`](../../tests/test_finite_markov_transport.py) and a dedicated trust-zero verifier. It defines a rational kernel on `Fin 2`, a deterministic history-update kernel, an observation that forgets history, and a separate quadratic action. The exact target example has equal finite transport cost under both histories but a 9:1 two-step action gap. The history-conditioned gains are still chosen by the model; they have not been derived from measured fibers or a microscopic law.

A remaining connection is to the existing `LinearInputFutureObservation.FutureEq` / `LinearInputBayes` definitions, which remain in the composite `.inc` pipeline and are not imported by these standalone modules. Broader rational/real control domains and a general finite-horizon transport/action theorem also remain open.

## Verification

The CI workflow first builds the retained Elastica library, runs `tools/verify_okanohara_bridge.py` for the Okanohara–Elastica sidecar, then runs `tools/verify_finite_markov_transport.py` for the new module and its explicit axiom audit. The new checker compiles its dependency as an importable sidecar before checking the finite model with `--trust=0`. The original `lean/Elastica.lean` and Elastica proof files remain unchanged. Verification status is specific to the head SHA and Actions run reported on the PR.
