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

## Next proof obligation

Formalize a finite Markov kernel on `Fin n` plus an explicit history-update operator, and derive (rather than assume) the change of control gain from a hysteretic finite transition law. Compare the resulting action with a finite optimal-transport coupling cost. If possible, connect the history-state observation map to the existing `LinearInputFutureObservation.FutureEq` / `LinearInputBayes` definitions; those are currently in the composite `.inc` pipeline, not importable standalone Elastica modules.

## Verification

The PR invokes `.github/workflows/primitive-lean-ci.yml` for changes under `lean/**`, with `tools/verify_okanohara_bridge.py` compiling this sidecar using `lake env lean --trust=0` and checking nine `#print axioms` outputs. The original `lean/Elastica.lean` is preserved byte-for-byte because the integration manifest protects the original source. Check the PR's latest commit SHA and Actions conclusion; this document makes no independent claim of local Lean execution.
