# A single curvature double-well generates two history-conditioned input stiffnesses

Date: 2026-11-07 JST. Continuation of [finite fiber hysteresis](2026-11-07-fiber-history-kernel.md) and the Okanohara Part I/II bridge.

## Primary mathematical sources
- Daisuke Okanohara, [A Thermodynamic Theory of Learning I: Irreversible Ensemble Transport and Epistemic Costs](https://arxiv.org/abs/2601.17607), 2026.
- Daisuke Okanohara, [A Thermodynamic Theory of Learning Part II: History-Dependent Reachability and Continual Learning](https://arxiv.org/abs/2602.07950v3), September 2026 revision. The relevant point is target-dependent, finite-horizon control cost rather than rank loss of old learning maps.

## Explicit new energy

Choose a single, nonnegative and asymmetric polynomial curvature density

`V(k) = ((k²-1)² * ((k+1)²+2))/16`.

It satisfies `V(-1)=V(+1)=0` and `V(k)≥0` for all real `k`.

Crucially, the curvatures of the wells differ: `V''(-1)=1` while `V''(+1)=3`, as independently checked by symbolic polynomial differentiation. The Lean extension verifies the equivalent *exact polynomial* second-order factorization, without yet using Mathlib's twice-differentiation operators:

`2V(-1+t) = t² * ((t-2)² * (t²+2))/8`;
`2V( 1+t) = t² * ((t+2)² * ((t+2)²+2))/8`.

Their smooth coefficients at `t=0` are respectively `1` and `3`. This directly distinguishes local second-order response with **equal** minimum energies, rather than assigning two arbitrary resistance values.

For an affine tangent angle `theta(s) = k*s` over length one, the *actual* existing `Elastica.energy` integral equals `V(k)`, using the retained `Elastica.energy_affine` theorem. Consequently both chosen curvature arcs have zero actual curvature-integral energy. These are two constant-curvature families; no claim is made that both have the same fixed physical endpoints.

## Finite mechanical/transport coupling

We introduce an explicit quadratic local response law as a controlled reduction, NOT as a theorem of hydrodynamics:

`W_q(z;p) = k_q*z²/2 - p*z`,
where `q ∈ {false,true}`, `k_false = 1`, `k_true = 3`,
`z` denotes a chosen generalized local displacement/flow-response coordinate and `p` its conjugate external pressure/force.

For any target `d`, choosing `p=k_q*d` yields

`W_q(z;k_q*d)-W_q(d;k_q*d) = (k_q/2)*(z-d)² ≥ 0`.

Therefore `d` is a global minimizer of this reduced quadratic work; because `k_q>0` it is unique. The squared input `p²=k_q²d²` reproduces the previous history-conditioned action, with the **stiffness values extracted from the one polynomial**.

The relay state itself follows from a *different* explicit energy reduction: evaluate actual Elastica energy at the two zero-energy affine curvature states, add the linear external work `-u*k_q_state` where `kappa(false)=-1, kappa(true)=1`, and a switching penalty of 2 between distinct states. The original `fiberStepEnergy` is recovered exactly. Therefore the existing `switchFiber` proof implies that the chosen relay minimizes the actual restricted curvature-integral plus work and dissipation.

This is a genuine syntactic Lean bridge to a previously proved actual integral, not an assumed energy symbol. However, the reduction still makes choices: the polynomial V, two-state restriction, switching penalty, identification of local curvature stiffness with input/flow resistance, and quadratic pressure work.

## Formal files and verification

- `lean/Research/OkanoharaTransport.lean`: 18 additional theorems (total 46), especially `curvature_double_well_integral`, `well_curvature_exact_variation`, `well_stiffness_eq_previous_resistance`, `curvature_flow_work_gap`, `curvature_flow_action_eq_prior_fiber_action`, `actual_curvature_step_eq_discrete_energy`, and `actual_curvature_switch_minimizes`.
- `tools/verify_okanohara_bridge.py`: audits `#print axioms` for each theorem, and runs the sidecar under `--trust=0`.
- `tests/test_okanohara_curvature.py`: independent exact Fraction finite-value checks of the polynomial identities, relay minimization and quadratic work. Finite tests are NOT mathematical proofs for all real numbers.
- CI: the existing protected Elastica library is built first. Standalone proofs are then checked and the original integration suite is run. Check the latest PR head and Actions result.

## Open questions / limits

1. The polynomial is an illustrative mechanical law, not an empirical constitutive fit to a particular yarn or fluid.
2. The quadratic response law is a second-order local approximation; no full nonlinear pressure–flux equation or viscosity law has been derived.
3. Comparing exact full nonlinear finite input/flow deformation costs may change the ratio away from 9:1 for large d.
4. Different boundary conditions may forbid transitions between two affine-curvature arcs, even when both minimize the unrestricted density.
5. To connect to Okanohara's general finite-horizon theorem, replace this one-coordinate quadratic action with a derived input-to-target linearization and its controllability Gramian, and explicitly distinguish initial-state pushforward from future-input response.
6. The previously proven exponential cascade action `9^n` assumes **multiplicative** stage gains, not ordinary additive hydraulic series resistance. The additive countermodel remains valid.
