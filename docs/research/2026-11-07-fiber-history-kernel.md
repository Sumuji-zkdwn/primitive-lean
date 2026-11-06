# Hysteretic fibers as a finite history-dependent transport kernel

Date: 2026-11-07 JST. Follow-up to [Okanohara transport bridge](2026-11-07-okanohara-learning-transport.md).

## Primary references

- Daisuke Okanohara (2026), *A Thermodynamic Theory of Learning I: Irreversible Ensemble Transport and Epistemic Costs*, https://arxiv.org/abs/2601.17607
- Daisuke Okanohara (2026), *A Thermodynamic Theory of Learning Part II: History-Dependent Reachability and Continual Learning*, v3 revised 2026-09-06, https://arxiv.org/html/2602.07950v3
- Relevant distinctions in Part II: Sections 2–4 (target-dependent future-input Gramian vs initial-state deformation), Section 7 (history-dependent gain) and Appendix B (withdrawn scalar-capacity assertions).

## New finite model and constructive proof obligations

The extension in `lean/Research/OkanoharaTransport.lean` introduces a binary fiber state `q : Bool`. A drive pulse above +1 sets `q = true`, below -1 sets `q = false`, and within the interval the fiber holds its previous state. These thresholds are **chosen** to define a minimal relay hysteron, not inferred from experimental fluid mechanics.

A chosen constitutive law assigns `h(false)=0`, `h(true)=2` and `R(q)=1+h(q)`. The control-response law is `displacement = input / R(q)`, directly matching the scalar gain example in Okanohara Part II §7. As the switching rule determines `q`, it now generates a history-dependent input cost `(R(q)*d)^2`, rather than stipulating a free history penalty.

Both histories start from `q=false`, then receive pulse +2 or -2 and return to zero drive. The final external drive and observable position agree, but `q=true` after the positive pulse and `q=false` after the negative pulse. For unit target displacement, the required quadratic input is **9 vs 1**. Thus the action cannot factor through the present observed position alone.

For the finite-ensemble analogue, a deterministic pushforward takes a mass `p : Bool → ℝ` through `switchFiber`. The positive pulse sends all mass to `true`, so the distinct initial Dirac measures become identical. This is loss of state distinguishability under a noninjective state update. It is different from small-gain ill conditioning: the two effects are exhibited separately.

For `n` fibers in series, choose multiplicative resistances: `R_series = ∏_i R(q_i)`. If all fibers are activated, `R_series=3^n`, and unit-horizon input action for displacement `d` becomes `9^n*d²`. If all are off, it is `d²`. **This conditional exponential input-energy law is not an algorithmic running-time lower bound**, and is not forced by the general Part II model.

## Relationship to existing formalizations

This extends the existing isolated Lean bridge without changing the source-retained `Elastica` library, importing `Elastica.ExponentialWeight` and reusing `requiredInput`/`requiredAction`. The existing finite Bayesian `LinearInputBayes` and future observational quotient `LinearInputFutureObservation` appear in separately composed `.inc` files and are **not imported or claimed to have been identified with this new fiber kernel**.

## Limitations and next verification

1. Thresholds and resistance law are explicit mathematical choices, not derived from bending energy or measured fluid dynamics.
2. The finite pushforward is a deterministic map on a two-point state space. No full Wasserstein-2 theorem or Fokker–Planck equation is established.
3. The exponential `9^n` follows from the **series product** assumption; alternative network topologies (parallel flow, correlated fibers, fluid feedback) require different laws.
4. A full connection with the original elastica energy would derive the relay threshold and the gain from a specific bistable curvature-energy minimization law, replacing the chosen `switchFiber` rule. The required step is a finite, provable energy comparison and threshold switching condition.
5. The composite repo's `--integration-only` and the isolated Lean `--trust=0`/axiom checks must both pass on the **current PR head**; this note is a description of proposed claims until that CI run succeeds.
