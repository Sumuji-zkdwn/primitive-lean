# Mono-eye v0.1 ↔ finite operator-word observation ↔ Elastica: composition audit

Date: 2026-11-08 (JST). Proposed baseline: `primitive-lean` main `67fdf6b74bbbcb20dc70e7bf98b90471e329aa91`.

## Separate claims

1. **ME-3 (open composition).** An open eye is a state space together with specified boundary inputs, deterministic updates, and a public readout. Joining two eyes while keeping their full states and wiring is always a valid open system. That alone does **not** imply that forgetting state before joining preserves its dynamics.
2. **T7–T9 (predictive quotient).** For `K : S → O`, `step : I → S → S`, the observational kernel is `WordEq K step x y`, equality of the outputs after every finite operation word (including the empty word). The existing `OperatorWordObservations.inc` constructs its canonical quotient and sound descended transitions.
3. **New open-product result.** If the two boundary alphabets `I_A`, `I_B` are nonempty, and a joined eye accepts *every* input pair in `I_A × I_B`, with coordinatewise deterministic updates, then

   `WordEq (K_A × K_B) (step_A × step_B) (a,b) (a',b')`
   `↔ WordEq K_A step_A a a' ∧ WordEq K_B step_B b b'`.

   Consequently the product of the component quotient encoders has exactly the global kernel and is surjective onto the product of the component quotient state spaces. In ordinary set-theoretic terms this gives a canonical bijection between the quotient of the joined state space and the product of local predictive quotients. This is the precise limited commuting square; it does **not** prove arbitrary feedback quotient commutation.
4. **New wired-feedback soundness result.** Assume every incoming boundary value is a function of the neighboring **public readout**, not a hidden internal state. Assume each local `WordEq` quantifies over all possible incoming boundary values and external operations. Then local equivalence of both components implies global equivalence under the wired update, because the two locally equivalent states expose the same boundary values at every step. The reverse implication need not hold.

## Smallest explicit boundary-obstruction witness

Let the left state be `a ∈ {0,1,2}`, with output `K_A(a)=[a=2]`; the right state be `b∈{false,true}` with output `K_B(b)=b`. The left update under incoming boundary bit `c` is `f(c,a)=2` if `c=true,a=1`, otherwise `f(c,a)=a`. The right update is always `false`. Join using the actual neighboring outputs as the boundary inputs.

- The global states `(0,false)` and `(1,false)` are fixed under the joined update, and both always read `(false,false)`.
- The local left states `0` and `1` are **not** `WordEq` under all possible boundary inputs: supply `true` for one step and their readouts become `false` and `true`.
- Thus the global predictive quotient identifies a pair that the product of *unrestricted-boundary* local quotients separates. Global quotienting **after feedback wiring** is strictly coarser in this example.

The independent Python audit enumerates all 4,096 pairs of two-state boundary-controlled models (4 observation maps for each eye; 16 two-input transitions for each eye). It uses iterative greatest-bisimulation refinement, not just fixed sample horizons. In every model, independent-input product equivalence matches the local product relation exactly, and the local product relation is contained in the wired one. The three-by-two-state counterexample is tested separately.

## Translation to existing Elastica expressions (not yet a geometric instantiation)

Use a smooth oriented curve segment `θ : ℝ → ℝ` on `[a,b]` as the **full local state**. Its external boundary data include endpoint tangent angles and the endpoint displacements

`Δx = ∫_a^b cos(θ(s)) ds`, `Δy = ∫_a^b sin(θ(s)) ds`.

For a full curve, `Elastica.xCoord` and `Elastica.yCoord` reconstruct positions and `Elastica.energy` integrates its curvature density. The existing `Elastica.Composition` theorems prove the splitting identities for these integrals and give an equality of end data for **already smooth** curves under explicitly equal exterior angles and equal middle displacement integrals. They do not construct a C¹ gluing of arbitrary pieces.

To instantiate the Mono-eye product or wired theorem on actual Elastica pieces, it remains necessary to supply: (i) a well-defined state type of admissible pieces, (ii) readout maps (possibly boundary angle/displacement/energy), (iii) boundary-input-dependent rewriting operators preserving admissibility and boundary compatibility, (iv) the exact correspondence between old and newly composite operation alphabets, and (v) an explicit proof that all boundary values used in the local predictive kernel are accessible (or a controlled restriction to reachable values). None of those obligations follows from ME-3 alone. Therefore this PR proves a **finite/state-level observational bridge** and a sharp obstruction, not arbitrary geometric gluing, physical self-similarity, or minimal real curvature energy.

## Verification and provenance boundaries

- The new additive Lean source `linear_input/lean_check/MonoEyeComposition.inc` reuses `LinearInputOperatorWords.run`, `WordEq`, `word_step`, `word_now`, `encode_eq_iff` and `State`. Prior proof sources are unchanged.
- The registered combined Lean verifier must pass `lake env lean --trust=0` and a public-axiom audit on the exact PR head before the new source can be labelled kernel-verified.
- The independent finite audit is `python -B tests/test_mono_eye_composition.py` (also part of PR integration CI).
- The standalone audit cannot replace Lean compilation. Source existence and success of a previous, different commit's CI are not verification of this head.

## Source anchors

- `mono_eye_axioms_v0_1.md`, fixed 2026-10-09: ME-1–3, T7–T9 (Library source; copy not incorporated into this repository).
- [`OperatorWordObservations.inc`](https://github.com/Sumuji-zkdwn/primitive-lean/blob/67fdf6b74bbbcb20dc70e7bf98b90471e329aa91/linear_input/lean_check/OperatorWordObservations.inc)
- [`Elastica/Composition.lean`](https://github.com/Sumuji-zkdwn/primitive-lean/blob/67fdf6b74bbbcb20dc70e7bf98b90471e329aa91/lean/Elastica/Composition.lean)
