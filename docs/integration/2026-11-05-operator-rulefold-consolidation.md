# Consolidation gate: operator self-extension and Rulefold (2026-11-05)

This note records a proposed **one-branch integration** of a checked stack. It is not a claim that independent or failing branches have been merged.

## Exact ancestry and scope

- Previously integrated into `main`: PR #3 (historical proof integration baseline, merge commit `3078aef262b544ab498377f940b92a84008b292c`) and PR #68 (independent orbit-trace modules, squash commit `9e49c308bb2cdcbabb1c77c2517c7e8986dbd6b5`).
- This integration branch consists of the stacked work **#55 → #56 → #57 → #60 → #61 → #62 → #63 → #64 → #73 → #74**. The direct parent of #74 is the verified source of #73 at `49bcf3612f5d166a916e8f16b73577fd0fbcdf73`.
- The change from #73 to the original #74 head `b5dee9b7af6d840672a428b848fbb11e16c7b594` adds seven files: the isolated Rulefold demo workflow, two browser demos, their tests, and demo documentation. It does not edit inherited Lean proof sources.
- Parent proof snippets stay in `linear_input/lean_check/`; `tools/verify.py --integration-only` remains the consolidated verifier. This does **not** migrate them into the Elastica library or overwrite their provenance.

## Proof layers (different mathematical claims)

1. **Observation and semantic operations (#55–#57).** Distinguish generated operator words, observation equivalence, bisimulation, finite-horizon distinguishability and compatible but non-word-generated operators.
2. **Conditional operator creation (#60–#62).** Old-reachable viability obstruction; finite local repair construction; bounded re-entry. All synthesis claims are relative to explicit candidates, finite rules and viability assumptions.
3. **State-dependent generation (#63–#64).** Learned descriptors can update object-level edges and meta-rule tables. The second-order lift in #64 remains a supplied external function.
4. **State-resident higher-order rules (#73).** The mutable lift table is part of finite machine state and is evaluated by a fixed interpreter; the Fin 4 controlled trace exposes a difference from frozen rules.
5. **Interactive realization (#74).** The JavaScript Fin 4 reference trace is tied to the integrated continuous three-phase black/white mandala maker. The creative LAB controller and field rendering are demonstrations, not Lean-certified mathematical or physical predictions.

No part proves unbounded autonomous discovery, unrestricted self-programming, perfect observation, or general physical dynamics.

## Verification and exclusions

- #73 exact-head workflow [41851704883](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41851704883) passed pinned Lean/mathlib `--trust=0`, supplement source audit, axiom audit, and finite Python tests at `49bcf3612f5d166a916e8f16b73577fd0fbcdf73`.
- #74 original-head standalone Node/Rulefold tests passed in [41857065203](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41857065203) at `b5dee9b7af6d840672a428b848fbb11e16c7b594`. The **new consolidated head requires its own exact-head integration run** before claiming whole-tree verification.
- **Explicitly excluded:** #58 and #59 (failing integration checks at their heads); #49 (failing integration check); #65–#72 (parallel historical/relational-gluing branch from #64); and other independent #31–#54 branches. Their source additions are not silently implied by this merge.
- Keep the fifth definition's historical preservation **falsifiable**: #65–#72 are about failure and boundaries, and must not be folded into a universal preservation axiom.

## Reproduction

```sh
python -B -X utf8 tools/verify.py --integration-only
node --test demos/higher_order_playground.test.cjs demos/rulefold_mandala.test.cjs
```

On merge, separately inspect the merge commit and any main-branch verification jobs. CI success for the proposed head alone is not retroactive proof for unrelated branches or for a future changed base.