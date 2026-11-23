# 定理崩壊 — theorem-dependency poset game (prototype)

A mobile-friendly, completely offline, single-file HTML game built from **actual elaborated proof-term references** in primitive-lean. No LLM, external runtime, or synthetic gameplay edges.

## Play

Open [index.html](index.html) in a browser. Choose any surviving theorem; selecting it previews the removal of that theorem and all theorems **transitively dependent on it inside the 18-node induced graph**. Confirm to make the move. The player removing the last theorem wins. Play against an exact-solving CPU or with two local players; hint and undo are available.

The board is formed from 18 `LinearInputVariablePairs.*` theorems in `linear_input/lean_check/VariablePairObservations.inc`. Its 20 arrows are the selected nodes' actual `direct.proof` edges read from `docs/dependency/data/deps.json`, pinned to Git blob `96c797ef04c2387d3645b5e6caca1aac460800a5`. The report's source main commit is `67fdf6b74bbbcb20dc70e7bf98b90471e329aa91`.

This is intentionally an **induced subgraph**, not a claim that other proof dependencies do not exist. An edge proves only an occurrence of a referenced declaration in a particular elaborated proof. Its removal is a *game event*; it does not establish mathematical falsity or an inability to re-prove a theorem.

## Result and reproducibility

```sh
python3 games/dependency-duel/verify.py
```

The read-only regression verifies the actual graph's Git blob hash, 18 selected theorem identities, all 20 selected proof edges, and a fully enumerated win/loss recurrence. The initial board has exactly one winning first move: #08 `gradXu_injective`.

The JavaScript CPU computes `W(S) = exists v in S: not W(S minus upwardClosure(v))`, with `W(empty) = false`, using memoization. Since each move strictly removes at least one node, evaluation always terminates. The game itself is not yet verified in Lean; the mathematical dependency data was extracted from kernel-accepted proof terms.

### Scope

Prototype only, not a full roguelike. No `main` merge, changes to mathematics, or live theorem generation are part of this experiment. Browser smoke tests covered node selection, cascade, exact hint, CPU reply, and undo.
