# primitive-lean × LMLExplore: Gibbs/softmax bridge experiment

**Status: experimental; NOT yet kernel-verified or merged.** This is an
independent Lake workspace. The canonical primitive-lean
`lean/lean-toolchain`, `lean/lakefile.toml`, source hashes and main proof
assembly are intentionally unchanged.

## Why this bridge?

- `lean/Elastica/ExponentialWeight.lean` defines
  `Elastica.exponentialWeight β ε θ ℓ := exp (-β * energy ε θ ℓ)`.
- LMLExplore's
  `LMLExplore/OnlineLearning/ExponentialWeights.lean` defines
  `softmax v a := exp (v a) / ∑ b, exp (v b)`, and proves the
  resulting vector lies in the probability simplex and is positive.
- This experiment imports both actual source modules and states their
  equality for a **finite** family of candidate curves. It reuses two
  LMLExplore results instead of reimplementing normalization proofs.

There is a real version barrier: primitive-lean is verified against Lean
`v4.30.0-rc2` and mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`;
LMLExplore uses Lean `v4.36.0-rc2` and mathlib
`2ddf59c8f14245864e6c0ed227a2dab76b9efea2`. This experiment
tests whether the unchanged Elastica source can compile at LMLExplore's pin.

## Reproduce

From `experiments/lmlexplore_bridge`:

```bash
lake update
lake exe cache get
lake build ElasticaLMLExploreBridge
lake env lean --trust=0 ElasticaLMLExploreBridge.lean
```

The project directly pins the dependency revisions recorded in
LMLExplore's `lake-manifest.json` at
`8280ba89e727bf08859d21c084dd44bca7968e1f`.
It imports `Elastica` from `../../lean`, avoiding duplication and
protecting original SHA-256 evidence.

## Success criterion

All imports compile, the three bridge theorems typecheck with `--trust=0`,
no `sorry` or added axiom is introduced, and the existing
primitive-lean/main verification is untouched. Until a successful CI run
on the exact branch head, **do not claim a verified cross-library merge**.

If the old Elastica code does not elaborate with Lean 4.36/mathlib, preserve
the failure log and port the *smallest required dependency fragment* on
this experimental branch. Do not update the pinned original project or
copy 4,830 theorems into LMLExplore.

## Sources

- primitive-lean: https://github.com/Sumuji-zkdwn/primitive-lean
- LMLExplore: https://github.com/LeanMachineLearning/LMLExplore
- LMLExplore source is Apache 2.0; no LMLExplore code is copied here.
