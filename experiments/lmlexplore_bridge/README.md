# primitive-lean × LMLExplore: first cross-library theorem

**Status: experimental until the exact-head CI passes.** This is a separate
Lean 4.36 Lake workspace. The canonical primitive-lean Lean 4.30 source,
toolchain, proof assembly and SHA-256 evidence stay untouched.

## Direct reuse of both projects

- Imports **the actual `Elastica.energy` definition** from
  `lean/Elastica/Variation.lean`, a curvature-energy interval integral.
- Imports `LMLExplore.OnlineLearning.softmax` and its existing probability
  simplex and positivity theorems from the LMLExplore Git dependency.
- Defines `curveGibbs` for a finite family of candidate curves, proves the
  normalized exp(-β energy) formula by definitional equality, and derives
  its membership in `LMLExplore.simplex` and strictly positive entries.
- No mathematical statements or definitions from either imported library
  are reimplemented. In particular, these bridge proofs are about the
  imported source, not a copied example that only has similar notation.

## Scope reduction after CI failures

Importing `Elastica.ExponentialWeight` also brings the full Elastica
variation, constrained-variation, and derivative proof stack. The unmodified
Lean 4.30 source encountered multiple Lean 4.36 elaboration differences. The
first attempt to port that whole proof stack was **not successful**, and the
failures remain visible in the earlier PR #138 CI runs.

The first cross-library theorem now imports only `Elastica.Variation`.
That file contains the original `Elastica.energy` definition, and passed the
first experimental Lean 4.36 build with one minimal proof-tactic adaptation.
The generator `prepare_compat.py` verifies the original file's Git blob SHA
before producing an isolated `compat/Elastica/Variation.lean` copy.
Only the proof tactic in a dominated-differentiation lemma is altered; no
statement, definition or mathematical hypothesis changes.

The earlier `Elastica.exponentialWeight` identifier is **not** imported by
the reduced bridge. Its defining expression is `exp (-β * energy ...)`,
but importing the full original module remains a separate porting task.
This scoped result cannot be claimed as an all-theorems merge.

## Reproduce

```bash
cd experiments/lmlexplore_bridge
lake update
python3 prepare_compat.py
lake exe cache get
lake build ElasticaLMLExploreBridge
lake env lean --trust=0 ElasticaLMLExploreBridge.lean
```

Versions: Lean 4.36.0-rc2 and Mathlib
`2ddf59c8f14245864e6c0ed227a2dab76b9efea2`, with LMLExplore at
`8280ba89e727bf08859d21c084dd44bca7968e1f`. The original project
is separately pinned to Lean 4.30.0-rc2 and Mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

**Success criterion:** the current exact-head CI builds both true source
modules and checks all three bridge theorems with `--trust=0`. A green CI
would certify this *small bridge only*. It would not certify a wholesale merge
of 4,830 + 4,019 theorems.

LMLExplore: https://github.com/LeanMachineLearning/LMLExplore (Apache 2.0).
primitive-lean: https://github.com/Sumuji-zkdwn/primitive-lean
