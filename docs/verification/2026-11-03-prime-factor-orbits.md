# Prime-factor observation orbits: S2/S3 finite probe verification

- Date: 2026-11-03 (JST)
- Draft PR: https://github.com/Sumuji-zkdwn/primitive-lean/pull/51
- Parent: https://github.com/Sumuji-zkdwn/primitive-lean/pull/50
- Lean proof commit: `35dcf2cb2bf30c18f6aaaaea27924823b87c89af`
- Independent workflow (success): https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41626860906
- New source: `linear_input/lean_check/PrimeFactorOrbits.inc`
- Lean toolchain: `leanprover/lean4:v4.30.0-rc2` (pinned in `lean/lean-toolchain`)
- Compile command: `lake env lean --trust=0 PrimeFactorOrbitsProbe.lean`

## Assumptions and observations

All factor values are encoded by `primeOf : Fin 3 → ℕ` in the verified PR #50, with values 2, 3 and 5. We study exactly two or exactly three ordered factors; these are *finite* state spaces.

- Two factors: 9 ordered states; 6 unordered canonical states. Their product kernel equals equality up to the transposition of the factors (the two S2 permutations).
- Three factors: 27 ordered states; 10 unordered canonical states. The product kernel equals equality up to the six explicitly enumerated permutations of the three positions, and equals multiset equality.
- Ten distinct triple-product outputs: 8, 12, 18, 20, 27, 30, 45, 50, 75 and 125.

## Restricted observation libraries

**Ordered pairs** (the verified parent PR #50): allowed probes are product and first factor. Every selection with fewer than two calls fails to separate states; two different probes suffice.

**Ordered triples** (this PR): allowed probes are product, first factor and second factor. Every *fixed* list of fewer than three allowed calls fails to separate all states; calling all three is injective.

**Unordered triples**: the only allowed probe in that library is the product. One call is sufficient, and an empty list is not.

All results refer to lists of observations chosen independently of outputs. We do not claim any lower bound for adaptive choices of the next probe.

## Observation-kernel link

`pair_joint_refines_swap_orbit` and `triple_joint_kernel` reuse the exact joint observation kernel theorem `LinearInputFiniteObservation.joint_eq_iff` from PR #36. The new file does not change previous theorem sources.

## Verification and boundaries

The standalone workflow concatenates `import Mathlib`, unmodified `TernaryZeroCesaro.inc`, `FiniteObservationSeparation.inc`, `PrimeFactorObservation.inc`, and only the new `PrimeFactorOrbits.inc`. The new file is checked for the forbidden substrings `sorry`, `admit`, `axiom`, `unsafe`, and `native_decide`. Compilation under `--trust=0` succeeded.

The six targeted `#print axioms` outputs listed only `propext`, `Classical.choice`, and `Quot.sound`. This is not a repository-wide automated axiom audit.

`Fin 6` enumerates all six rearrangements; no abstract S3 group object, homomorphism, or action laws are formalized here. The Burnside formula `(27 + 3 * 9 + 2 * 3) / 6 = 10` is a separate mathematical cross-check, not yet a Lean theorem in this PR.

No theorem about general integer factorization, primality testing cost, computational runtime, any unrestricted observation library, or arbitrary-length prime sequences is claimed.
