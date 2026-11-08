# Arbitrary finite-length sorting F0 — verification record

- Date: 2026-11-03 JST
- Draft PR: https://github.com/Sumuji-zkdwn/primitive-lean/pull/54
- Verified Lean proof commit: 331cae85c9ab5019fb0acbcda5779e3a44db8226
- Successful pinned independent Actions run: https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41633253537
- New source: linear_input/lean_check/PrimeFactorGeneralF0.inc
- New workflow: .github/workflows/prime-factor-general-f0-probe.yml
- Command: lake env lean --trust=0 PrimeFactorGeneralF0Probe.lean

## Domain
The normalizer sorts arbitrary finite lists of natural numbers. List length and the unordered multiset of list elements are preserved.
The observations are exact list product and arbitrary functions of the original list.

## Verified statements
- normalize_idempotent: sorting twice equals sorting once.
- normalize_eq_iff_perm: two lists normalize to the same list iff they are permutations.
- normalize_preserves_product: sorting does not change multiplication.
- factors_through_normalize_iff: f can be computed from the normalized list iff f is invariant under permutations.
- prime_product_eq_iff_perm: for lists whose elements are all prime, equal products iff the lists are permutations.
- prime_product_kernel_eq_normalize_kernel: for prime lists, equality of products coincides with equality of normal forms.
- prime_product_invariant_of_normalize: any observation constant on prime-product fibers is unchanged by normalizing prime lists.

## Required provenance
General prime product equality-to-permutation uses Mathlib's established theorem Nat.primeFactorsList_unique.
This is not a new proof of the fundamental theorem of arithmetic.
Without the AllPrime hypotheses, products can be equal for lists that are not permutations.

## Trust
The standalone workflow assembles import Mathlib, unchanged prior PR #36/#50/#51/#52 sources, and only the new PrimeFactorGeneralF0.inc.
The new file is screened for forbidden source substrings and compiled with lake env lean --trust=0.
All seven targeted #print axioms show only propext and Quot.sound, or propext, Classical.choice, Quot.sound; no sorryAx.
This does not assert an automated full-repository axiom audit.

## Strict scope
No time complexity bounds for sorting, primality testing, or factorization.
No connection claim that this equals a separately existing F0 operator.
PR #53 independently proves the min count in a restricted nonadaptive observation library; this proof does not imply an unrestricted complexity lower bound.
