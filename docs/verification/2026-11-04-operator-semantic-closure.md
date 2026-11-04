# Semantic closure of generated operators — 2026-11-04

## Research motivation

An old operator vocabulary determines a complete observational kernel,
meaning two states are equivalent if every old finite operator word
returns the same observation.

The new Lean source
`linear_input/lean_check/OperatorSemanticClosure.inc`
separates two concepts that should **not** be confused:

- **Syntactic generation:** a newly named operator is equal to a finite
  composition of existing primitive operators.
- **Semantic compatibility:** the operator preserves the old
  observational-equivalence relation, and so descends to a unique map
  on the old predictive quotient.

The latter includes the former, but can be strictly more general.

## Central formal statements

With `Compatible K step T` meaning
`∀ x y, WordEq K step x y → WordEq K step (T x) (T y)`:

```
Compatible K step T ↔
  ∃ F : State K step → State K step,
    ∀ x, F (encode K step x) = encode K step (T x)
```

The quotient map `F` is uniquely determined, compatible operators
contain the identity and all old operator words, and are closed under
composition. The induced map preserves identities and composition,
so this is a homomorphic passage to quotient endomorphisms.

Surjectivity of `T` implies surjectivity of its induced map.
If `T` reflects old observational equivalence, its induced map is
injective. Preservation of the current readout passes to the quotient.

## Separating syntax from semantics

Take a 3-state system with identity as its only old primitive and a
readout that maps 0,1 to 0 and 2 to 1. The new constant-to-2
transformer is *conservative*:

```
WordEq K (sumStep old constantTwo) x y ↔ WordEq K old x y
```

But the constant transformer acts nontrivially on the old quotient,
while every old finite word acts as the identity. Consequently no
old-language word can represent it even on predictive quotient states.

This shows that *semantic compatibility* is strictly weaker than
*word definability*. No algorithm for automatically discovering a
novel compatible primitive is claimed.

## Verification

This adds 17 theorem candidates and three definitions, plus independent
3-state finite regression tests.

```sh
python -m pytest -q tests/test_operator_semantic_closure.py
python -B -X utf8 tools/verify.py --integration-only
```

All Lean proof and no-unexpected-axioms claims depend on a successful,
commit-pinned CI run. The base branch PR #56 is separately validated.
