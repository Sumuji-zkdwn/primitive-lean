# Semantic operator monoid and exact finite counts — 2026-11-04

The previous operator-language extensions distinguish two states if an
operator word produces different readout traces. The new theory builds
**all** raw operators that preserve this complete observational
equivalence, quotients them by their effective action, and maps that
quotient algebra to endomorphisms of minimal predictive states.

## Formally proposed

`OperatorSemanticMonoid.inc` establishes:
- Identity, composition, constants and all old words are compatible
- Compatible raw operations compose associatively
- Quotient actions preserve identity and composition
- Observational equivalence is a two-sided congruence
- Modulo observational equivalence, the effective operators embed
  faithfully into self-maps of minimal predictive states
- **Every** endomorphism of the predictive quotient is realizable by
  selecting a representative original state for each quotient state
- Therefore evaluation from effective operators to quotient-state
  endomorphisms is bijective (the full transformation monoid)

This is an *existence result* relying on choice and total functions.
It is not an efficient synthesis algorithm.

`OperatorFiniteMapCounts.inc` contains executable finite cardinality
certificates, including the 3-state partition `(2,1)`.

## Finite counting result

For `r` equivalence classes of positive sizes `m₁,...,mᵣ`, the
number of compatible **raw state transformers** is:

```
C_raw = product_i sum_j (m_j ** m_i)
```

The number of effective, distinguishable maps on the quotient is

```
C_effective = r ** r
```

The second statement follows from the surjectivity theorem, assuming
finite quotient state and the ordinary counting of finite functions.
The full general numerical formula is **not** claimed as a Lean-proven
counting theorem in this PR: `tools/count_operator_compatibility.py`
provides an exact enumeration/formula cross-check for finite partitions.
The special 3-state `C_raw=15` is a separate Lean theorem candidate.

## Sample counts

| Fiber sizes | Original states | Compatible raw maps | Quotient maps |
|---|---:|---:|---:|
| (2,1) | 3 | 15 | 4 |
| (2,2) | 4 | 64 | 4 |
| (3,1) | 4 | 112 | 4 |
| (2,1,1) | 4 | 96 | 27 |
| (2,2,1) | 5 | 405 | 27 |

## Verification

```sh
python -m pytest -q tests/test_operator_counting.py
python -B -X utf8 tools/verify.py --integration-only
```

A proof success claim is allowed only after a successful pinned Lean
`--trust=0` run, source hash audit and complete axiom audit at the
**exact** PR head. Parent PRs must also be verified or reconciled.
