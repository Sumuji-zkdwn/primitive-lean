# Operator algebra scale-up — 2026-11-04

## Goal

Grow `primitive-lean` as a verified, compositional **operator calculus**
with explicit state observations, finite-word programs, quotient semantics,
adaptive feedback, product systems, reachability, and F0 forgetting.

This is a stacked extension of PR #55–#57. Source-level declarations remain
candidates until exact-head pinned Lean verification and axiom audits pass.
No counted theorem is a new physical law or an automated invention claim.

## New modules

- `OperatorContextualEquivalence.inc`: program equivalence is a
  two-sided congruence; replacing any subword preserves the **whole
  predictive quotient**. Concrete equality implies observational equality.
  Injective sensors make them coincide.
- `OperatorAdaptivePolicies.inc`: a state-dependent policy that factors
  through the current predictive quotient cannot refine its observation
  classes. Unsafe feedback can reveal a distinction invisible to every
  fixed old word; a Fin 3 construction witnesses that strict gap.
- `OperatorProductSystems.inc`: two independent systems have a product
  observational kernel equal to the product of their individual kernels,
  even for arbitrary mixed-order action sequences. Cross-coordinate
  actions commute exactly.
- `OperatorReachability.inc`: invariant predicates correspond exactly
  to predicates closed under reachability; generated old-word operators
  do not expand the reachable state relation, while adding genuinely
  new primitives may.
- `OperatorSensorFamilies.inc`: arbitrary indexed sensor bundles
  intersect observational kernels; reindexing and output processing
  cannot improve distinctions. Independent coordinate readouts can be
  jointly injective while separately non-injective.
- `OperatorF0SemanticBridge.inc`: under a fiber-respecting old
  vocabulary and an idempotent F0 observation map, semantic operator
  compatibility equals F0 descent. This identifies two existing
  concepts by their **definitions**, without an analogy-only proof.

## Explicit limitations

- Deterministic total state updates; action and sensor alphabets may be infinite
- No claim of computational decidability for infinite systems
- Finite regression tests complement but do not replace the Lean kernel
- Existing source hashes of the prior successful branches are preserved
- New PRs remain draft; no merge into main
- Success means a pinned `lake env lean --trust=0` proof check,
  all-declaration axiom audit, hash audit and tests at an exact commit

## Reproduction

```sh
python -m pytest -q tests/test_operator_algebra_scale.py
python -B -X utf8 tools/verify.py --integration-only
```
