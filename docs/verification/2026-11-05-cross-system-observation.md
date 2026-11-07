# Cross-system observational connection: a modularity test case (2026-11-05)

## Two deliberately separate layers

1. **General Lean structure.** `linear_input/lean_check/CrossSystemObservation.inc` adds a relation between two independently presented deterministic labelled systems. It depends on the existing `LinearInputOperatorWords` vocabulary, `WordEq`, `State`, `encode`, `readout`, and `transition`. It is inserted after `OperatorSemanticClosure.inc` in the unchanged additive verifier path. No new axiom is declared.
2. **Finite arithmetic check.** `tools/elliptic_modular_probe.py` independently calculates integer Fourier coefficients of `eta(tau)^2 eta(11*tau)^2` and point counts of `E: y^2+y=x^3-x^2-10x-20` modulo good primes. `tests/test_elliptic_modular_probe.py` checks the two lists and the standard Hecke coefficient relations over a **finite** range.

The layers are *not linked by a purported modularity theorem*; the arithmetic experiment supplies a test scenario for future, mathematically typed connections.

## Structural theorem statements

Let `A`, `B` be arbitrary state spaces, `I` one common action alphabet, `K: A→O`, `L: B→O` readouts and `sA`, `sB` action families.

- `CrossTrace` matches the output after **every finite operator word**.
- `CrossBisim` is a cross-state relation matching readout now and preserved by any matched action.
- `greatest_cross_bisim` proves the full-trace relation is the greatest cross-bisimulation.
- `ExactBridge K L sA sB φ` requires both `L(φ(x))=K(x)` and `φ(sA(i,x))=sB(i,φ(x))`; it does *not* assume an invertible state map.
- `bridge_trace`, `bridge_preserves_wordEq` and `predictiveMap` transport the bridge to the existing predictive quotient.
- `predictiveMap_output` and `predictiveMap_step` make the induced output and operator laws explicit.
- `separating_word_refutes_trace` converts any explicit mismatching operator word to a formal contradiction of `CrossTrace`.
- `bridge_reflects_wordEq` shows that an exact bridge also **reflects** every finite trace equality. Hence `predictiveMap_injective` needs no extra hypothesis. `predictiveMap_surjective` requires a surjective `φ`; `predictiveMap_bijective_of_surjective` then proves quotient bijectivity. The older conditional helper lemmas remain for explicit dependencies. No unqualified isomorphism of original state spaces is asserted.
- `no_bridge_if_fiber_splits` shows that if `φ(x)=φ(y)` but `φ(sA(i,x))≠φ(sA(i,y))`, **no** transition `sB` can make the square commute. `flip_bridge` is a valid many-to-one forgetting example and `flip_predictive_bijective` shows its predictive quotients are nevertheless bijective; `reveal_has_no_bridge` proves an impossible forgetting for Bool pairs.

These statements establish a precise boundary between observably sound forgetting and loss of successor consistency; this is the intended connection to the F0 and operator-language series.

## Exact arithmetic probe

For the classical conductor-11 example, write

```
E  : y² + y = x³ − x² − 10x − 20
f  : q × ∏(1−qⁿ)²(1−q¹¹ⁿ)²
a_p(E) = p+1−#E(F_p),  p≠11.
```

The Python script obtains `#E(F_p)` by enumerating `y²+y` residues and `x` values including the unique point at infinity, and builds the truncated eta product using only exact integers. Its default checks are all **24** primes `2 ≤ p ≤ 97` excluding the bad prime `11`, along with `a_(p^(r+1))=a_p*a_(p^r)−p*a_(p^(r−1))` for every good prime power in range and `a_(mn)=a_m a_n` when `gcd(m,n)=1` for `mn ≤ 200`. A changed curve constant is a negative control.

Sample computed rows:

| p | #E(F_p) | a_p(E) | a_p(f) |
|---|---:|---:|---:|
| 2 | 5 | -2 | -2 |
| 3 | 5 | -1 | -1 |
| 7 | 10 | -2 | -2 |
| 13 | 10 | 4 | 4 |
| 47 | 40 | 8 | 8 |

**Important limitations:** finite equality is not a proof of modularity, an isomorphism of elliptic curves and modular forms, a Hecke-eigensystem uniqueness theorem, or a reduction of the full Shimura–Taniyama theorem. The Hecke relations are only *checked* in the finite range, not formalized in Lean. The Lean bridge is about deterministic words, whereas arithmetic Frobenius/Hecke operators require careful specification of their types and compositions.

## Re-run and evidence

```bash
python -m pytest -q tests/test_elliptic_modular_probe.py
python tools/elliptic_modular_probe.py
python -B -X utf8 tools/verify.py --integration-only
```

The local Python smoke test passed **5/5** tests on the authoring session. The full Lean compilation and joint axiom audit must be evaluated from the PR's pinned commit GitHub Actions result; the local environment did not have `lean`/`lake`. Do not count these Lean theorems as verified until that result is confirmed.
