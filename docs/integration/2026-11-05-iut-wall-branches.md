# Two non-equivalent proof targets in the IUT pilot comparison (2026-11-05)

## Sources compared

- [LANA interim report](https://github.com/katobungen/LANA_report_202607): §9.2 equation (9-1), `η^q = η^anab_S`; §10 interpretation of Theorem 3.11 to Corollary 3.12.
- [LANA Lean EtaAlg](https://github.com/lana-agents/iut/blob/main/Iut/Wall/EtaAlg.lean): output class equality `etaAnab_eq_etaQ_iff`, conditional `variant_of_wall`.
- [LANA Lean NonDerivable](https://github.com/lana-agents/iut/blob/main/Iut/WallEquiv/NonDerivable.lean): `Thm311Package.xi_iff` and **model-relative** `not_forall_xi`.
- [LANA Lean VcI](https://github.com/lana-agents/iut/blob/main/Iut/WallEquiv/VcI.lean): `ssIneq_iff_packets` for genuine arithmetic container local term formula.
- [LANA Lean Gap](https://github.com/lana-agents/iut/blob/main/Iut/WallEquiv/Gap.lean): `gap_nonneg`, `ss_iff_le_rhs_sub_gap`, `variant_and_not_ss_iff`, and `gap_eq`.

## Strong route A: identified-copies wall

Let `a(D)=absLogQ(D)`, `s(D)=sFactor(nC D)` and `V(D)=logVol(hull(VC(I)))`.

Under the **specific identified-copies output volume law** `-s*a+vol(S)` and the downward-complete admissible set of `S`, the comparison is equivalent to

```
(s(D)-1)*a(D) <= V(D).
```

By `ssIneq_iff_packets` this is an actual weighted-local-packet sum lower bound. The existing proof does **not** obtain it for genuine `D`; it identifies what arithmetic coupling would have to be proved.

The `primitive-lean` abstract bridge `PilotVolumeTransport.shifted_wall_iff` shows how admissible volume shifts modify the numerical requirement. For transports known to preserve volume the shift is exactly zero. It is not valid to infer numerical slack from additional *neutral* transport choices.

## Weaker route B: Corollary 3.12 numerical variant

Write `R(D)=rhsData.rhs` and `Δ(D)=R(D)-logVol(LGP·hull(VC(I)))`. LANA proves `Δ>=0` and

```
Var(D) <-> -a(D) <= R(D)
SS(D)  <-> -a(D) <= R(D)-Δ(D).
```

The interval `0<=R+a<Δ` is an actual formal possibility for `Var` without `SS`. `gap_eq` locates `Δ` in nonnegative bad-prime **Ind2 hull-of-union** terms, while shell/archimedean defects cancel after using hulls on both sides.

The new `PilotHullInflation.inc` confirms, in a **separate finite rectangle model**, that volume preservation of individual images cannot justify volume preservation of the hull of a union. It does *not* prove that genuine IUT Ind2 terms are positive, zero, bounded, or sufficient to establish the desired comparison.

The unsolved step for route B is not merely the existence of a region of volume `-a` inside the bigger hull. That existence follows numerically once `Var` is assumed and can be circular. The step is to **construct the output from the genuine eta-algorithm**, carry its specified Ind1–Ind3 constraints, and show that it represents the source q-pilot in the required target.

## What the three new primitive-lean modules do and do not do

| Source | Exact contribution | Not proved |
| --- | --- | --- |
| `PilotComparisonBridge.inc` | Choice output coverage vs deterministic factorization; F0-descent counterexample; numerical window iff | Genuine q-pilot reconstruction |
| `PilotVolumeTransport.inc` | Exact shifted comparison criterion, neutral-shift obstruction, conditional packet charge bound | Arithmetic relation between q-degree and hull packets |
| `PilotHullInflation.inc` | Concrete finite hull volume can grow under an individually volume-preserving symmetry | Actual Ind2-hull growth or Corollary 3.12 |

These are original abstract theorems, not copies or imports of the LANA proof stack.

## Verification protocol

The source files are separately registered with hashes, preserve all baseline proofs, and are subject to `tools/verify.py --integration-only`, pinned Lean/mathlib `--trust=0`, complete axiom auditing and finite Python regressions. Previous confirmed CI for PR #78 is [41899320499](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41899320499), and for the two-module stage [41900981481](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41900981481). Exact-head verification of all three modules must be checked separately.
