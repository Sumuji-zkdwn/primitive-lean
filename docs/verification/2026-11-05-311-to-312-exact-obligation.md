# IUT III Theorem 3.11 → Corollary 3.12: exact remaining implication

Checked against the publicly accessible [LANA Lean repository](https://github.com/lana-agents/iut) on 2026-11-05. This note is a *scope correction and proof-obligation audit*, not a proposed proof of the IUT gap. It supersedes any suggestion that general F0/descent/hull lemmas themselves resolve Step (xi).

## Source-level theorem ledger

| Already established in LANA's model | Exact source | What it means |
| --- | --- | --- |
| `EtaAlg.etaAnab_eq_etaQ_iff` | `Iut/Wall/EtaAlg.lean` | Equality of pointed line maps reduces to equality of output volume with the native q-pilot volume. |
| `variant_of_wall` | `Iut/Wall/EtaAlg.lean` | The wall **if assumed** implies the Corollary 3.12 variant. This is bookkeeping, not construction of the missing wall. |
| `variant_of_wallOn` | `Iut/Wall/MultiContainer.lean` | A wall on a nonempty directed relation implies the variant **provided transported outputs are realized inside the target theta-image hull**. |
| `variant_of_wallOn_of_volCompat` | `Iut/Wall/MultiContainer.lean` | Under Kummer volume compatibility, the same implication is available using source-side realization. |
| `wallOn_iff_of_thetaShift` and `wallOn_iff_ss_of_volCompat` | `Iut/Wall/MultiContainer.lean` | **If** one assumes the identified-copies volume law `ThetaShift` and Kummer volume compatibility, even a directed wall is equivalent to the strong Scholze–Stix inequality. Merely selecting a directed arrow does not bypass this. |
| `EtaAlg.sheq_iff_wall` | `Iut/Wall/Constraints.lean` | A proposed «SHE» condition stating that some output is q-pilot-like **is the missing wall itself**. It may not be used as an independent premise to claim the gap solved. |
| `Thm311Package.xi_iff` and `not_forall_xi` | `Iut/WallEquiv/NonDerivable.lean` | In a model abstracting the formalized Theorem 3.11, Step (xi) is equivalent to `(s−1)a≤V` and fails for some valid packages. Not a counterexample to genuine IUT initial data. |
| `gap_eq` | `Iut/WallEquiv/Gap.lean` | The target hull bound exceeds the identified-copies output hull by a nonnegative bad-prime Ind2 term. **An upper bound on possible outputs is not an accessible output witness.** |

## Exact directed proof objective

Fix a **genuine** initial Theta datum `D`, distinct Hodge theaters `h₁,h₂`, and a *directed* theta link `h₁ → h₂`. Let `A` be the actual multiradial / anabelian eta algorithm constructed from the genuine group-theoretic data and with the correct Ind1/Ind2/Ind3 indeterminacies.

The only desired new witness is a permitted choice `ι` of input representation and `S` in the *actual* Ind3 domain such that:

```
vol_target(transport(h₁,h₂, A.out(ι,S))) = vol_target(qRegion(h₂)).
```

Additionally show that this transported output is in the theta-pilot hull **of the target column** (or prove Kummer volume compatibility and the source-side containment needed by LANA's corresponding theorem). On a fixed directed link the source statements are sufficient to apply `variant_of_wallOn` or `variant_of_wallOn_of_volCompat`.

In LANA terms, `WallOn L` quantifies over every pair in relation `L`. Its theorem `variant_of_wallOn` needs only one such pair and the admissible target containment; to minimize the *original* task one may formulate a dedicated one-link witness rather than an unnecessarily universal wall. The point remains to produce a **valid algorithmic witness**, not a free numeric or set-theoretic selection.

## Why the extra Ind2 hull volume is not yet the witness

Write:

```
Q = -a = log-vol(q-pilot)
B = log-vol(LGP·hull(VC(I))) = -s*a + V
R = log-vol(hull(theta-pilot))
Delta = R - B >= 0.
```

LANA's `Gap.lean` computes the **ambient** hull increase `Delta`. But the existing comparison algorithms with the identified-copies law have outputs bounded by `B`, not automatically by the *attainable* upper endpoint `R`.

The required extra step is to show that **the genuine eta output can actually occupy enough of the Ind2-enlarged hull** to match `Q`, or directly prove a weaker target inequality without the eta comparison. A proof that the ambient hull is large is insufficient unless the algorithmic output is tied to that enlargement.

For models satisfying `ThetaShift` and `VolCompat`, the strong obstacle reappears:

```
WallOn(directed theta links)  <->  (s−1)*a <= V
```

provided the directed link relation is nonempty and the model satisfies the cited LANA hypotheses. If `(s−1)a>V`, such an algorithm cannot provide the directed witness in that model, even if `Delta>0`. Therefore any genuinely different route must use an **additional proven property** of the real IUT algorithm not captured by this identified-copies law (or directly prove the arithmetic inequality).

One may not posit `SHEq`, `Wall`, `XiPrinciple`, the requisite log-volume equality, or the desired inequality as an axiom, then call the conclusion proved.

## Explicit falsification checks

1. **Trivial algorithm bypass:** `exists_wall_iff` in `Iut/Wall/Checks.lean` says that *some* algorithm with the wall exists iff the Corollary 3.12 variant already holds. Inventing the algorithm is circular.
2. **Artificial distortion bypass:** `Iut/Wall/MultiConstraints.lean` constructs `chainModel` with `exists_wallOn_chain` by shifting volumes, but `not_volCompat_chain` and `not_she3_chain` demonstrate failure of the critical compatibility constraints. An arbitrary directed wall does not establish the genuine claim.
3. **Unjustified local-to-global bridge:** the existing `primitive-lean` theorems `descends_iff_respects`, `reachable_iff_fiber_covered`, and `orbit_hull_eq_iff_each_image_stable` give conditional tests. They supply no `EtaAlg.out` from genuine arithmetic data.

## Next proof attempt (single target, no extra side projects)

Find an explicit construction from the *genuine* Theorem 3.11 output of a directed eta algorithm satisfying:
(i) correct Ind1–Ind3 domains, (ii) target-column hull realization, (iii) the native q-pilot volume match. If the output obeys `ThetaShift` and volume-neutral Kummer transports, this cannot be obtained without proving the strong `SSIneq`; so isolate **exactly which additional genuine construction changes the achievable output range** before claiming an alternative route.

### Status

**OPEN.** LANA's formalized conditions do not derive the comparison. This document does not prove the open arithmetic or group-theoretic bridge. The earlier Lean-verified four `primitive-lean` supplements are relevant conditional lemmas and counterexamples only.
