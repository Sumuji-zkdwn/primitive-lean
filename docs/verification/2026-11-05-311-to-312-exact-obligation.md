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


## First missing *typed* construction: raw multiradial orbit → eta output

The actual public LANA code search finds `MRRep.possibleRegion` only in `Iut/Multiradial/Spec.lean` and planning notes (not as an input to `EtaAlg.out`). The sources define objects at two different stages:

```text
Iut/Multiradial/Spec.lean:
  RawOutput  →  MRRep R P  →  MRRep.possibleRegion reg r : Set X

Iut/Wall/EtaAlg.lean:
  EtaAlg.out ι S : Region D
  EtaAlg.etaAnab ι S : B.val.C →ₗ[ℝ] ℝ

Iut/HodgeTheater/Wall.lean:
  theaterAlg.out _ S := lgp D S.1
  theaterKummer _ := 1
```

Thus no inspected construction maps the **genuine algorithmic orbit with its Ind1/Ind2 provenance** to the actual `EtaAlg.out` for a non-identified pair of Hodge theaters, with a verified log-volume readout. `theaterAlg` uses an identified-copies output by definition; it cannot be evidence that the needed nontrivial reconstruction has happened.

In addition, `Iut/Multiradial/Spec.lean` proves `sUnion_ind3Possible`: the union of *all* Ind3 subregions of a fixed region is just that region. Ind3 can select and adjust **inside** an allowed image; it cannot introduce a missing new image into the orbit. The separate `Iut/Wall/Ind3.lean` grants arbitrarily smaller log-volumes inside `hull(VC(I))`, but that is a **container-domain statement** and is not an identification of these regions with an actual q-pilot-producing algorithmic output.

The next meaningful proof target is therefore not another abstract closure theorem. It is a genuine map/functionality from the actual `MRRep` orbit (with its admissible choices and transport) into the output side of the eta algorithm, **together with** a proof that its chosen output has the native q-pilot value or yields the original numerical inequality. Naturality / quotient well-definedness alone will not imply the missing arithmetic equality.

A source-based implementation check must reject any purported proof that:
- defines `out` to return the q-pilot by fiat;
- assumes `SHEq` (which is definitionally equivalent to `Wall` in the interface);
- uses the full available *ambient* theta hull as if it were already an actual possible `EtaAlg.out`;
- assumes `SSIneq`, `XiPrinciple`, `Wall`, or `Corollary312Variant` as an input.

This narrows the 3.11→3.12 goal to a single **provenance-preserving arithmetic output comparison**, with its actual source types now identified.


## Direct proof attempt: instantiate retained gluing and volume lemmas (2026-11-05)

**Attempted chain.** Apply `LinearInputParallelGluing.operational_gluing_iff` (PR #70) to the actual output of IUT III Theorem 3.11, and then apply the already verified `LinearInputPilotComparison.scaled_pilot_witness_iff` (PR #78) to identify its native q-pilot readout.

At the concrete instantiation point, the gluing theorem requires all local reports and the global observation to use a **common coordinate type** `I → V`, plus an actual finite operator word whose observed state equals the canonical glue. The existing primitive-lean result *does not construct* a common value-group/log-shell coordinate from Hodge theaters with different arithmetic holomorphic structures, nor an IUT-correct run of the multiradial η-algorithm. Calling the existential `operational_gluing_iff` is not a proof of that existential.

Under the **currently available identified-copies** output law (from LANA `EtaAlg.ThetaShift`) and volume-neutral Kummer transports, the exact remaining equation becomes

```
logVol(out(ι,S)) = -s*a + logVol(S) = -a
  ↔ logVol(S) = (s-1)*a.

Allowed Ind3 volumes fill (-∞, V].
Hence ∃ (allowed S), correct logVol(out(ι,S))
  ↔ (s-1)*a ≤ V.
```

This equivalence is established in the existing LANA `xi_iff_ss`, `wallOn_iff_ss_of_volCompat` and the already verified primitive-lean `scaled_pilot_witness_iff`. **None of those lemmas proves the inequality on genuine initial Θ-data.**

**Countercheck.** LANA's formalized `Thm311Package.counterexample` (and the analogous primitive-lean `ell7_small_container_obstruction`) uses `ell=7`, `s=14/3`, `a=1`, `V=1`. Every allowed `S` has `logVol(S)≤1`, hence

```
logVol(out(ι,S)) ≤ -14/3+1 = -11/3 < -1 = logVol(q-pilot).
```

All the formalized package premises are compatible with this failure. **It is a counterexample to derivability in that model, not to genuine IUT or abc.** Therefore adding existing generic gluing/fiber lemmas cannot close the implication *within that abstraction*.

**Only possible ways forward:** prove the needed arithmetic lower bound for the genuine log-shell hull; or construct and verify a genuinely different, holomorphic-structure-sensitive multiradial output law/transport that does not reduce to identified copies. The IUT-specific construction must be provided explicitly. In particular, LANA's `EtaAlg.etUnitOnly` (T2) forces `not_valDependent`, while its intended (SHE) comparison may require the q-side value/holomorphic structure; a proof must resolve that tension rather than assuming the desired identification.

**Outcome of this attempt:** no new proof of Step (xi). The explicit failed application point is the absent **genuine IUT output witness**, not missing general-purpose Lean infrastructure. PR remains draft.
