# Pilot comparison, log-volume transport and packet localization (2026-11-05)

## Scope

Additive formalization: `linear_input/lean_check/PilotVolumeTransport.inc`, namespace `LinearInputPilotTransport`, registered in the integrated proof/axiom audit of `primitive-lean`.

This supplements `PilotComparisonBridge.inc`, **without modifying that verified source**. It does **not** construct genuine IUT Θ-links, Kummer comparison maps, anabelian log-shells, the arithmetic hull, nor prove Corollary 3.12 / abc.

## Correspondence checked against LANA's public source

1. [Iut/WallEquiv/Forms.lean](https://github.com/lana-agents/iut/blob/main/Iut/WallEquiv/Forms.lean), `ss_iff_exists_ind3`: the identified-copies comparison is equivalent to an allowed (Ind3) region with volume `(s-1)*a`.
2. [Iut/WallEquiv/NonDerivable.lean](https://github.com/lana-agents/iut/blob/main/Iut/WallEquiv/NonDerivable.lean), `Thm311Package.vol_transport` and `xi_iff`: the specified Kummer transport preserves log-volume, and the wall is equivalent to `(s-1)*a <= V` in the abstract package. Its counterexample is *model-relative*.
3. [Iut/WallEquiv/VcI.lean](https://github.com/lana-agents/iut/blob/main/Iut/WallEquiv/VcI.lean), `logVol_hull_vcI_eq` and `ssIneq_iff_packets`: the genuine hull volume has a formula as an average over capsule indices of finite-support sums of weighted local hull terms. This **does not** by itself give a lower bound tied to `a`.
4. [Iut/Arakelov/QPilot.lean](https://github.com/lana-agents/iut/blob/main/Iut/Arakelov/QPilot.lean) represents the genuine `q` degree, but a comparison between those q-arithmetic quantities and the local hull packet volumes remains to be shown.

## Exact abstract results

### Permitted log-volume distortions

Assume a downward-complete volume window `vol(S) <= V` and a labelled transport satisfying `vol(T_g S) = vol(S) + delta(g)`. Then:

```
(exists g S, -(s*a) + vol(T_g S) = -a)
    <-> exists g, (s-1)*a - delta(g) <= V.
```

- `shifted_wall_iff`: exact equivalence.
- `neutral_transport_wall_iff`: if all `delta(g)=0` and at least one transport exists, the choice of labels does not change the wall: it is still `(s-1)*a <= V`.
- `bounded_shift_forces_budget`: if all `delta(g) <= d`, any witness forces `(s-1)*a <= V+d`.
- `bounded_shift_cannot_bridge_gap`: if `V+d < (s-1)*a`, **no number of allowable transport labels** creates a witness.

In the LANA model, Kummer transports have zero shifts. This statement does *not* imply that every possible IUT operation is volume-neutral; the allowance must be checked for each operation in its actual domain and codomain.

### Arithmetic packet requirement

Write `h_i` for abstract real packet volumes at finitely many capsule indices `i`. Then `packet_wall_iff_total_bound` formalizes

```
(s-1)*a <= (sum_i h_i)/N   <->   N*(s-1)*a <= sum_i h_i  (N>0).
```

Theorems `packet_budget_suffices` and `packet_budget_yields_wall` provide an explicit *sufficient certificate*: find real-valued charges `c_i` such that

```
sum_i c_i = N*(s-1)*a,
and for each i, c_i <= h_i.
```

The actual LANA `h_i` are sums of local place/tuple hull terms. No charge allocation is constructed here. In particular, one must relate `q`-valuation / q-degree data to those hull terms, allowing for compensation between local places when necessary.

## Exact first missing arithmetic bridge

The next non-structural obligation can be targeted at:

```
for genuine D:
    N*(s(D)-1)*a(D) <= sum_i (sum_v^fin hullPacket(D,i,v)).
```

This is the actual `ssIneq_iff_packets` criterion, not a new theorem. New work must establish a **genuine arithmetic inequality or a different allowed comparison mechanism**, rather than postulating it. Equating a freely chosen fake region with the q-pilot would be circular.

## Verification boundary

The additive source is registered for compilation with the original pinned Lean/mathlib, `--trust=0`, and full declaration-axiom audit. CI needs to succeed at the *new* exact commit after this addition; the prior successful CI run only verifies the previous PR #78 head.
