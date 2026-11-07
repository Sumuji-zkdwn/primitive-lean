# Choice-dependent pilot comparison bridge (2026-11-05)

## Aim and scope

This is an **abstract proof-obligation mapper**, not a proof of IUT III Corollary 3.12, not an independent proof of abc, and not an implementation of the anabelian/Kummer theta algorithm. No arithmetic conclusion is assumed.

Source: `linear_input/lean_check/PilotComparisonBridge.inc`.
It is registered as namespace `LinearInputPilotComparison` in the existing integrated Lean proof and axiom audit.

## Statements added

1. `reachable_iff_fiber_covered`: for a forgotten observation `forget : A -> B`, direct target `target : A -> V`, and choice-dependent output `out : B -> S -> V`, reconstruction for every original state is equivalent to inclusion of the original target values of each forgotten fiber in the range of all admissible outputs at that fiber. There is **no uniqueness assumption** on the choice.
2. `factorization_iff_fiber_invariant`: for inhabited `V`, single-valued factorization `target = q ∘ forget` holds iff the target is constant on each forgotten fiber. This is deliberately *stronger* than choice-dependent reconstruction.
3. `reachable_of_factor_and_witness`: even after target factorization, one must separately construct an admissible output choice for every quotient observation.
4. `reachable_choice_independent_implies_fiber_invariant`: if all choices at a given observed state give the same output, successful reconstruction requires fiber invariance; without choice-independence this implication fails.
5. `log_wall_iff_bound`: when the output log-volume is `offset(b) + volume(b,s)`, and the available volumes at `b` fill precisely the downward interval ending at `cap(b)`, successful comparison is equivalent to
   `target(x) - offset(forget(x)) <= cap(forget(x))`. The interval-filling hypothesis is an explicit input, not inferred from arbitrary data.
6. `scaled_pilot_witness_iff`: if offset is `-scale*a` and target is `-a`, the comparison witness is equivalent to `(scale - 1)*a <= cap` in this abstract numerical model.
7. `ell7_small_container_obstruction` and `ell7_larger_container_witness`: the same `scale=14/3, a=1` gives failure for cap 1 and success for cap 4 in a concrete downward-complete volume model.
8. `choice_range_can_cover_nonconstant_fiber` / `choice_range_not_single_valued`: two distinct direct values can both be represented via different choices even after they are merged by forgetting.
9. `f0_descent_does_not_force_wall`: the existing theorem `LinearInputF0Descent.identity_descends` supplies an F0-compatible update, but cannot force the arithmetic comparison in the concrete countermodel.

## Relation to the published IUT gap

LANA's July 2026 report isolates the desired equation `eta^q = eta^anab_S` for an admissible choice `S`. The independent [Iut/Wall/EtaAlg.lean](https://github.com/lana-agents/iut/blob/main/Iut/Wall/EtaAlg.lean) models this as a choice-dependent comparison of pointed lines and concrete log-volumes. Its [NonDerivable.lean](https://github.com/lana-agents/iut/blob/main/Iut/WallEquiv/NonDerivable.lean) gives a **model-relative** non-derivability result and the same shape `(s - 1)*a <= V`; that does not refute the genuine arithmetic statement.

Our bridge explains precisely which extra work is needed:

* Construct the **actual** admissible output choices from IUT data and map the resulting log-volume to this interface, without identifying unrelated holomorphic structures.
* Establish the relevant allowed volume range, and prove the **arithmetic** lower-bound relation for the genuine initial theta data or obtain the comparison by another method.
* Verify that the selected witnesses are induced by the genuine algorithm rather than freely selected to force the target value.

The present file **does not provide** these witnesses or bounds. The numerical equivalence itself cannot produce a missing inequality.

**Important distinction (Gap.lean):** The displayed numerical wall corresponds to the stronger *identified-copies* comparison. It is sufficient, but need not be necessary for the weaker Corollary 3.12 numerical variant: LANA proves the latter can hold in the abstract window between the strong wall and the enlarged indeterminacy hull. The volume of individual transports and the volume of the hull of their union are different constructions. See `2026-11-05-pilot-transport-localization.md` for the two proof obligations.

## Verification criteria

The new source is additive and leaves the baseline proofs unchanged. A success claim requires the exact-head `python -B -X utf8 tools/verify.py --integration-only` CI run, including `lake env lean --trust=0`, complete public declaration axiom auditing, source provenance and finite regressions. Independent Python tests are supporting checks, not Lean proofs.
