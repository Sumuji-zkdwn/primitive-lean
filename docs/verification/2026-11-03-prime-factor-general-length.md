# General finite-length prime-factor observation — verification

- Date: 2026-11-03 JST
- Draft PR: https://github.com/Sumuji-zkdwn/primitive-lean/pull/53
- Lean proof source commit: b4d928af47d6f867b0fc708654cc8b5b2fbfd78d
- Successful independent workflow: https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41632958621
- Source: linear_input/lean_check/PrimeFactorFiniteLength.inc
- Job command: lake env lean --trust=0 PrimeFactorFiniteLengthProbe.lean
- Pinned Lean: v4.30.0-rc2; Mathlib comes from the unchanged lake manifest

## State, allowed observations, operation cost
For every n >= 0, Word n = (Fin n -> Fin 3) × Fin 3 encodes n+1 ordered prime factors (2,3,5).
The library Probe n = Option (Fin n) contains product (None) and reading each of the first n positions (Some i).
The final position is not directly readable. The product is a full exact natural number; each query is counted as one oracle call regardless of runtime.

## Verified claims
- prefix_product_pos: products of the first n factors are strictly positive.
- full_library_separates: all n+1 available probes determine the ordered word uniquely.
- bumped_prefix_swap_product: swapping a 2 at an arbitrary prefix position with a final 3 preserves the total product.
- missing_probe_witness: every individual operation is essential, with explicit alternative states not separated by any remaining operation.
- separates_iff_univ: a set of allowed probes separates states iff it equals the complete probe library.
- minimal_distinct_probe_count: n+1 is the minimum number of distinct probes.
- minimal_list_observation_count: a nonadaptive list allowing repeated calls must still have length at least n+1.
- unordered_factor_multiset_count: Fintype.card (Sym (Fin 3) m) = (m+2).choose 2, via Mathlib symmetric powers/stars-and-bars.

## Verification scope
The workflow assembled the five *unchanged* earlier .inc files and only PrimeFactorFiniteLength.inc after import Mathlib.
The new file was screened for sorry/admit/axiom/unsafe/native_decide substrings, then kernel-checked with --trust=0.
All eight targeted #print axioms displayed only propext, Classical.choice, Quot.sound; no sorryAx.
Three nonfatal simp-versus-simpa style warnings occurred. They do not change soundness or successful kernel verification.
This is targeted axiom inspection, not a repository-wide declaration audit.

## Explicit exclusions
The unrestricted factorization complexity, the time for computing any probe, and general integer factorization uniqueness are not proved.
The minimal-list theorem covers preselected, nonadaptive probe calls, not the full general adaptive decision tree.
The count theorem treats unordered multisets via Sym; it does not claim to derive the arbitrary-length sorted normalizer from the PR #52 triple normalizer.
PrimeFactorGeneralF0 in sibling PR #54 separately handles arbitrary length normalization using Mathlib's existing factorization uniqueness.
