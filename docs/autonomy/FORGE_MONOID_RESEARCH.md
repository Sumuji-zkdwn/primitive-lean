# Forge: from permutations to transformations

Read-only experiment on the pinned six-generation evolution ledger and four
semantic receipts. No production workflow, main branch, or persistent ledger
is changed. The snapshot fixtures are copies, not new production receipts.

## Reproduction

From the repository root:

```sh
python -B -m tools.autonomy.forge_lean_monoid \
  --state tests/fixtures/forge_monoid_evolution6.json \
  --semantic tests/fixtures/forge_monoid_semantic4.json \
  --output verification/forge-monoid
```

Add `--kernel` with the pinned Lean environment available to check the
historical seed and receipt proofs and the new rank-separation certificate.
The finite report is written even if a subsequent kernel check fails.

## Mathematical result

The 256-state permutation group after generation five is the alternating
group. The independent replay found a 65,280-element ordered-pair orbit,
and a fixed 60-letter word raised to power 71,060 is the single 3-cycle
(69 183 104). The word's action and orbit are rechecked, not asserted.
By Jordan's theorem the two-transitive group contains A_256; all generators
are even, so equality holds. Generation six adds an odd permutation, hence
the group is S_256. These group conclusions invoke the classical theorem
and are not represented as Lean-certified group-order theorems.

All original nonbijective generators have image sizes 4, 16, 64 or 175.
Composition cannot increase image size relative to either factor. Thus
every old word is injective or has image size at most 175.

A new typed construction, restrict_at(parent, a), acts as parent at a and
as identity elsewhere. If parent(a) differs from a, its rank is exactly
255 and it is idempotent. The deterministic candidate uses reverse at 1:
1 maps to 64, everything else is fixed. Its SHA-256 is
f9fdd6687e635000fdec6a4f4aba333918956dd8c7ed7751669d3c2425ed86f8.

The proposed Lean proof explicitly provides image covers for the singular
letters, left inverses for permutation letters, and 176 distinct candidate
outputs. It proves candidate_not_word and candidate_not_macros for arbitrary
word length. Kernel verification is required before any production adoption.

Together S_256 and any rank-255 map generate the full transformation monoid
T_256: permutation conjugates of the single-point collapse give every
elementary collapse a -> b. To realize any function, collapse each fiber
onto a representative, then use a permutation to send the representatives
to their distinct target values. Thus all 256^256 = 2^2048 endomaps exist
in the generated monoid. This is a symbolic universality statement, not an
enumeration or claim of efficient synthesis.

## Next frontier

Do not increase the receipt limit merely to search for new endomaps of the
same set. A subsequent reviewed migration must admit rank-extension
certificates without breaking byte-identical replay of the original six
receipts. After admission, new expressivity requires a larger or typed
state space, e.g. X x X, variable-length states, or maps between spaces.
A minimal follow-up is to separate products of independent single-register
maps from a coupling operation on two registers, without enumerating
65,536^65,536 functions. No migration or state write is performed here.
