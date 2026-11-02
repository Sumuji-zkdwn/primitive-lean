# Exact bridges between independently retained representations

`RepresentationBridges.inc` records seven theorem statements connecting
the actual definitions of separate PRs. Register namespace
`LinearInputRepresentationBridges` after `F16FullMatrix.inc`,
`F16ConstructiveRecovery.inc`, `EWFSFenchel.inc`, and `EnergyWfsFenchel.inc`.

The two F16 implementations use identical coefficients from the original
signed multiplication table. The following are exact equalities, stronger
than agreement of their determinants, ranks, or sampled values:

| Definitions being identified | Theorem |
|---|---|
| PR #16 `leftMatrix t` and PR #20 `realPencilAll t` | `leftMatrix_eq_realPencilAll` |
| PR #16 `leftMatrixInt t` and PR #18 `intPencil t` | `leftMatrixInt_eq_intPencil` |
| Their row coordinate maps | `rowOrder_eq_rowCoord` |
| Their column coordinate maps | `colOrder_eq_colCoord` |

The theorem `reconstruct_leftMatrix_observations` then reuses PR #25's
actual constructive decoder for paired PR #16 observations. Neither a new
decoder nor an assumed equivalence of matrices is introduced.

Two other exact identifications connect PR #12's `orientedGradient` and
`orientedInverse` to PR #13's `H` and `HInv`. This preserves both original
modules while recording that their chosen reversible polynomial maps are
the same. It does not identify all remaining Fenchel or WFS constructions,
which still have their own pairing and domain assumptions.

Six statements have proof term `rfl`, exposing definitional identity. The
reconstruction theorem directly invokes `reconstruct_observations`. The
final integrated `--trust=0` compile and full axiom audit are the execution
record for these seven additions; source inspection alone is not recorded
as a completed Lean run.

The F16 block decompositions use independent row and column permutations.
They are matrix equivalences and are not asserted to be conjugacies; in
particular this bridge makes no new eigenvalue or dynamical claim.
