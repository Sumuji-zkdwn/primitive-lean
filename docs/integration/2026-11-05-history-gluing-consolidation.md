# Consolidation: historical nonpreservation and relational gluing (2026-11-05)

This integration carries the exact Lean source files from the verified ancestry #65 → #66 → #67 → #69 → #72 without rewriting the original proofs.

The five supplemental units are `HistoryNonpreservation.inc`, `TemporalLocalExtinction.inc`, `LocalCapacityIncompatibility.inc`, `CooperativeGluingObstruction.inc` and `RelationalOddCycleGluing.inc`. Their five matching Python tests and five verification records are retained. The source hashes in `docs/integration/manifest.json` are brought forward without alteration.

## Preserved distinctions

- Historical preservation is a *falsifiable property*, not an axiom. The countermodels show loss of readout or local-operation domains, and the stated conditional boundaries.
- Pairwise relational feasibility is not the same proposition as matching partial assignments on overlaps; different pairwise witnesses need not glue globally.
- The earlier finite operator machine and Rulefold work from #74 is retained, and its `HigherOrderLiftSelfRewriting.inc` is preserved byte-for-byte.
- Sibling PR #70 and #71 both define `ParallelLocalGluing.inc` with different contents; **neither version is selected in this merge**. They require explicit name/API reconciliation and separate verification.
- Failed or unverified PR #49, #58 and #59 are not included.

## Method and verification

The previous `main` and the independently verified #72 source are combined by copying the 15 new, non-overlapping source/test/note blobs unchanged, merging *additive* registrations into `tools/verify.py` and `tools/verify_main_result.py`, combining file provenance by unique path, and retaining both groups of Python regression tests in CI. Existing verification scopes and hashes are preserved; no original proof is edited.

Each #65/#66/#67/#69/#72 source head had a successful Lean integration/axiom check before consolidation. Those successes do **not** constitute a full build of the new combined tree. The proposed merge commit must run `python -B -X utf8 tools/verify.py --integration-only` at its exact head; CI outcome is recorded separately. All new conclusions retain their explicit finite-state and compatibility hypotheses.
