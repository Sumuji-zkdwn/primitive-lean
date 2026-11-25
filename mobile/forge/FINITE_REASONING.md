# Finite reasoning kernel

This change adds exact bounded finite-state reasoning independently of the language adapter. It does not add a pretrained language model or alter production Lean certificates. The functions compute the coarsest stable observation refinement, a shortest distinguishing operation word (pair-graph BFS), and a bounded shortest composition word realizing a requested table. Failure at a search bound is explicitly inconclusive.

On the existing Android dialogue branch, enter **演算子の偶奇観測商** to examine all current transition tables on the 256 actual states. The result is a local finite check, not a new Lean proof. This turn is not used as a factual training target.

Run `python mobile/forge/test_mobile.py` in the normal snapshot-prepared host environment. The new independent tests compare 252 seeded machines and 5,040 ordered state pairs against a separate reachable-pair oracle, and verify shortest distinguishing words and bounded synthesis. Without a snapshot, run `PYTHONPATH=mobile/forge/app/src/main/python python mobile/forge/test_finite_reason.py`.

The APK v0.5 dialogue/retrieval and rational-polynomial layer are distributed separately; this PR deliberately contains only the shared finite kernel and a small integration into the original branch. No private corpus or conversation records are added. Android installation and CI have not yet been verified for this branch.
