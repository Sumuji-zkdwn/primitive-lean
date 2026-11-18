# Compression pass 1: reachability-preserving source view

This pass is deliberately **not** a Lean theorem-deletion pass. It constructs a
smaller navigation graph for subsequent agents while keeping every original
source, proof, and provenance record intact.

## Audited input

- Exact saved lexical graph: `docs/dependency/generated/graph.json`
- Its recorded `main_commit`: `f6ee8eb8fec6a9441785613f034714c535c47b18`
- Its recorded PR snapshot: `2026-11-05`
- Repository main was separately inspected on 2026-11-17 at
  `1f83367f9680319849a1e0c5288cf7b5a19efb86`.
  **Do not mistake the older lexical graph for an audit of that newer main.**

The saved graph contains 406 source nodes and 1,317 typed source edges.
Only 410 edges of kinds `exact_import` and `qualified_reference` are eligible
(405 unique source/target pairs). Of those pairs, 113 are reachable via other
strong-link paths, leaving **292 pairs** in the reachability-preserving
projection (27.9% fewer strong pairs). All 907
`unique_identifier_candidate` edges are excluded from this projection:
these are uncertain matches, not verified references.

## How to reproduce

```sh
python3 tools/compress_dependency_graph.py
python3 tools/compress_dependency_graph.py --check
python3 -m unittest discover -s tests -p 'test_compress_dependency_graph.py' -v
```

The output is `docs/compression/source-reachability.json`. It stores the
identifiers, reduced edge pairs, source graph content SHA-256, and counts.
The tool fails if strong links are cyclic, self-referential, refer to unknown
nodes, or if reduction changes any source-to-source reachability.

**Meaning boundary:** `A -> B` means that source A lexically references or
imports B. A retained multistep path does **not** mean that a removed direct
import, symbol reference, theorem premise, or proof obligation is dispensable.
The full typed and symbol-labeled original graph remains authoritative.
Do not edit Lean imports/proofs mechanically from this projection.

## Next mathematically meaningful compression pass

1. Identify candidate theorem pairs with equal or mutually implying statements
   **under explicitly compared assumptions**. Name and surface these as
   candidates, never automatically delete them on a textual similarity score.
2. Prove the bridge in Lean with `--trust=0`, record the exact proof SHA and
   which declaration remains canonical.
3. Replace selected clients, independently compile them, audit axioms and
   dependency changes, and only then propose deleting redundant wrappers.
4. Keep original historical proofs and dated source snapshots available through
   Git history. Do not automatically merge research PRs.

This view supplies a smaller dependency map; no theorem-count reduction or
kernel-certified semantic deduplication is claimed in pass 1.
