# Compression pass 1: reachability-preserving source view

This pass is deliberately **not** a Lean theorem-deletion pass. It constructs a
smaller navigation graph for subsequent agents while keeping every original
source, proof, and provenance record intact.

## Saved graph and reduction

Read [graph.json](../dependency/generated/graph.json) and
[source-reachability.json](source-reachability.json) at the same repository revision.
The graph's `main_commit` identifies the input tree for main sources. PR overlays
use the commits in `pr_inputs`. The reduction's `source` records the same
`main_commit` and `pr_snapshot` and the SHA-256 of the exact graph bytes.
Use the reduction's `counts` for the revision being read. Strong pairs count
each source/target pair once across `exact_import` and `qualified_reference`.

| Saved reduction | Source `main_commit` | Nodes | Typed edges | Strong edges | Unique strong pairs → retained | Removed | Weak candidates |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| [#157 merge](https://github.com/Sumuji-zkdwn/primitive-lean/blob/4282766ba6c00bb3ff9f95536d0117056aae9008/docs/compression/source-reachability.json) | `7fe2a0642d10b22a7bbed95c4a028265eda0ee33` | 426 | 1,373 | 427 | 420 → 306 | 114 | 946 |
| [#158 merge](https://github.com/Sumuji-zkdwn/primitive-lean/blob/8ed4c9347609ff350f947da7e44101abcd993ed9/docs/compression/source-reachability.json) | `baf013235612d010f8f17eee34948e401956e174` | 431 | 1,383 | 428 | 421 → 307 | 114 | 955 |

Both merges use PR metadata dated `2026-11-05`.

## Historical audit (PR #152)

- [Saved lexical graph](https://github.com/Sumuji-zkdwn/primitive-lean/blob/fa368ca72011bca59edc52b152798d74cf234cd4/docs/dependency/generated/graph.json) and [saved reduction](https://github.com/Sumuji-zkdwn/primitive-lean/blob/fa368ca72011bca59edc52b152798d74cf234cd4/docs/compression/source-reachability.json) at the original PR head.
- Its recorded `main_commit`: `f6ee8eb8fec6a9441785613f034714c535c47b18`
- Its recorded PR snapshot: `2026-11-05`
- Repository main was separately inspected on 2026-11-17 at
  `1f83367f9680319849a1e0c5288cf7b5a19efb86`.
  **Do not mistake the older lexical graph for an audit of that newer main.**

That historical graph contains 406 source nodes and 1,317 typed source edges.
Only 410 edges of kinds `exact_import` and `qualified_reference` are eligible
(405 unique source/target pairs). Of those pairs, 113 are reachable via other
strong-link paths, leaving **292 pairs** in the reachability-preserving
projection (27.9% fewer strong pairs). All 907
`unique_identifier_candidate` edges are excluded from this projection:
these are uncertain matches, not verified references.

## How to reproduce

```sh
python3 tools/compress_dependency_graph.py --check
python3 -m unittest discover -s tests -p 'test_*dependency_graph.py' -v
```

The tests check the saved projection against the graph. The generator in this
checkout reads the recorded Git inputs and writes the replay to a temporary
directory. It needs the recorded source and PR commits locally. In a single-branch
or shallow clone, fetch any missing pinned objects before running it.
To refresh the projection after updating the graph, run
`python3 tools/compress_dependency_graph.py`.

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
