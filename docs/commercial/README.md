# Primitive Lean: an agent-readable, commit-pinned source catalog

**Status:** working export prototype, not a paid service or a kernel verification certificate.

`primitive-lean` contains Lean 4 research modules, finite experiment scripts, and verification records. AI agents and researchers need a way to *locate* a declaration and identify the exact source snapshot before spending tokens or running a build. The exporter creates a source-level JSONL inventory from **one immutable Git commit**. It does not claim that every indexed declaration has an independently verified theorem or a marketable novelty claim.

## What works

From a Git checkout of this repository:

```sh
python3 tools/export_agent_catalog.py --out-dir /tmp/primitive-lean-catalog
python3 tools/export_agent_catalog.py --out-dir /tmp/primitive-lean-catalog --check
python3 -m unittest discover -s tests -p 'test_export_agent_catalog.py' -v
```

For a reproducible historical export, add `--ref <full-commit-SHA>` to **both** export and check calls. The resulting files are:

* `declarations.jsonl`: one row per lexically recognized named Lean declaration, containing its source path, line, declared name, kind, header preview, content SHA-256, and commit.
* `manifest.json`: the commit, counts, source-file count, SHA-256 of the JSONL bytes, and an explicit evidence boundary.

The program reads committed blobs using `git show`, not the working directory. Thus editing a file without committing it does **not** silently alter a pinned export. It uses only Python's standard library and Git. Outputs are sorted and deterministic for the same commit.

A consumer can use `path` and `line` to inspect the actual source, compare `file_sha256`, and determine which build/axiom audit (if any) covers that commit. The header is a *lexical preview*, not an elaborated Lean type: namespaces, section variables, macros, tactics, and local declarations require real Lean elaboration for interpretation. Some Lean syntax lies outside this simple scanner. `verification_status` is therefore always `not_assessed`, regardless of previously published whole-project CI runs.

## What cannot yet be sold as a verified dataset

The older [`docs/index/lean-declaration-index.json`](../index/lean-declaration-index.json) records 1,594 declarations and a verification run for a **different, historical tree**. Its `verified_source_commit` must not be mistaken for the current `main` or merged with this catalog without proof of compatibility. Other source-level dependency graphs are lexical snapshots rather than kernel dependency graphs. No proof-of-correctness, automatic theorem deduplication, or declaration-specific `--trust=0` claim is supplied by this exporter.

Before offering any *paid verified release*, produce a separately pinned CI result for the chosen commit, an axiom audit, license/third-party-source review, a reproducible artifact, and a buyer-facing statement of exactly what was checked. A public GitHub repository does not by itself grant a blanket commercial redistribution license. The dedicated Apache-2.0 license for the Möbius contribution should not be mistaken for repository-wide licensing.

## Proposed deliverable and buyer use case

**Evidence pack for proof-assistant/agent developers:** a machine-consumable declaration index, immutable source hashes, and (in a later independently verified release) a matching CI/axiom ledger for selecting, retrieving, and rechecking Lean material. A prospective buyer can evaluate the free exporter on this repository before any commercial discussion. The distinctive claim to test is *traceable evidence and stable agent consumption*, not the number of theorems, novelty of all statements, or a promise that AI will automatically get smarter.

**Commercial status:** pricing, distribution rights, demand, a checkout route, and automated fulfillment are **not established**. No orders or revenue are claimed. This document is a concrete working prototype and a boundary for further independent validation, not a live store.
