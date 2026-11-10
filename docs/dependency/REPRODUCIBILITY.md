# Dependency graph provenance and reproduction

The historical [graph.json at merge commit 389bcf5](https://github.com/Sumuji-zkdwn/primitive-lean/blob/389bcf585e206fdf4241f73e75dc3f40a27ad43e/docs/dependency/generated/graph.json) says its `main_commit` is `f348ec7541551ec84ca537ade7feac206313e6da`. An independent Git-tree audit found **65 `main:` source nodes absent from that commit** (31 `.lean` and 34 `.inc`). That artifact remains as historical evidence, but its recorded SHA does **not** reproduce its contents. No `.lake` nodes were found in that artifact.

The generator now reads **all baseline source blobs, assembly registries and PR snapshot JSON** at a single immutable `--main-ref` Git commit. It records the resolved full `main_commit` and each PR overlay's fixed base/head/merge-base SHAs (`pr_inputs`), using the head SHA of the target PR stored in the snapshot for stacked branches. A missing pinned PR Git object fails generation rather than silently changing the graph. To omit PR overlays explicitly, pass `--skip-prs`.

To regenerate from a checked-out repository containing the referenced Git objects:

```bash
python3 tools/generate_dependency_graph.py --main-ref <full-commit-sha>
python3 -m unittest discover -s tests -p test_dependency_graph.py -v
```

The CI workflow deliberately pins the latest commit touching input sources or the generator, **not the graph-output-only bot commit**, so it cannot repeatedly change the recorded SHA when committing its own output. Source inclusion is defined by the committed tree, restricted to `lean/**/*.lean` and direct `linear_input/lean_check/*.{lean,inc}` files, excluding generated `All.lean`, `MainResult.lean`, and any `.lake` directory.

This is a lexical source-reference graph, not a Lean kernel proof-dependency closure. The PR metadata is the dated snapshot in `docs/dependency/pr_snapshot.json`, not a live PR inventory.
