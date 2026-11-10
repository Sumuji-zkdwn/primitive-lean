#!/usr/bin/env python3
"""Source-evidence dependency graph; distinguishes imports, references, and PR bases.
This is a lexical scan, not the Lean elaborator's exact proof-dependency graph.
"""
from __future__ import annotations
import argparse
import ast
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
REPO = "Sumuji-zkdwn/primitive-lean"
DECL = re.compile(r"(?m)^[ \t]*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
QUAL = re.compile(r"\b((?:Elastica|LinearInput[A-Za-z0-9_']+|OrbitTrace[A-Za-z0-9_']*)\.[A-Za-z_][A-Za-z0-9_']+(?:\.[A-Za-z_][A-Za-z0-9_']+)*)\b")
BARE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']{9,}\b")


def git(*args):
    try:
        return subprocess.check_output(["git", "-C", str(ROOT), *args],
                 text=True, stderr=subprocess.DEVNULL).rstrip("\n")
    except (OSError, subprocess.CalledProcessError):
        return None


def git_bytes(*args):
    """Read immutable Git data as exact bytes (including trailing newlines)."""
    try:
        return subprocess.check_output(
            ["git", "-C", str(ROOT), *args], stderr=subprocess.PIPE
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise RuntimeError("Unable to read pinned Git object: git " + " ".join(args)) from exc


def resolved_commit(ref):
    return git_bytes("rev-parse", "--verify", ref + "^{commit}").decode("ascii").strip()


def committed_text(commit, path):
    return git_bytes("show", commit + ":" + path).decode("utf8")


def is_source_path(path):
    if ".lake" in path.split("/") or Path(path).name in ("All.lean", "MainResult.lean"):
        return False
    if path.startswith("lean/") and path.endswith(".lean"):
        return True
    prefix = "linear_input/lean_check/"
    return (path.startswith(prefix) and "/" not in path[len(prefix):]
            and path.endswith((".lean", ".inc")))


def tracked_source_paths(commit):
    raw = git_bytes("ls-tree", "-r", "-z", "--name-only", commit)
    return sorted(p for p in raw.decode("utf8").split("\0") if is_source_path(p))


def strip(src):
    out = []
    i = depth = 0
    line = string = escaped = False
    while i < len(src):
        c, pair = src[i], src[i:i + 2]
        if line:
            if c == "\n": line = False
            out.append("\n" if c == "\n" else " ")
        elif depth:
            if pair == "/-": depth += 1; out.extend("  "); i += 2; continue
            if pair == "-/": depth -= 1; out.extend("  "); i += 2; continue
            out.append("\n" if c == "\n" else " ")
        elif string:
            if c == '"' and not escaped: string = False
            escaped = (c == "\\" and not escaped)
            out.append("\n" if c == "\n" else " ")
        elif pair == "--":
            line = True; out.extend("  "); i += 2; continue
        elif pair == "/-":
            depth = 1; out.extend("  "); i += 2; continue
        elif c == '"':
            string = True; escaped = False; out.append(" ")
        else:
            out.append(c)
        i += 1
    return "".join(out)


def assignment(filename, key, source_commit):
    root = ast.parse(committed_text(source_commit, filename))
    for node in root.body:
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == key for t in node.targets):
            return ast.literal_eval(node.value)
    raise ValueError("No " + key + " in " + filename)


def category(path, baseline, supplements):
    stem = Path(path).stem
    if path.startswith("lean/Elastica/") or path == "lean/Elastica.lean": return "Elastica"
    if path.startswith("lean/OrbitTrace"): return "OrbitTrace"
    if path in baseline: return "LinearInput foundation"
    for prefix, label in (
        (r"^(F0|Future|ObservationRetraction|Branch|StrangeOperator|RepresentationBridges)", "F0 / Observation"),
        (r"^(Operator|FiniteSelf|RecursiveOperator|RuleSelf|MetaRule|HigherOrder|SemanticInterval)", "Operator / Rulefold"),
        (r"^(Galois|Kummer|VariablePairGalois|Chebyshev|PrimeFactor|Radical)", "Arithmetic / Galois"),
        (r"^(F16|Complementary|Shear)", "F16 / Recovery"),
        (r"^(WFS|EWFS|EnergyWfs|Temporal)", "WFS / Fenchel"),
        (r"^(FiniteBayes|FourBayes|Hanna)", "Bayes / Jets"),
        (r"^Pilot", "IUT comparison / Pilot"),
        (r"^(Parallel|Relational|LocalCapacity|HistoryNon|Cooperative)", "Local / Global gluing"),
    ):
        if re.match(prefix, stem): return label
    return "Other supplements" if path in supplements else "Other"


def source_node(path, text, scope, baseline, supplements):
    code = strip(text)
    namespaces = re.findall(r"(?m)^namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)", code)
    return {
        "id": scope + ":" + path, "scope": scope, "path": path,
        "group": category(path, baseline, supplements),
        "namespace": namespaces[0] if namespaces else "",
        "declarations": [m.group(1) for m in DECL.finditer(code)],
        "imports": re.findall(r"(?m)^import\s+([A-Za-z0-9_'.]+)", code),
        "sha256": hashlib.sha256(text.encode("utf8")).hexdigest(),
        "_code": code,
    }


def sources(baseline, supplements, source_commit):
    # Worktree files never contribute to a graph labeled with a different SHA.
    return [source_node(path, committed_text(source_commit, path),
                        "main", baseline, supplements)
            for path in tracked_source_paths(source_commit)]


def branch_sources(snap, baseline, supplements, source_commit):
    overlay, inputs = [], []
    interesting = {31, 65, 66, 67, 69, 70, 71, 72, 75, 77, 78}
    pinned_branches = {p["head_branch"]: p.get("head_sha") for p in snap["prs"]}
    for pr in snap["prs"]:
        n, head, base = pr["number"], pr.get("head_sha"), pr.get("base_branch")
        if n not in interesting:
            continue
        base_sha = source_commit if base == "main" else pinned_branches.get(base)
        if not head or not base_sha:
            raise ValueError(f"PR #{n}: no immutable head/base in PR snapshot")
        for role, sha in (("base", base_sha), ("head", head)):
            if git("cat-file", "-e", sha + "^{commit}") is None:
                raise RuntimeError(f"PR #{n}: pinned {role} commit {sha} unavailable; "
                                   "fetch its Git object or use --skip-prs")
        merge_base = git("merge-base", base_sha, head)
        paths = git("diff", "--name-only", base_sha + "..." + head)
        if merge_base is None or paths is None:
            raise RuntimeError(f"PR #{n}: cannot compare pinned base and head")
        inputs.append({"number": n, "base_branch": base, "base_sha": base_sha,
                       "head_sha": head, "merge_base_sha": merge_base})
        for path in paths.splitlines():
            if not is_source_path(path):
                continue
            if git("cat-file", "-e", head + ":" + path) is not None:
                overlay.append(source_node(path, committed_text(head, path),
                                           "pr" + str(n), baseline, supplements))
    return overlay, inputs


def source_edges(nodes):
    full, bare = defaultdict(set), defaultdict(set)
    imports = {}
    by_id = {n["id"]: n for n in nodes}
    for n in nodes:
        for decl in n["declarations"]:
            qname = n["namespace"] + "." + decl if n["namespace"] else decl
            full[qname].add(n["id"])
            bare[decl].add(n["id"])
        p = n["path"]
        if n["scope"] == "main" and p.startswith("lean/") and p.endswith(".lean"):
            imports[p[5:-5].replace("/", ".")] = n["id"]
    found = defaultdict(set)
    def add(frm, to, kind, word):
        if frm != to and to in by_id: found[frm, to, kind].add(word)
    for n in nodes:
        frm, code = n["id"], n["_code"]
        for imp in n["imports"]:
            if imp in imports: add(frm, imports[imp], "exact_import", imp)
        for name in set(QUAL.findall(code)):
            refs = full.get(name, set())
            same = {x for x in refs if by_id[x]["scope"] == n["scope"]}
            for dest in same or {x for x in refs if by_id[x]["scope"] == "main"}:
                add(frm, dest, "qualified_reference", name)
        for name in set(BARE.findall(code)):
            mains = {x for x in bare.get(name, set()) if by_id[x]["scope"] == "main"}
            if len(mains) == 1: add(frm, next(iter(mains)), "unique_identifier_candidate", name)
    return [
        {"from": a, "to": b, "kind": k, "symbols": sorted(words)}
        for (a, b, k), words in sorted(found.items())
    ]


def group_mermaid(nodes, edges):
    sizes = Counter(n["group"] for n in nodes)
    label_ids = {g: "g" + str(i) for i, g in enumerate(sorted(sizes))}
    lines = ["flowchart LR"]
    lines += ['  ' + label_ids[g] + '["' + g + ' (' + str(sizes[g]) + ')"]'
              for g in sorted(sizes)]
    by_id = {n["id"]: n for n in nodes}
    counter = Counter()
    for e in edges:
        if e["kind"] not in ("exact_import", "qualified_reference"): continue
        a, b = by_id[e["from"]]["group"], by_id[e["to"]]["group"]
        if a != b: counter[a, b] += 1
    for (a, b), c in sorted(counter.items(), key=lambda item: (-item[1], item[0])):
        lines.append("  " + label_ids[a] + " -->|" + str(c) + " source refs| " + label_ids[b])
    return "\n".join(lines) + "\n"


def module_mermaid(nodes, edges):
    strong = [e for e in edges if e["kind"] in ("exact_import", "qualified_reference")]
    active = {e["from"] for e in strong} | {e["to"] for e in strong}
    selected = [n for n in nodes if n["id"] in active]
    ids = {n["id"]: "f" + str(i) for i, n in enumerate(selected)}
    lines = ["flowchart LR"]
    for n in selected:
        prefix = "#" + n["scope"][2:] + " " if n["scope"].startswith("pr") else ""
        lines.append('  ' + ids[n["id"]] + '["' + prefix + Path(n["path"]).stem + '"]')
    for a, b in sorted({(e["from"], e["to"]) for e in strong}):
        lines.append("  " + ids[a] + " --> " + ids[b])
    return "\n".join(lines) + "\n"


def branch_mermaid(snap):
    prs = snap["prs"]
    reverse = {p["head_branch"]: p["number"] for p in prs}
    lines = ["flowchart LR", '  main["main"]']
    for p in prs:
        status = "merged" if p["merged"] else p["state"]
        lines.append('  p' + str(p["number"]) + '["PR #' + str(p["number"]) + ' ' + status + '"]')
    for p in prs:
        base = reverse.get(p["base_branch"])
        to = "p" + str(base) if base is not None else "main"
        lines.append("  p" + str(p["number"]) + " -.->|PR base| " + to)
    return "\n".join(lines) + "\n"


def main():
    arg = argparse.ArgumentParser()
    arg.add_argument("--out", default="docs/dependency/generated")
    arg.add_argument("--skip-prs", action="store_true")
    arg.add_argument("--main-ref", default="HEAD",
                     help="Immutable source Git revision for ALL main inputs (default: HEAD)")
    opts = arg.parse_args()
    source_commit = resolved_commit(opts.main_ref)
    baseline = {"linear_input/lean_check/" + p for p in
                assignment("linear_input/verify_lean.py", "PARTS", source_commit)}
    supplements = {p for p, ns in
                   assignment("tools/verify_main_result.py", "SUPPLEMENTS", source_commit)}
    snapshot = json.loads(committed_text(source_commit, "docs/dependency/pr_snapshot.json"))
    nodes = sources(baseline, supplements, source_commit)
    issues, pr_inputs = [], []
    if not opts.skip_prs:
        extra, pr_inputs = branch_sources(snapshot, baseline, supplements, source_commit)
        nodes += extra
    edges = source_edges(nodes)
    for n in nodes:
        del n["_code"]
    graph = {"schema_version":1, "repo":REPO, "main_commit":source_commit,
             "pr_snapshot":snapshot["snapshot_date"], "nodes":nodes, "edges":edges,
             "baseline_part_order":list(assignment("linear_input/verify_lean.py", "PARTS", source_commit)),
             "supplement_order":[p for p, _ in assignment("tools/verify_main_result.py", "SUPPLEMENTS", source_commit)],
             "prs":snapshot["prs"], "issues":issues, "pr_inputs":pr_inputs,
             "source_provenance":"Git blobs at main_commit; PR diffs from pinned base/head SHAs",
             "meaning":"Source textual evidence, not kernel-certified theorem dependency closure"}
    output = ROOT / opts.out
    output.mkdir(parents=True, exist_ok=True)
    (output / "graph.json").write_text(json.dumps(graph, indent=2, ensure_ascii=False) + "\n", "utf8")
    (output / "groups.mmd").write_text(group_mermaid(nodes, edges), "utf8")
    (output / "modules.mmd").write_text(module_mermaid(nodes, edges), "utf8")
    (output / "branches.mmd").write_text(branch_mermaid(snapshot), "utf8")
    with (output / "source-edges.tsv").open("w", encoding="utf8") as f:
        f.write("source\tdependency\tkind\tsymbols\n")
        for e in edges:
            f.write(e["from"] + "\t" + e["to"] + "\t" + e["kind"] + "\t" +
                    ",".join(e["symbols"]) + "\n")
    by_kind = Counter(e["kind"] for e in edges)
    counts = Counter(n["group"] for n in nodes)
    intro = [
        "# primitive-lean dependency graphs",
        "",
        "Snapshot: main " + str(source_commit) + ", PR metadata " + snapshot["snapshot_date"] + ".",
        "Main sources, registries and PR snapshot were read from Git blobs at main_commit.",
        "PR overlays use immutable base/head SHAs listed in graph.json pr_inputs.",
        "",
        "A --> B means A references B. It does NOT mean A mathematically implies B.",
        "",
        "This graph distinguishes (1) exact Lean import, (2) literal qualified declaration",
        "references, (3) globally unique bare-name candidates, and (4) PR base-target edges.",
        "Only (1) and (2) appear in the graphical source edges.",
        "",
        "Main files: " + str(sum(n["scope"] == "main" for n in nodes)) +
        "; PR overlay files: " + str(sum(n["scope"] != "main" for n in nodes)) + ".",
        "Declaration names scanned: " + str(sum(len(n["declarations"]) for n in nodes)) + ".",
        "Source edges: " + json.dumps(by_kind, ensure_ascii=False) + ".",
        "",
        "## Source group dependencies",
        "",
        "~~~mermaid", group_mermaid(nodes, edges).rstrip(), "~~~",
        "",
        "## PR targets (not theorem dependencies)",
        "",
        "~~~mermaid", branch_mermaid(snapshot).rstrip(), "~~~",
        "",
        "## Complete machine-readable outputs",
        "",
        "- graph.json: source files, declaration names, evidence and confidence classes",
        "- modules.mmd: exact import and qualified reference module graph",
        "- groups.mmd: overview by subject area",
        "- branches.mmd: PR target graph",
        "- source-edges.tsv: source-to-dependency evidence table",
        "",
        "## Limits",
        "",
        "Concatenation order in the generated All.lean / MainResult.lean is recorded,",
        "but is not itself considered a proof dependency.",
        "The scanner does not invoke Lean elaboration or trace theorem premises.",
        "The #70/#71 ParallelLocalGluing.inc implementations conflict and remain distinct.",
        "No IUT III 3.11 -> 3.12 proof is inferred from superficial thematic links.",
    ]
    if issues: intro.extend(["", "Skipped overlays:", *("- " + x for x in issues)])
    (output / "README.md").write_text("\n".join(intro) + "\n", "utf8")
    report = {"main":sum(n["scope"] == "main" for n in nodes),
              "overlays":sum(n["scope"] != "main" for n in nodes),
              "declarations":sum(len(n["declarations"]) for n in nodes),
              "edges":dict(by_kind), "groups":dict(counts), "issues":issues}
    print(json.dumps(report, ensure_ascii=False))
    assert report["main"] >= 130, "unexpected incomplete main source"
    assert len(baseline) >= 30 and len(supplements) >= 55, "incomplete assembly registry"
    assert by_kind["exact_import"] >= 20, "import graph unexpectedly empty"
    assert report["declarations"] >= 900, "declaration graph unexpectedly empty"


if __name__ == "__main__":
    main()
