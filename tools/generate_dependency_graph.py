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
SNAP = ROOT / "docs/dependency/pr_snapshot.json"
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


def assignment(filename, key):
    root = ast.parse((ROOT / filename).read_text("utf8"))
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


def sources(baseline, supplements):
    paths = sorted((ROOT / "lean").rglob("*.lean"))
    paths += sorted((ROOT / "linear_input/lean_check").glob("*.lean"))
    paths += sorted((ROOT / "linear_input/lean_check").glob("*.inc"))
    paths = [p for p in paths if p.is_file() and p.name not in ("All.lean", "MainResult.lean")]
    return [source_node(p.relative_to(ROOT).as_posix(), p.read_text("utf8"),
                        "main", baseline, supplements) for p in paths]


def branch_sources(snap, baseline, supplements):
    overlay, issues = [], []
    interesting = {31, 65, 66, 67, 69, 70, 71, 72, 75, 77, 78}
    for pr in snap["prs"]:
        n, head, base = pr["number"], pr.get("head_sha"), pr.get("base_branch")
        if n not in interesting: continue
        if not head or git("cat-file", "-e", head + "^{commit}") is None:
            issues.append("PR #" + str(n) + ": head commit unavailable")
            continue
        base_ref = "refs/remotes/origin/" + str(base)
        if git("cat-file", "-e", base_ref + "^{commit}") is None:
            issues.append("PR #" + str(n) + ": base ref unavailable")
            continue
        paths = git("diff", "--name-only", base_ref + "..." + head)
        if paths is None:
            issues.append("PR #" + str(n) + ": unable to compare base")
            continue
        for path in paths.splitlines():
            if not (path.endswith(".lean") or path.endswith(".inc")): continue
            if not path.startswith(("lean/", "linear_input/lean_check/")): continue
            data = git("show", head + ":" + path)
            if data is not None:
                overlay.append(source_node(path, data, "pr" + str(n), baseline, supplements))
    return overlay, issues


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
    opts = arg.parse_args()
    baseline = {"linear_input/lean_check/" + p for p in
                assignment("linear_input/verify_lean.py", "PARTS")}
    supplements = {p for p, ns in
                   assignment("tools/verify_main_result.py", "SUPPLEMENTS")}
    snapshot = json.loads(SNAP.read_text("utf8"))
    nodes = sources(baseline, supplements)
    issues = []
    if not opts.skip_prs:
        extra, issues = branch_sources(snapshot, baseline, supplements)
        nodes += extra
    edges = source_edges(nodes)
    for n in nodes:
        del n["_code"]
    head_main = git("rev-parse", "refs/remotes/origin/main") or git("rev-parse", "HEAD")
    graph = {"schema_version":1, "repo":REPO, "main_commit":head_main,
             "pr_snapshot":snapshot["snapshot_date"], "nodes":nodes, "edges":edges,
             "baseline_part_order":list(assignment("linear_input/verify_lean.py", "PARTS")),
             "supplement_order":[p for p, _ in assignment("tools/verify_main_result.py", "SUPPLEMENTS")],
             "prs":snapshot["prs"], "issues":issues,
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
        "Snapshot: main " + str(head_main) + ", PR metadata " + snapshot["snapshot_date"] + ".",
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
