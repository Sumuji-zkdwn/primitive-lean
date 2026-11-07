#!/usr/bin/env python3
"""Typed dependency analysis over the kernel-accepted declarations.

Input: the JSON written by tools/deps/ExtractDeps.lean, the exact assembled
source that was compiled (MainResult.lean), and the verification reports.

Edge categories are kept apart and never merged in the output:
  proof       constants occurring in a theorem's elaborated proof term
  statement   constants occurring in a declaration's type
  definition  constants occurring in a definition's body
  module      import edges between compiled modules (Elastica library only;
              the linear-input sources are textually concatenated, so for
              them only the registered assembly order exists)
  conceptual  never produced by this tool; reserved for reviewed bridges

An edge records an occurrence. It does not assert that the target is
mathematically necessary, and the absence of a path to the initial layer is
not evidence that a statement cannot be derived from it.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PROOFS = ROOT / "linear_input" / "lean_check"

# Proof-term glue that carries no mathematical content of its own.
GLUE_PREFIXES = ("Eq.", "id", "of_eq_true", "eq_self", "trivial", "True.", "And.", "Iff.",
                 "propext", "congrArg", "congrFun", "cast", "Exists.", "Or.", "absurd", "False.")
DECIDE_MARKERS = {"of_decide_eq_true", "Decidable.decide", "decide_eq_true"}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def strip_private(name: str) -> str:
    m = re.match(r"_private\.[^.]+(?:\.[^.]+)*?\.\d+\.(.*)", name)
    return m.group(1) if m else name


def line_map(assembled: Path, report: dict, root: Path = ROOT):
    """Map each line of the assembled file to (layer, source file)."""
    text = assembled.read_bytes()
    all_bytes = (root / "linear_input/lean_check/All.lean").read_bytes()
    start = text.find(all_bytes)
    prefix = text[:start] if start >= 0 else b""
    # Some assembler versions hoist extra imports above the exact All.lean bytes.
    if start < 0 or any(l and not l.startswith(b"import ") for l in prefix.split(b"\n")):
        raise ValueError("assembled source does not contain the exact All.lean after an import-only prefix")
    shift = prefix.count(b"\n")
    spans = []  # (first_line, last_line, layer, file)
    # Inside All.lean: '-- Source: X' markers written by linear_input/verify_lean.py.
    all_lines = all_bytes.decode("utf-8").split("\n")
    current = None
    start_line = 1
    for i, line in enumerate(all_lines, 1):
        m = re.match(r"-- Source: (\S+)$", line)
        if m:
            if current:
                spans.append((start_line, i - 1, "initial", "linear_input/lean_check/" + current))
            current, start_line = m.group(1), i
    spans.append((start_line, len(all_lines), "initial", "linear_input/lean_check/" + current))
    spans = [(f + shift, l + shift, y, src) for f, l, y, src in spans]
    offset = shift + all_bytes.count(b"\n") + 1  # pieces are joined with b"\n"
    pos = start + len(all_bytes) + 1
    for source in report["supplemental_sources"]:
        data = (root / source).read_bytes()
        if text[pos:pos + len(data)] != data:
            raise ValueError("assembly mismatch at " + source)
        first = offset + 1
        last = first + data.count(b"\n")
        spans.append((first, last, "subsequent", source))
        offset = last
        pos += len(data) + 1
    return spans


def locate(spans, line):
    for first, last, layer, src in spans:
        if first <= line <= last:
            return layer, src
    return None, None


def origin_of_module(module: str) -> str:
    top = module.split(".")[0]
    if top == "Mathlib":
        return "mathlib"
    if top in ("Init", "Lean", "Std"):
        return "core"
    if top == "Batteries":
        return "batteries"
    return "other:" + top


def build(raw: dict, spans, autonomy_sources: dict, module_sources: dict | None = None,
          module_spans: dict | None = None):
    module_sources = module_sources or {}
    module_spans = module_spans or {}
    decls = {d["name"]: d for d in raw["declarations"]}
    external = {e["name"]: e for e in raw["external"]}

    # 1. User-level declarations: carry a source range and are not internal.
    user = {n for n, d in decls.items() if d["line"] is not None and not d["internal"]}

    def owner(name: str):
        if name in user:
            return name
        base = strip_private(name)
        prefix = name[:len(name) - len(base)]  # "_private.<module>.0." or ""
        parts = base.split(".")
        for k in range(len(parts) - 1, 0, -1):
            stem = ".".join(parts[:k])
            for cand in ((prefix + stem, stem) if prefix else (stem,)):
                if cand in user:
                    return cand
        return None

    # Generated constants with no user-level owner (e.g. derived instances)
    # become nodes of their own.
    for n, d in decls.items():
        if n not in user and owner(n) is None:
            user.add(n)

    # 2. Layer of each user-level node.
    layer, source = {}, {}
    for n in user:
        d = decls[n]
        mod = d["module"]
        if mod.startswith("Elastica"):
            layer[n], source[n] = "initial", "lean/" + mod.replace(".", "/") + ".lean"
        elif mod == "AutonomyProbe":
            layer[n] = "autonomy"
            m = re.match(r"LinearInputAutoCycle(\d+)\.", n)
            source[n] = autonomy_sources.get(int(m.group(1))) if m else "AutonomyProbe"
        elif mod == "PrimitiveMain":
            ln = d["line"]
            if ln is None:  # generated, ownerless: inherit from namespace siblings
                layer[n], source[n] = None, None
                continue
            layer[n], source[n] = locate(spans, ln)
        elif mod in module_spans and d["line"] is not None:
            # Standalone concatenation: attribute each declaration to its source file by line.
            layer[n] = "module"
            source[n] = next((src for f, l, src in module_spans[mod] if f <= d["line"] <= l), "unresolved")
        elif mod in module_sources:
            # Separately compiled module (isolated Lean file or probe stacked on the assembly).
            layer[n], source[n] = "module", module_sources[mod]
        else:
            raise ValueError("unexpected module " + mod)
    by_namespace = collections.defaultdict(set)
    for n in user:
        if layer.get(n):
            by_namespace[n.split(".")[0]].add((layer[n], source[n]))
    for n in user:
        if layer.get(n) is None:
            cands = by_namespace.get(strip_private(n).split(".")[0], set())
            if len(cands) == 1:
                layer[n], source[n] = next(iter(cands))
            else:
                layer[n], source[n] = "unresolved", None

    # 3. Resolve a referenced constant to node ids.
    # Lean shares auxiliary proofs (`_proof_N`, `_simp_N`, `_auxLemma`) between
    # declarations with the same proposition. A reference to another declaration's
    # shared proof is not a dependency on that declaration: expand its contents.
    # Equation lemmas and matchers do mean unfolding the owner, so they map to it.
    def is_shared_proof(c: str) -> bool:
        return any(re.match(r"^_?(proof_\d|simp_\d|auxLemma)", part) for part in c.split(".")[1:])

    def targets(c: str, seen=None):
        if c in decls:
            o = owner(c)
            if o and o != c and is_shared_proof(c):
                seen = seen if seen is not None else set()
                if c in seen:
                    return
                seen.add(c)
                d = decls[c]
                for x in d["type_consts"] + d["value_consts"]:
                    yield from targets(x, seen)
                return
            yield ("project", o if o else c)
            return
        e = external.get(c)
        yield (origin_of_module(e["module"]) if e else "unknown", c)

    # 4. Typed edges. Constants of a node's own auxiliaries are inlined.
    own_aux = collections.defaultdict(list)
    for n in decls:
        o = owner(n)
        if o and o != n:
            own_aux[o].append(n)

    edges = {cat: collections.defaultdict(set) for cat in ("proof", "statement", "definition")}
    external_edges = {cat: collections.defaultdict(set) for cat in ("proof", "statement", "definition")}
    heads = {}
    for n in user:
        d = decls[n]
        is_thm = d["kind"] == "theorem"
        groups = {"statement": list(d["type_consts"]),
                  ("proof" if is_thm else "definition"): list(d["value_consts"])}
        for aux in own_aux.get(n, []):
            a = decls[aux]
            # Auxiliary pieces of a theorem's proof belong to the proof;
            # equation lemmas and matchers of a definition belong to its definition.
            cat = "proof" if is_thm else "definition"
            groups.setdefault(cat, [])
            groups[cat] += a["type_consts"] + a["value_consts"]
        for cat, consts in groups.items():
            for c in consts:
                for kind, t in targets(c):
                    if kind == "project":
                        if t != n:
                            edges[cat][n].add(t)
                    else:
                        external_edges[cat][n].add((kind, t))
        heads[n] = d["head"]
    return dict(decls=decls, user=user, layer=layer, source=source, edges=edges,
                external_edges=external_edges, heads=heads, external=external)


def analyze(g):
    decls, user, layer, edges = g["decls"], g["user"], g["layer"], g["edges"]
    kind = {n: decls[n]["kind"] for n in user}
    thms = {n for n in user if kind[n] == "theorem"}
    all_edges = collections.defaultdict(set)
    for cat in edges:
        for a, bs in edges[cat].items():
            all_edges[a] |= bs

    order = sorted(user, key=lambda n: (decls[n]["module"] != "Elastica", decls[n]["line"] or 0))
    # Lean's declaration order guarantees acyclicity; compute closures by memoised DFS.
    memo_all, memo_proof = {}, {}

    def closure(n, adj, memo):
        if n in memo:
            return memo[n]
        stack, seen = [n], set()
        while stack:
            x = stack.pop()
            for y in adj.get(x, ()):
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        memo[n] = seen
        return seen

    proof_adj = {a: {b for b in bs if b in thms} for a, bs in edges["proof"].items()}
    depth = {}

    def proof_depth(n):
        if n in depth:
            return depth[n]
        stack = [(n, False)]
        while stack:
            x, done = stack.pop()
            if x in depth:
                continue
            kids = proof_adj.get(x, set())
            if done:
                depth[x] = 0 if not kids else 1 + max(depth[k] for k in kids)
            else:
                stack.append((x, True))
                stack.extend((k, False) for k in kids if k not in depth)
        return depth[n]

    def hops_to_initial(n, adj):
        if layer[n] == "initial":
            return 0
        frontier, seen, h = {n}, {n}, 0
        while frontier:
            h += 1
            nxt = set()
            for x in frontier:
                for y in adj.get(x, ()):
                    if y in seen:
                        continue
                    if layer.get(y) == "initial":
                        return h
                    seen.add(y)
                    nxt.add(y)
            frontier = nxt
        return None

    rows = {}
    for n in user:
        if kind[n] not in ("theorem", "def", "inductive", "opaque"):
            continue
        clo = closure(n, all_edges, memo_all)
        pclo = closure(n, proof_adj, memo_proof)
        direct = {cat: sorted(edges[cat].get(n, ())) for cat in edges}
        by_layer = collections.Counter(layer.get(t) for t in clo)
        head = g["heads"].get(n)
        proof_consts = edges["proof"].get(n, set())
        ext_proof = g["external_edges"]["proof"].get(n, set())
        project_thms_used = sorted(t for t in proof_consts if t in thms)
        head_const = head["const"] if head else None
        head_is_project_thm = head_const is not None and head_const in thms
        shape = None
        own_src = g["source"][n]
        foreign_thms = [t for t in project_thms_used if g["source"].get(t) != own_src]
        uses_decision = bool({t for _, t in ext_proof} & DECIDE_MARKERS)
        if kind[n] == "theorem":
            if head_is_project_thm and g["source"].get(head_const) != own_src and foreign_thms == [head_const]:
                # The proof term is one earlier theorem applied to arguments; any other
                # project theorems used come from the same source file (local lemmas).
                shape = "application_of_earlier_theorem"
            elif not project_thms_used and uses_decision:
                shape = "decision_procedure_only"
            elif not project_thms_used:
                shape = "library_only"
            else:
                shape = "composite"
        rows[n] = dict(
            name=n, kind=kind[n], layer=layer[n], source=g["source"][n],
            line=decls[n]["line"],
            direct=direct,
            direct_external_counts={cat: dict(collections.Counter(k for k, _ in g["external_edges"][cat].get(n, ())))
                                    for cat in edges},
            transitive_project=len(clo),
            transitive_by_layer=dict(by_layer),
            reaches_initial_any_edge=by_layer.get("initial", 0) > 0,
            initial_reached=sorted(t for t in clo if layer.get(t) == "initial"),
            hops_to_initial_any_edge=hops_to_initial(n, all_edges),
            hops_to_initial_proof_only=hops_to_initial(n, proof_adj) if kind[n] == "theorem" else None,
            proof_depth=proof_depth(n) if kind[n] == "theorem" else None,
            proof_closure_size=len(pclo) if kind[n] == "theorem" else None,
            head=head_const, proof_shape=shape, uses_kernel_decision=uses_decision if kind[n] == "theorem" else None,
            foreign_project_theorems_in_proof=len(foreign_thms) if kind[n] == "theorem" else None,
        )
    return rows


def source_graph(g, rows):
    """Aggregate typed edges between source files (for inventory and ERG mapping)."""
    agg = collections.defaultdict(lambda: collections.Counter())
    for n, r in rows.items():
        for cat, ts in r["direct"].items():
            for t in ts:
                s, u = g["source"].get(n), g["source"].get(t)
                if s and u and s != u:
                    agg[(s, u)][cat] += 1
    return [dict(source=s, target=u, counts=dict(c)) for (s, u), c in sorted(agg.items())]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--raw", required=True)
    ap.add_argument("--assembled", help="assembled MainResult.lean (omit for standalone modules)")
    ap.add_argument("--report", default=str(ROOT / "verification/main-result.json"))
    ap.add_argument("--autonomy-ledger")
    ap.add_argument("--out", required=True)
    ap.add_argument("--root", default=str(ROOT), help="repository checkout the assembly came from")
    ap.add_argument("--module-source", action="append", default=[],
                    help="MODULE=source/path for separately compiled modules")
    ap.add_argument("--module-spans", action="append", default=[],
                    help="MODULE=spans.json: [[first_line, last_line, source], ...] for concatenated modules")
    a = ap.parse_args()
    raw = json.loads(Path(a.raw).read_text())
    if a.assembled:
        report = json.loads(Path(a.report).read_text())
        spans = line_map(Path(a.assembled), report, Path(a.root))
    else:
        spans = []  # standalone modules only; every node comes from --module-source
    auto = {}
    if a.autonomy_ledger:
        for c in json.loads(Path(a.autonomy_ledger).read_text())["cycles"]:
            auto[c["cycle"]] = c["source"]
    mods = dict(x.split("=", 1) for x in a.module_source)
    mspans = {m: json.loads(Path(f).read_text()) for m, f in (x.split("=", 1) for x in a.module_spans)}
    g = build(raw, spans, auto, mods, mspans)
    rows = analyze(g)
    modules = raw["module_imports"]
    out = dict(
        scope=("Occurrences of constants in kernel-accepted types, proof terms and definition bodies. "
               "An edge is not a claim of mathematical necessity; a missing path is not a proof of "
               "non-derivability. No conceptual edges are produced."),
        inputs=dict(raw_sha256=sha(Path(a.raw).read_bytes()),
                    assembled_sha256=sha(Path(a.assembled).read_bytes()) if a.assembled else None,
                    report_sha256=sha(Path(a.report).read_bytes()) if a.assembled else None),
        source_spans=[dict(first_line=f, last_line=l, layer=y, source=s) for f, l, y, s in spans],
        module_imports=modules,
        nodes=rows,
        source_edges=source_graph(g, rows),
    )
    Path(a.out).write_text(json.dumps(out, ensure_ascii=False, indent=1))
    print(json.dumps(dict(nodes=len(rows), layers=collections.Counter(r["layer"] for r in rows.values())),
                     ensure_ascii=False))


if __name__ == "__main__":
    main()
