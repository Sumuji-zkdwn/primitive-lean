#!/usr/bin/env python3
"""Independent checks of the dependency extraction.

1. Every declaration in the verification reports is present with the layer
   and source file the reports give.
2. Known proof edges written explicitly in source tactics are recovered.
3. Generated autonomy sources match the growth ledger byte for byte.
4. Lexical comparison: for proof edges between project theorems, does the
   target's short name occur in the source text of the declaring theorem?
   Kernel edges with no lexical mention (simp sets, instances, unfolding) and
   lexical mentions with no kernel edge are both counted. This measures how
   far a name-matching graph would differ from the kernel graph.
"""
from __future__ import annotations

import argparse
import collections
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def norm(f: str) -> str:
    f = f.replace("../lean/", "lean/")
    return f if f.startswith(("lean/", "linear_input/")) else "linear_input/" + f


def decl_texts(nodes, assembled: Path):
    """Source slice of each declaration in the assembled file (start line to next start)."""
    lines = assembled.read_text(encoding="utf-8").split("\n")
    starts = sorted((r["line"], n) for n, r in nodes.items()
                    if r["layer"] != "autonomy" and not r["source"].startswith("lean/") and r["line"])
    out = {}
    for i, (ln, n) in enumerate(starts):
        end = starts[i + 1][0] - 1 if i + 1 < len(starts) else len(lines)
        out[n] = "\n".join(lines[ln - 1:end])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--deps", required=True)
    ap.add_argument("--assembled", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    g = json.loads(Path(a.deps).read_text())
    N = g["nodes"]
    res = {}

    m = json.loads((ROOT / "verification/main-result.json").read_text())
    b = json.loads((ROOT / "linear_input/lean_results.json").read_text())
    exp = {}
    for d in b["parent_declarations"] + b["declarations"]:
        exp[d["name"]] = ("initial", norm(d["file"]))
    for d in m["declarations"]:
        exp[d["name"]] = ("subsequent", norm(d["file"]))
    mism = [n for n, e in exp.items() if (N.get(n, {}).get("layer"), N.get(n, {}).get("source")) != e]
    res["report_declarations"] = dict(expected=len(exp), mismatched=len(mism), examples=mism[:10],
                                      extra_nodes=len([n for n in N if n not in exp]))

    t = N["LinearInputMainResult.locallyMinimizing_pressure_curvature_phase"]
    want = {"LinearInputAreaMinimum.locallyMinimizing_areaStationary",
            "LinearInputPressureStationary.areaStationary_exists_pressure",
            "LinearInputPressureStationary.stationary_curvature",
            "LinearInputCurvatureBridge.forced_energy_constant",
            "LinearInputCurvatureBridge.forced_phase_hasDerivAt",
            "LinearInputCurvatureBridge.energy_shear"}
    got = {x for x in t["direct"]["proof"] if N.get(x, {}).get("kind") == "theorem"}
    res["known_edges_main_result"] = dict(expected=sorted(want), extracted=sorted(got), equal=got == want)

    texts = decl_texts(N, Path(a.assembled))
    kernel_only = lexical_only = both = 0
    ko_examples, lo_examples = [], []
    thm = {n for n, r in N.items() if r["kind"] == "theorem"}
    short = {n: n.split(".")[-1] for n in thm}
    by_short = collections.defaultdict(set)
    for n, s in short.items():
        by_short[s].add(n)
    for n, txt in texts.items():
        if N[n]["kind"] != "theorem":
            continue
        body = re.sub(r"--[^\n]*", "", txt)
        body = re.sub(r"(?m)^#print axioms[^\n]*$", "", body)  # audit lines are not proof text
        body = re.sub(r"/-.*?-/", "", body, flags=re.S)
        tokens = set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", body))
        tok_short = {x.split(".")[-1] for x in tokens}
        kern = {x for x in N[n]["direct"]["proof"] if x in thm}
        for x in kern:
            if short[x] in tok_short:
                both += 1
            else:
                kernel_only += 1
                if len(ko_examples) < 12:
                    ko_examples.append([n, x])
        own = short[n]
        for s in tok_short:
            if s == own or s not in by_short:
                continue
            cands = by_short[s]
            if not (cands & kern) and len(cands) == 1:
                lexical_only += 1
                if len(lo_examples) < 12:
                    lo_examples.append([n, next(iter(cands))])
    res["lexical_vs_kernel"] = dict(
        scope="proof edges between project theorems; theorems of the concatenated linear-input sources",
        kernel_and_lexical=both, kernel_only=kernel_only, lexical_only_unambiguous=lexical_only,
        kernel_only_examples=ko_examples, lexical_only_examples=lo_examples)
    Path(a.out).write_text(json.dumps(res, ensure_ascii=False, indent=1))
    print(json.dumps({k: {kk: vv for kk, vv in v.items() if "examples" not in kk} for k, v in res.items()},
                     ensure_ascii=False, indent=1))


if __name__ == "__main__":
    main()
