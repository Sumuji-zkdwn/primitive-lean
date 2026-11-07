#!/usr/bin/env python3
"""Is a theorem about the initial objects, and does its proof pass through initial theorems?

Logically, every theorem accepted by Lean here is provable from Mathlib and its
own definitions alone; adding definitions is conservative, so "derivable from
the 465 initial theorems" cannot separate anything. This script asks the two
questions that can:

  vocabulary  Follow statement and definition edges from the theorem.
              A *new primitive* definition is a non-initial project definition whose
              own statement/definition closure contains no initial node: an object
              introduced from scratch. Classes:
                initial_only      reaches initial vocabulary, no new primitives
                mixed             reaches initial vocabulary and new primitives
                new_objects_only  new primitives only
                mathlib_only      no project definition at all
  proof       Does the transitive proof-edge closure contain an initial theorem?

Limits: two constants with different names are treated as different even if
they are definitionally equal (a re-defined copy of an initial object counts as
new). An absent proof path is not a proof that no derivation exists.
"""
from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path

CLASSES = ("initial_only", "mixed", "new_objects_only", "mathlib_only")


def classify(N, targets):
    layer = {n: r["layer"] for n, r in N.items()}
    voc = {n: set(r["direct"]["statement"]) | set(r["direct"]["definition"]) for n, r in N.items()}
    prf = {n: set(r["direct"]["proof"]) for n, r in N.items()}
    memo = {}

    def clo(adj, s, key):
        if (key, s) not in memo:
            seen, st = set(), [s]
            while st:
                x = st.pop()
                for y in adj.get(x, ()):
                    if y not in seen and y in N:
                        seen.add(y)
                        st.append(y)
            memo[(key, s)] = seen
        return memo[(key, s)]

    def is_def(n):
        return N[n]["kind"] != "theorem"

    out = {}
    for t in targets:
        V = clo(voc, t, "v")
        touches = any(layer[x] == "initial" for x in V)
        prims = sorted(x for x in V if is_def(x) and layer[x] != "initial"
                       and not any(layer[y] == "initial" for y in clo(voc, x, "v")))
        cls = ("initial_only" if touches and not prims else "mixed" if touches
               else "new_objects_only" if prims else "mathlib_only")
        through = sorted(x for x in clo(prf, t, "p") if layer[x] == "initial" and N[x]["kind"] == "theorem")
        out[t] = dict(vocabulary=cls, proof_through_initial=bool(through),
                      initial_theorems_in_proof=len(through), new_primitive_definitions=prims)
    return out


def table(counter):
    rows = ["| 命題の語彙 | 証明が初期定理を経由 | 経由しない | 計 |", "|---|---:|---:|---:|"]
    for c in CLASSES:
        a, b = counter[(c, True)], counter[(c, False)]
        rows.append(f"| {c} | {a} | {b} | {a + b} |")
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--main-deps", required=True)
    ap.add_argument("--compare", help="PR inventory compare.json")
    ap.add_argument("--kernel-dir", help="per-measurement deps (needed with --compare)")
    ap.add_argument("--absorbed", default="", help="comma-separated PR numbers to exclude from PR totals")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    M = json.loads(Path(a.main_deps).read_text())["nodes"]
    res = dict(main={}, prs={})
    for L in ("subsequent", "autonomy"):
        t = [n for n, r in M.items() if r["kind"] == "theorem" and r["layer"] == L]
        res["main"][L] = classify(M, t)
    if a.compare:
        C = json.loads(Path(a.compare).read_text())["prs"]
        cache = {}
        for n, r in C.items():
            k = r["kernel"]
            if k["status"] != "ok":
                continue
            tip = r["kernel_tip"]
            if tip not in cache:
                cache[tip] = json.loads((Path(a.kernel_dir) / tip / "deps.json").read_text())["nodes"]
            N = cache[tip]
            res["prs"][n] = classify(N, [x for x in k["new_names"] if x in N and N[x]["kind"] == "theorem"])
    absorbed = set(filter(None, a.absorbed.split(",")))

    def count(d):
        return collections.Counter((v["vocabulary"], v["proof_through_initial"]) for v in d.values())
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / "grounding.json").write_text(json.dumps(res, ensure_ascii=False, indent=1))
    L = ["# 初期層からの導出可能性：何が問えるか（2026-11-07）", "",
         "## 前提", "",
         "- Lean が受理した定理は、どれも mathlib と自身の定義だけから証明されている。新しい定義の追加は保存的拡大なので、"
         "論理の意味での「初期 465 定理から導けるか」は、すべての定理について自明に成り立ち、何も区別しない。",
         "- そこで次の 2 軸で分ける。",
         "  1. **命題の語彙**：命題と定義をたどって、初期の対象に行き着くか。初期層に一度も触れずに mathlib だけから定義された"
         "プロジェクトの定義を「新しい原始的対象」と呼ぶ。",
         "  2. **証明の経路**：証明項の連鎖が、初期の定理を実際に経由しているか。",
         "- 語彙が `new_objects_only` または `mathlib_only` の定理は、初期の対象について何も述べていないので、"
         "「初期定理から導けるか」という問い自体が成り立たない。",
         "- 語彙が `initial_only` で証明が初期定理を経由しない定理が、「初期定理から導けるかもしれないが示されていない」候補である。",
         "- 名前の違う定数は、定義として等しくても別物として数える（初期の対象を作り直した写しは「新しい対象」に入る）。", "",
         "## main の後続層（984 定理）", ""]
    L += table(count(res["main"]["subsequent"]))
    L += ["", "## main の自動生成定理（成長ブランチ cycle 1–2）", ""]
    L += table(count(res["main"]["autonomy"]))
    if res["prs"]:
        tot = collections.Counter()
        for n, d in res["prs"].items():
            if n not in absorbed:
                tot += count(d)
        L += ["", f"## 未統合 PR の新しい定理（吸収案の PR {', '.join('#' + x for x in sorted(absorbed, key=int))} を除く）", ""]
        L += table(tot)
        L += ["", "### 語彙が初期の対象だけで書ける定理を持つ PR", "",
              "| PR | initial_only | うち初期定理を経由 | mixed |", "|---|---:|---:|---:|"]
        for n in sorted(res["prs"], key=int):
            c = count(res["prs"][n])
            g = c[("initial_only", True)] + c[("initial_only", False)]
            if g:
                L.append(f"| #{n} | {g} | {c[('initial_only', True)]} | {c[('mixed', True)] + c[('mixed', False)]} |")
    (out / "README.md").write_text("\n".join(L) + "\n", encoding="utf-8")
    print("\n".join(L[-30:]))


if __name__ == "__main__":
    main()
