#!/usr/bin/env python3
"""Emit inspectable finite observer-orientation evidence from GitHub request JSON.

This is exact finite PYTHON enumeration, not a general Lean theorem. The
Proof Forge workflow separately Lean-certifies the chosen representative
pairs and audits the generated proof dependencies.
"""
from __future__ import annotations

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path

from tools.autonomy import proof_forge as pf

NAMES = (
    "orientation_old_alphabet", "orientation_extended_alphabet",
    "orientation_primitive", "orientation_macro",
    "orientation_hidden_primitive", "orientation_hidden_macro",
    "orientation_hidden_quotient",
)


def load(root):
    req = root / "proof_forge/requests"
    models = {name: pf.read_request(req / (name + ".json")) for name in NAMES}
    hashes = {name: sha256((req / (name + ".json")).read_bytes()).hexdigest()
              for name in NAMES}
    return models, hashes


def check_model_relations(models):
    old = models["orientation_old_alphabet"]
    new = models["orientation_extended_alphabet"]
    p = models["orientation_primitive"]
    m = models["orientation_macro"]
    hp = models["orientation_hidden_primitive"]
    hm = models["orientation_hidden_macro"]
    hq = models["orientation_hidden_quotient"]
    if old["observations"] != [0, 0, 1] or old["transitions"] != [[0, 1, 2]]:
        raise ValueError("old vocabulary differs from archived research object")
    if new["observations"] != old["observations"] or new["transitions"] != [[0, 1, 2], [0, 2, 2]]:
        raise ValueError("new vocabulary differs from archived research object")
    if p["observations"] != [0, 0, 0, 1] or p["transitions"] != [[0, 2, 3, 3]]:
        raise ValueError("primitive differs from archived research object")
    step = p["transitions"][0]
    compiled = [step[step[s]] for s in range(4)]
    if m["observations"] != p["observations"] or m["transitions"] != [step, compiled]:
        raise ValueError("macro must be precisely two primitive steps")
    lifted = [step[i % 4] + 4 * (i // 4) for i in range(8)]
    lifted_macro = [lifted[lifted[i]] for i in range(8)]
    readout = p["observations"] * 2
    if hp["observations"] != readout or hp["transitions"] != [lifted]:
        raise ValueError("incorrect eight-state primitive lift")
    if hm["observations"] != readout or hm["transitions"] != [lifted, lifted_macro]:
        raise ValueError("incorrect eight-state compiled lift")
    if hq["transitions"] != hm["transitions"] or hq["observations"] != readout:
        raise ValueError("hidden state not evaluated with compiled vocabulary")
    if any(models[name]["pair"] != [0,1] for name in NAMES if name != "orientation_hidden_quotient"):
        raise ValueError("unexpected designated distinguishing pair")
    if hq["pair"] != [0,4]:
        raise ValueError("wrong designated hidden pair")


def result(model, x, y):
    altered = dict(model, pair=[x,y])
    answer = pf.solve(altered)
    pf.validate_result(altered, answer)
    if answer["kind"] == "EQUIVALENT":
        return {"word": None, "depth": None, "equivalent": True}
    return {"word": answer["word"], "depth": len(answer["word"]),
            "equivalent": False}


def compare(p, m):
    n = len(p["observations"])
    if p["observations"] != m["observations"]:
        raise ValueError("readout mismatch")
    records, pc, mc = [], Counter(), Counter()
    for x in range(n):
        for y in range(n):
            a, b = result(p, x, y), result(m, x, y)
            if a["equivalent"] != b["equivalent"]:
                raise ValueError(f"compiled macro changed equivalence: {(x,y)}")
            if not a["equivalent"] and b["depth"] > a["depth"]:
                raise ValueError(f"compiled macro increased depth: {(x,y)}")
            pc[str(a["depth"])] += 1
            mc[str(b["depth"])] += 1
            records.append({"pair":[x,y], "primitive":a, "macro":b})
    classes = []
    for i in range(n):
        if any(i in cls for cls in classes):
            continue
        cls = [j for j in range(n)
               if next(r for r in records if r["pair"] == [i,j])["primitive"]["equivalent"]]
        for j in cls:
            for k in range(n):
                found = next(r for r in records if r["pair"] == [j,k])["primitive"]["equivalent"]
                if found != (k in cls):
                    raise ValueError("failed equivalence relation closure")
        classes.append(cls)
    return {"ordered_pairs_checked": n * n,
            "predictive_quotient": classes,
            "primitive_depth_histogram": dict(pc),
            "macro_depth_histogram": dict(mc),
            "pairs": records}


def build(root, head):
    if not pf.HEAD.fullmatch(head):
        raise ValueError("full exact source SHA required")
    models, hashes = load(root)
    check_model_relations(models)
    old, new = (result(models[name], 0,1) for name in
                ("orientation_old_alphabet", "orientation_extended_alphabet"))
    four = compare(models["orientation_primitive"], models["orientation_macro"])
    eight = compare(models["orientation_hidden_primitive"], models["orientation_hidden_macro"])
    hidden = result(models["orientation_hidden_quotient"], 0,4)
    if not old["equivalent"] or new["word"] != [1] or not hidden["equivalent"]:
        raise ValueError("selected research results differ")
    if four["predictive_quotient"] != [[0],[1],[2],[3]]:
        raise ValueError("unexpected four-state quotient")
    if eight["predictive_quotient"] != [[0,4],[1,5],[2,6],[3,7]]:
        raise ValueError("unexpected eight-state quotient")
    if eight["primitive_depth_histogram"] != {"None":16, "0":24,"1":16,"2":8}:
        raise ValueError("unexpected primitive depth histogram")
    if eight["macro_depth_histogram"] != {"None":16, "0":24, "1":24}:
        raise ValueError("unexpected macro depth histogram")
    return {"schema_version":1, "source_commit":head, "input_sha256":hashes,
            "status":"FINITE_PYTHON_ENUMERATION_NOT_A_LEAN_PROOF",
            "kernel_verified":False, "old_vocabulary":old,
            "new_vocabulary":new, "four_state":four, "eight_state":eight,
            "hidden_pair":hidden, "passed":True}


def markdown(report):
    four, eight = report["four_state"], report["eight_state"]
    p, m = eight["primitive_depth_histogram"], eight["macro_depth_histogram"]
    rows = "\n".join(f"| {key} | {p.get(key,0)} | {m.get(key,0)} |"
                     for key in ["None","0","1","2"])
    return (
        "## Proof Forge: real observer-orientation research\n\n"
        "Independent finite Python enumeration, not an all-pairs Lean proof. "
        "Specified examples have separate Lean kernel certificates.\n\n"
        f"Source commit: {report['source_commit']}\n\n"
        f"Four-state quotient: {four['predictive_quotient']}\n\n"
        f"Eight-state quotient: {eight['predictive_quotient']}\n\n"
        "| Minimum depth | Primitive only | Primitive + compiled macro |\n"
        "| --- | ---: | ---: |\n"
        f"{rows}\n\n"
        "None means unseparable by any finite word in the chosen finite model. "
        "Length counts named operations, not physical time.\n"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--markdown", type=Path)
    args = parser.parse_args()
    report = build(args.root, args.head)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n",
                           encoding="utf-8")
    if args.markdown:
        with args.markdown.open("a", encoding="utf-8") as stream:
            stream.write(markdown(report))
    print(json.dumps({"passed":report["passed"], "python_only":True,
                      "ordered_pairs":report["four_state"]["ordered_pairs_checked"]
                                       +report["eight_state"]["ordered_pairs_checked"],
                      "quotient":report["eight_state"]["predictive_quotient"]}))


if __name__ == "__main__":
    main()
