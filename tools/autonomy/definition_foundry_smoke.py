#!/usr/bin/env python3
"""Reviewable independent kernel checks for a small typed observation grammar.

Generate only declarative finite models and Lean sources. Never execute
untrusted notes; no certificate is called verified until --trust=0 audit.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from tools.autonomy import definition_foundry as f
from tools.autonomy import finite_discovery as fd
from tools.autonomy import proof_forge as pf
from tools.autonomy import research_conveyor_routes as routes


def cases(root):
    observer = fd.rename_model(routes.observer_model(root, "observer_primitive"))
    laakso = fd.rename_model(routes.laakso_model("laakso_w1_advance"))
    s0 = {"op": "read"}
    ahead = {"op": "after", "action": 0, "arg": s0}
    ahead2 = {"op": "after", "action": 0, "arg": ahead}
    bit0 = {"op": "bit", "label": 1, "arg": s0}
    bit1 = {"op": "bit", "label": 1, "arg": ahead}
    return (
        ("lookahead2", observer, ahead2),
        ("compare", observer, {"op": "eq", "left": s0, "right": ahead}),
        ("pair_flag", observer, {"op": "pair", "left": bit0, "right": bit1}),
        ("xor_flag", observer, {"op": "xor", "left": bit0, "right": bit1}),
        ("laakso_next", laakso, {"op": "after", "action": 1, "arg": s0}),
    )


def generate(root, output, head):
    if not pf.HEAD.fullmatch(head):
        raise ValueError("invalid exact commit SHA")
    if output.exists() and any(output.iterdir()):
        raise ValueError("nonempty smoke output")
    output.mkdir(parents=True)
    manifest = []
    for label, machine, expr in cases(root):
        target = f.derived_model(machine, expr)
        if machine == target:
            raise ValueError("uninformative smoke definition")
        folder = output / label
        requests = folder / "requests"
        requests.mkdir(parents=True)
        for model in (machine, target):
            f.save(requests / (model["name"]+".json"), model)
            if pf.read_request(requests / (model["name"]+".json")) != model:
                raise ValueError("invalid generated finite model")
        pf.generate(requests, folder / "proof", head)
        (folder / "semantics.lean").write_text(
            f.semantics_source(machine, expr, target), "utf-8")
        manifest.append({"case": label, "source_name": machine["name"],
                         "target_name": target["name"],
                         "expression": expr, "kernel_verified": False})
    f.save(output / "smoke.json", {"checkout_sha": head, "cases": manifest,
                                 "scope": "FINITE_OBSERVATION_DEFINITION_ONLY"})
    print(json.dumps({"cases": len(manifest), "lean_verified": False}))


def audit(root, output, head):
    manifest = f.load(output / "smoke.json")
    if manifest["checkout_sha"] != head:
        raise ValueError("smoke checkout SHA changed")
    expected = list(cases(root))
    if len(manifest["cases"]) != len(expected):
        raise ValueError("smoke model count changed")
    for info, (label, base, expr) in zip(manifest["cases"], expected):
        target = f.derived_model(base, expr)
        if info != {"case":label, "source_name":base["name"],
                    "target_name":target["name"], "expression":expr,
                    "kernel_verified":False}:
            raise ValueError("unreviewed smoke model changed")
        path = output / label
        if pf.audit(path / "proof") != 0:
            raise ValueError("finite-model proof failed")
        f.audit_semantics(path, head, base, expr, target)
    print(json.dumps({"cases": len(expected), "kernel_verified": True}))


def main():
    a = argparse.ArgumentParser(description=__doc__)
    a.add_argument("mode", choices=("generate", "audit"))
    a.add_argument("--root", required=True, type=Path)
    a.add_argument("--output", required=True, type=Path)
    a.add_argument("--head", required=True)
    args = a.parse_args()
    if args.mode == "generate":
        generate(args.root.resolve(), args.output, args.head)
    else:
        audit(args.root.resolve(), args.output, args.head)


if __name__ == "__main__":
    main()
