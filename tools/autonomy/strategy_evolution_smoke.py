#!/usr/bin/env python3
"""Independently compile representative typed strategy programs with Lean.

Output is unverified until the calling CI job runs pinned --trust=0 and audits.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from tools.autonomy import finite_discovery as fd
from tools.autonomy import proof_forge as pf
from tools.autonomy import strategy_evolution as meta


def generate(root, output, head):
    if not pf.HEAD.fullmatch(head):
        raise ValueError("exact commit SHA required")
    if output.exists() and any(output.iterdir()):
        raise ValueError("output directory must be empty")
    _, reviewed = fd.seeds(root)
    base = {r["seed"]: r["model"] for r in reviewed}
    cases = [
        ("observer", ["compose_first_action"]),
        ("observer", ["compose_first_action", "forget_last_observation"]),
        ("observer_hidden", ["split_hidden_readout"]),
        ("observer_hidden", ["bisimulation_quotient"]),
        ("siphon", ["append_distinguishing_probe"]),
        ("laakso", ["remove_last_action"]),
    ]
    models, names = [], set()
    for family, program in cases:
        m = meta.apply_program(base[family], program)
        if m["name"] in names:
            raise ValueError("smoke experiment duplicate model")
        names.add(m["name"])
        models.append({"domain": family, "program": program, "model": m})
    req = output / "requests"
    req.mkdir(parents=True)
    for item in models:
        meta.save(req / (item["model"]["name"]+".json"), item["model"])
        pf.read_request(req / (item["model"]["name"]+".json"))
    pf.generate(req, output / "proof", head)
    meta.save(output / "provenance.json", {
        "source": "typed_composition_of_reviewed_finite_mutations",
        "checkout_sha": head, "programs": [
            {"domain": item["domain"], "program": item["program"],
             "model": item["model"]["name"]} for item in models
        ],
        "scope": "FINITE_MODEL_ONLY",
        "kernel_verified": False,
    })
    print(json.dumps({"smoke_models": len(models),
                      "names": sorted(names), "kernel_verified": False}))


def main():
    a = argparse.ArgumentParser()
    a.add_argument("--root", type=Path, required=True)
    a.add_argument("--output", type=Path, required=True)
    a.add_argument("--head", required=True)
    p = a.parse_args()
    generate(p.root.resolve(), p.output, p.head)


if __name__ == "__main__":
    main()
