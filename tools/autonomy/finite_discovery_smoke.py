#!/usr/bin/env python3
"""Review fixture: independently Lean-check seeds and derived hypothesis families.

The generated Lean is explicitly UNVERIFIED until Actions compiles it and
audits its axioms. This tool creates only bounded JSON/Lean data artifacts.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from tools.autonomy import finite_discovery as fd
from tools.autonomy import proof_forge as pf


def smoke(root, output, head):
    if not pf.HEAD.fullmatch(head):
        raise ValueError("exact commit SHA required")
    if output.exists() and any(output.iterdir()):
        raise ValueError("output directory must be empty")
    catalog, roots = fd.seeds(root)
    models = [r["model"] for r in roots]
    observer = roots[0]["model"]
    hidden = roots[3]["model"]
    edited = dict(fd.mutate(observer, "DISTINGUISHABLE"))
    if "compose_first_action" not in edited:
        raise ValueError("reviewed macro experiment unavailable")
    models.append(fd.rename_model(edited["compose_first_action"]))
    edited = dict(fd.mutate(hidden, "EQUIVALENT"))
    for op in ("split_hidden_readout", "bisimulation_quotient"):
        if op not in edited:
            raise ValueError("reviewed " + op + " experiment unavailable")
        models.append(fd.rename_model(edited[op]))
    names = [m["name"] for m in models]
    if len(names) != 7 or len(set(names)) != 7:
        raise ValueError("duplicate or unexpected smoke models")
    req = output / "requests"
    req.mkdir(parents=True)
    for model in models:
        fd.validate_model(model)
        fd.save(req / (model["name"] + ".json"), model)
        if pf.read_request(req / (model["name"] + ".json")) != model:
            raise ValueError("smoke model does not meet Proof Forge input schema")
    pf.generate(req, output / "proof", head)
    fd.save(output / "provenance.json", {
        "schema_version": 1,
        "scope": fd.SOURCE_SCOPE,
        "checkout_sha": head, "catalog_sha256": catalog,
        "models": names, "kernel_verified": False,
        "origin": "reviewed_seeds_and_deterministic_mutation_grammar",
    })
    return names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--head", required=True)
    args = parser.parse_args()
    names = smoke(args.root.resolve(), args.output, args.head)
    print(json.dumps({"models": names, "kernel_verified": False}))


if __name__ == "__main__":
    main()
