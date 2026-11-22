#!/usr/bin/env python3
"""Generate bounded, provenance-anchored Lean smoke certificates for new routes.

This generator does not claim the resulting Lean files have compiled.
Only the CI trust-zero compilation and Proof Forge axiom audit may do that.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from tools.autonomy import proof_forge
from tools.autonomy import research_conveyor_routes as routes

SMOKE_TASKS = (
    "observer_macro", "observer_hidden", "observer_visible",
    "laakso_w1_stop", "laakso_w1_advance", "laakso_w2_advance",
)


def generate(root, output, head):
    if not proof_forge.HEAD.fullmatch(head):
        raise ValueError("full exact commit SHA required")
    if output.exists() and any(output.iterdir()):
        raise ValueError("smoke output must start empty")
    anchors = {name: routes.source_anchor(root, name)
               for name in ("observer", "laakso")}
    requests = output / "requests"
    requests.mkdir(parents=True)
    for task_id in SMOKE_TASKS:
        model = routes.source_model(root, task_id)
        path = requests / (task_id + ".json")
        path.write_text(json.dumps(model, ensure_ascii=False, indent=2) + "\n",
                        encoding="utf-8")
        if proof_forge.read_request(path) != model:
            raise ValueError("generated smoke request failed schema verification")
    proof_forge.generate(requests, output / "proof", head)
    provenance = {
        "schema_version": 1,
        "kind": "FINITE_REVIEWED_ADAPTER_SMOKE_NOT_A_LEAN_PROOF",
        "checkout_sha": head,
        "reviewed_anchors": anchors,
        "models": list(SMOKE_TASKS),
        "kernel_verified": False,
    }
    (output / "provenance.json").write_text(
        json.dumps(provenance, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8")
    print(json.dumps({"models": list(SMOKE_TASKS), "kernel_verified": False}))
    return provenance


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root", type=Path, required=True)
    p.add_argument("--head", required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    generate(args.root.resolve(), args.output, args.head)


if __name__ == "__main__":
    main()
