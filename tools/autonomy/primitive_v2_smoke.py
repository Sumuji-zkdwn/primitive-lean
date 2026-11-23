#!/usr/bin/env python3
"""Replay fixed delayed-separation and inert-control Lean smoke obligations."""
from __future__ import annotations

import argparse
from pathlib import Path

from tools.autonomy import primitive_v2 as v2
from tools.autonomy import proof_forge as pf

SPECS = (
    {"family": "delayed_split", "states": 5, "depth": 2},
    {"family": "inert_swap", "states": 3},
)


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--head", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args(argv)
    requests = args.output / "requests"
    if args.output.exists() and any(args.output.iterdir()):
        raise ValueError("smoke output must be empty")
    requests.mkdir(parents=True, exist_ok=False)
    for spec in SPECS:
        base, extended, _, _ = v2.model_pair(spec)
        for model in (base, extended):
            (requests / (model["name"] + ".json")).write_bytes(
                v2.request_bytes(model))
    pf.generate(requests, args.output / "proof", args.head)


if __name__ == "__main__":
    main()
