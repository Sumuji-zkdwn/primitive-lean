"""Select and compile the standalone prime-factor proofs from the repository root."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
from typing import NamedTuple


class Probe(NamedTuple):
    stem: str
    push_branch: str
    pr_base: str
    dependencies: tuple[str, ...]
    namespace: str
    theorems: tuple[str, ...]


CESARO = "chatgpt/ternary-zero-cesaro-20261103"
OBSERVATION = "chatgpt/prime-factor-observation-20261103"
ORBITS = "chatgpt/prime-observation-orbits-20261103"
ADAPTIVE = "chatgpt/prime-factor-f0-adaptive-20261103"
COMMON = ("TernaryZeroCesaro", "FiniteObservationSeparation")
WITH_OBSERVATION = (*COMMON, "PrimeFactorObservation")
WITH_ORBITS = (*WITH_OBSERVATION, "PrimeFactorOrbits")
WITH_ADAPTIVE = (*WITH_ORBITS, "PrimeFactorF0Adaptive")

PROBES = {
    "observation": Probe(
        "PrimeFactorObservation", OBSERVATION, CESARO, COMMON,
        "LinearInputPrimeFactorObservation", (
            "product_kernel_eq_bag_kernel", "canonical_product_injective",
            "minimal_ordered_observation_count",
        ),
    ),
    "orbits": Probe(
        "PrimeFactorOrbits", ORBITS, OBSERVATION, WITH_OBSERVATION,
        "LinearInputPrimeFactorOrbits", (
            "pair_product_eq_iff_swap_orbit", "triple_product_eq_iff_orbit",
            "triple_product_eq_iff_bag", "canonical_triple_product_injective",
            "minimal_unordered_triple_observations", "minimal_ordered_triple_observations",
        ),
    ),
    "f0-adaptive": Probe(
        "PrimeFactorF0Adaptive", ADAPTIVE, ORBITS, WITH_ORBITS,
        "LinearInputPrimeFactorF0", (
            "normalize_idempotent", "product_kernel_eq_normalize_kernel",
            "normalize_kernel_eq_orbit", "normalize_fixed_point_count",
            "factors_through_normalize_iff", "adaptive_two_not_injective",
        ),
    ),
    "general-f0": Probe(
        "PrimeFactorGeneralF0", "chatgpt/general-prime-f0-normalization-20261103",
        ADAPTIVE, WITH_ADAPTIVE, "LinearInputPrimeFactorGeneralF0", (
            "normalize_idempotent", "normalize_eq_iff_perm", "normalize_preserves_product",
            "factors_through_normalize_iff", "prime_product_eq_iff_perm",
            "prime_product_kernel_eq_normalize_kernel", "prime_product_invariant_of_normalize",
        ),
    ),
    "general-length": Probe(
        "PrimeFactorFiniteLength", "chatgpt/general-prime-probe-minimality-20261103",
        ADAPTIVE, WITH_ADAPTIVE, "LinearInputPrimeFactorFiniteLength", (
            "prefix_product_pos", "full_library_separates", "bumped_prefix_swap_product",
            "missing_probe_witness", "separates_iff_univ", "minimal_distinct_probe_count",
            "minimal_list_observation_count", "unordered_factor_multiset_count",
        ),
    ),
}

SHARED_PATHS = {
    ".github/workflows/prime-factor-probes.yml",
    ".github/scripts/prime_factor_probes.py",
    ".github/scripts/test_prime_factor_probes.py",
}
FRAGMENTS = Path("linear_input/lean_check")


def changed_paths(event_name, event):
    if event_name == "pull_request":
        pr = event["pull_request"]
        revisions = [f"{pr['base']['sha']}...{pr['head']['sha']}"]
    else:
        before = event["before"]
        if event.get("size", len(event.get("commits", []))) > 1000:
            return None  # GitHub bypasses path filters for large pushes.
        if before == "0" * 40:
            commits = event.get("commits", [])
            if not commits:
                return None  # The new ref has no comparison base in the payload.
            parents = subprocess.check_output(
                ["git", "show", "-s", "--format=%P", commits[0]["id"]], text=True
            ).split()
            before = parents[0] if parents else subprocess.check_output(
                ["git", "hash-object", "-t", "tree", "--stdin"], input="", text=True
            ).strip()
        elif subprocess.run(["git", "cat-file", "-e", before], stderr=subprocess.DEVNULL).returncode:
            # A force push can orphan the comparison base outside the fetched refs.
            if subprocess.run(["git", "fetch", "--no-tags", "--depth=1", "origin", before]).returncode:
                print("Push base unavailable; checking all probes for this branch.", file=sys.stderr)
                return None
        revisions = [before, event["after"]]

    paths = subprocess.check_output(["git", "diff", "--no-renames", "--name-only", "-z", *revisions, "--"])
    return {os.fsdecode(path) for path in paths.split(b"\0") if path}


def select(event_name, event):
    if event_name == "workflow_dispatch":
        choice = event["inputs"]["probe"]
        if choice == "all":
            return list(PROBES)
        if choice not in PROBES:
            raise ValueError(f"Unknown probe: {choice}")
        return [choice]

    if event_name == "push":
        if event.get("deleted"):
            return []
        branch = event["ref"].removeprefix("refs/heads/")
        candidates = {key: p for key, p in PROBES.items() if p.push_branch == branch}
    elif event_name == "pull_request":
        branch = event["pull_request"]["base"]["ref"]
        candidates = {key: p for key, p in PROBES.items() if p.pr_base == branch}
    else:
        raise ValueError(f"Unsupported event: {event_name}")

    paths = changed_paths(event_name, event)
    if event_name == "pull_request" and branch == "main":
        return list(PROBES) if SHARED_PATHS.intersection(paths) else []
    if paths is None or SHARED_PATHS.intersection(paths):
        return list(candidates)
    return [
        key for key, probe in candidates.items()
        if (FRAGMENTS / f"{probe.stem}.inc").as_posix() in paths
    ]


def assemble(probe):
    fragment = (FRAGMENTS / f"{probe.stem}.inc").read_text(encoding="utf-8")
    for token in ("sorry", "admit", "axiom", "unsafe", "native_decide"):
        if token in fragment:
            raise ValueError(f"Forbidden Lean token in {probe.stem}: {token}")
    sources = [(FRAGMENTS / f"{name}.inc").read_text(encoding="utf-8") for name in probe.dependencies]
    sources.append(fragment)
    checks = [f"#print axioms {probe.namespace}.{name}" for name in probe.theorems]
    source = "import Mathlib\n\n" + "\n\n".join(sources) + "\n" + "\n".join(checks) + "\n"
    output = Path("lean", f"{probe.stem}Probe.lean")
    output.write_text(source, encoding="utf-8")
    return output


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("select")
    commands.add_parser("prove").add_argument("probe", choices=PROBES)
    args = parser.parse_args()
    if args.command == "select":
        event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text(encoding="utf-8"))
        print("probes=" + json.dumps(select(os.environ["GITHUB_EVENT_NAME"], event)))
    else:
        proof = assemble(PROBES[args.probe])
        subprocess.run(["lake", "env", "lean", "--trust=0", proof.name], cwd=proof.parent, check=True)
