#!/usr/bin/env python3
"""Read-only cross-forge experiment: verified rules act on verified macros.

Measure exact finite behavior outside the ordinary pair-composition frontier.
Retain an auditable, bounded shadow lineage; never write either live ledger.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

from tools.autonomy import generic_forge as gf
from tools.autonomy import meta_forge as mf

MAX_ROUNDS = 3
MAX_RULES = 8
MAX_SEEDS_PER_DOMAIN = 6
MAX_CANDIDATES_PER_ROUND = len(gf.DOMAINS) * MAX_RULES * MAX_SEEDS_PER_DOMAIN
EVALUATOR = "forge-bridge-v1-finite-shadow"
CAPACITY_ERROR = "generated program exceeds finite interpreter capacity"


def pair_frontier(domain, history):
    """All behavior fingerprints of the ordinary current bounded pair search."""
    tokens = gf.primitive_tokens(domain) + gf.verified_tokens(domain, history)
    programs = {tuple(a + b) for _, a in tokens for _, b in tokens
                if len(a) + len(b) <= gf.MAX_PROGRAM}
    return {gf.audit(domain, program)["fingerprint"] for program in sorted(programs)}


def checked_rewrite(domain, rule, program):
    """Only a matching, expected capacity rejection may be skipped."""
    results = []
    for interpreter in (mf.rewrite_reference, mf.rewrite_independent):
        try:
            results.append(interpreter(domain, rule, program))
        except ValueError as exc:
            if str(exc) != CAPACITY_ERROR:
                raise
            results.append(None)
    gf.require(results[0] == results[1], "independent rewrite disagreement")
    return results[0]


def one_round(history, rules, index):
    seen = {(r["domain"], r["behavior"]["fingerprint"]) for r in history}
    counts = Counter(r["domain"] for r in history)
    frontiers = {d: pair_frontier(d, history) for d in gf.DOMAINS}
    candidates = {}
    examined = rejected_capacity = rejected_known = rejected_pair = 0
    for domain in gf.DOMAINS:
        seeds = [r for r in history if r["domain"] == domain][-MAX_SEEDS_PER_DOMAIN:]
        for seed in seeds:
            for rule in rules[-MAX_RULES:]:
                examined += 1
                program = checked_rewrite(domain, rule["steps"], seed["program"])
                if program is None:
                    rejected_capacity += 1
                    continue
                behavior = gf.audit(domain, tuple(program))
                fp = (domain, behavior["fingerprint"])
                if fp in seen or behavior["changed_inputs"] == 0:
                    rejected_known += 1
                    continue
                if fp[1] in frontiers[domain]:
                    rejected_pair += 1
                    continue
                # Novelty is behavioral, not syntactic. Prefer balanced domains,
                # reuse of shadow results, varied outputs, then shorter programs.
                rank = (counts[domain], -int(seed["id"].startswith("fb_")),
                        -behavior["distinct_outputs"], len(program),
                        domain, rule["id"], seed["id"])
                row = {"domain": domain, "program": program, "behavior": behavior,
                       "seed_id": seed["id"], "rule_id": rule["id"],
                       "seed_program": seed["program"], "rule_steps": rule["steps"],
                       "rule_chain_sha256": rule["chain_sha256"],
                       "round": index, "status": "EXHAUSTIVELY_CHECKED_SHADOW_OPERATOR"}
                row["id"] = "fb_" + gf.digest(row)[:16]
                if fp not in candidates or rank < candidates[fp][0]:
                    candidates[fp] = (rank, row)
    gf.require(examined <= MAX_CANDIDATES_PER_ROUND, "candidate budget exceeded")
    selected = min(candidates.values(), key=lambda x: x[0])[1] if candidates else None
    return {"round": index, "examined": examined, "capacity_rejections": rejected_capacity,
            "known_or_identity_rejections": rejected_known,
            "ordinary_pair_rejections": rejected_pair,
            "distinct_outside_pair_frontier": len(candidates),
            "pair_frontier_sizes": {d: len(fps) for d, fps in frontiers.items()},
            "selected": selected}


def experiment(generic, meta, head, rounds=MAX_ROUNDS):
    gf.require(type(head) is str and gf.HEAD40.fullmatch(head), "exact source SHA required")
    gf.require(type(rounds) is int and 1 <= rounds <= MAX_ROUNDS, "round budget exceeded")
    gf.validate_state(generic)
    mf.validate_state(meta)
    history = list(generic["receipts"])
    results = []
    for index in range(1, rounds + 1):
        result = one_round(history, meta["rules"], index)
        results.append(result)
        if result["selected"] is None:
            break
        history.append(result["selected"])
    return {"evaluator": EVALUATOR, "head_sha": head,
            "generic_state_sha256": gf.digest(generic), "meta_state_sha256": gf.digest(meta),
            "generic_receipts": len(generic["receipts"]), "meta_rules": len(meta["rules"]),
            "round_budget": rounds, "rounds": results,
            "shadow_operators": sum(r["selected"] is not None for r in results),
            "shadow_reentry": sum(bool(r["selected"] and r["selected"]["seed_id"].startswith("fb_"))
                                  for r in results),
            "guarantee": "Finite exhaustive comparison with the bounded pair frontier only; "
                         "not new primitive expressive power, usefulness, or a Lean theorem."}


def main(argv=None):
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("command", choices=("prepare", "verify"))
    cli.add_argument("--generic", required=True, type=Path)
    cli.add_argument("--meta", required=True, type=Path)
    cli.add_argument("--head", required=True)
    cli.add_argument("--rounds", default=MAX_ROUNDS, type=int)
    cli.add_argument("--report", required=True, type=Path)
    args = cli.parse_args(argv)
    generic, meta = gf.read(args.generic), mf.load(args.meta)
    report = experiment(generic, meta, args.head, args.rounds)
    if args.command == "prepare":
        gf.require(not args.report.exists(), "refuse to overwrite existing evidence")
        gf.save(args.report, report)
    else:
        gf.require(gf.read(args.report) == report, "report does not reproduce exactly")
    print(json.dumps({"shadow_operators": report["shadow_operators"],
                      "shadow_reentry": report["shadow_reentry"],
                      "rounds": [{"examined": r["examined"],
                                  "outside_pair_frontier": r["distinct_outside_pair_frontier"]}
                                 for r in report["rounds"]]}))


if __name__ == "__main__":
    main()
