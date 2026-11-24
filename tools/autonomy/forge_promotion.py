#!/usr/bin/env python3
"""Production acceptance of bounded, independently replayed cross-forge operators.

The original Generic ledger is the only write target. A reviewed typed meta
rule can become a generation edge, never a new interpreter or executable.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from tools.autonomy import generic_forge as gf
from tools.autonomy import meta_forge as mf
from tools.autonomy import forge_bridge as fb


def validate_inputs(state, meta):
    gf.validate_state(state)
    mf.validate_state(meta)
    previous = state.get("meta_snapshot")
    if previous is not None:
        prior = previous["rules"]
        gf.require(meta["rules"][:len(prior)] == prior,
                   "upstream meta ledger is not an extension of accepted ancestry")


def plan(state, meta, day, head):
    gf.check_day(day)
    gf.require(type(head) is str and gf.HEAD40.fullmatch(head), "exact source SHA required")
    validate_inputs(state, meta)
    gf.require(state["last_utc_day"] is None or day >= state["last_utc_day"],
               "clock moved backwards")
    # Alternate opportunities by count: ordinary composition remains live.
    # All no-candidate, duplicate-slot and cap semantics remain those of Generic.
    if (len(state["receipts"]) % 2 == 1
            and len(state["receipts"]) < gf.MAX_RECORDS
            and state["last_utc_day"] != day):
        eligible = [r for r in meta["rules"] if r["day"] <= day]
        result = fb.one_round(state["receipts"], eligible, 1)
        chosen = result["selected"]
        if chosen is not None:
            left = "m:" + chosen["seed_id"]
            right = "r:" + chosen["rule_id"]
            domain, program, behavior = chosen["domain"], chosen["program"], chosen["behavior"]
            operator = {"id": gf.make_id(domain, left, right, program),
                        "domain": domain, "left": left, "right": right,
                        "program": program, "behavior": behavior,
                        "score": gf.score_candidate(domain, left, right, program,
                                                    behavior, state["receipts"]),
                        "origin": {"kind": "verified_meta_rule_v1",
                                   "rule_id": chosen["rule_id"],
                                   "rule_chain_sha256": chosen["rule_chain_sha256"]}}
            return {"schema_version": gf.SCHEMA, "day": day, "head_sha": head,
                    "candidate": True, "operator": operator,
                    "status": "CANDIDATE_AWAITING_INDEPENDENT_VERIFICATION",
                    "candidates_checked": result["examined"],
                    "outside_pair_frontier": result["distinct_outside_pair_frontier"],
                    "route": "meta_rule",
                    "generic_state_sha256": gf.digest(state),
                    "meta_state_sha256": gf.digest(meta)}
    ordinary = gf.plan(state, day, head)
    return {**ordinary, "route": "composition",
            "generic_state_sha256": gf.digest(state),
            "meta_state_sha256": gf.digest(meta)}


def accept(state, meta, presented, head):
    expected = plan(state, meta, presented["day"], head)
    gf.require(expected == presented and expected["candidate"] is True,
               "stale or altered cross-forge plan")
    entry = expected["operator"]
    gf.require(gf.audit(entry["domain"], tuple(entry["program"])) == entry["behavior"],
               "full-domain operator verification failed")
    row = {**entry, "day": expected["day"], "head_sha": head,
           "status": gf.STATUS, "evaluator": gf.EVALUATOR,
           "previous_sha256": (state["receipts"][-1]["chain_sha256"]
                               if state["receipts"] else gf.ZERO)}
    row["chain_sha256"] = gf.digest(row)
    updated = {**state, "last_utc_day": expected["day"],
               "receipts": state["receipts"] + [row]}
    if expected["route"] == "meta_rule":
        updated["meta_snapshot"] = meta
    gf.validate_state(updated)
    gf.require(len(gf.canonical(updated)) < 300_000, "compact state size budget exceeded")
    # Check pretty-printed on-disk bound before writing.
    gf.require(len((json.dumps(updated, sort_keys=True, ensure_ascii=False, indent=2)
                    + "\n").encode("utf-8")) <= 500_000, "state file budget exceeded")
    return updated


def main(argv=None):
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("command", choices=("prepare", "receipt"))
    cli.add_argument("--state", required=True, type=Path)
    cli.add_argument("--meta-state", required=True, type=Path)
    cli.add_argument("--head", required=True)
    cli.add_argument("--day")
    cli.add_argument("--output", required=True, type=Path)
    cli.add_argument("--evidence", type=Path)
    args = cli.parse_args(argv)
    state, meta = gf.read(args.state), mf.load(args.meta_state)
    if args.command == "prepare":
        gf.require(args.day is not None, "day required")
        gf.require(not args.output.exists() or not any(args.output.iterdir()),
                   "output folder must be empty")
        result = plan(state, meta, args.day, args.head)
        gf.save(args.output / "plan.json", result)
        print(json.dumps({"candidate": result["candidate"], "route": result["route"],
                          "id": result.get("operator", {}).get("id"),
                          "outside_pair_frontier": result.get("outside_pair_frontier")}))
    else:
        gf.require(args.evidence is not None, "evidence required")
        presented = gf.read(args.evidence / "plan.json")
        result = accept(state, meta, presented, args.head)
        gf.save(args.output, result)
        print(json.dumps({"certified": result["receipts"][-1]["id"],
                          "route": presented["route"], "saved": len(result["receipts"])}))


if __name__ == "__main__":
    main()
