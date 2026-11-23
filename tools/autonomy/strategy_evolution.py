#!/usr/bin/env python3
"""Typed, proof-gated evolution of finite experimental strategies.

Candidate strategies are JSON data: a short composition of *reviewed*
mutation primitives. This does not synthesize/execute Python or change main.
Each experiment Lean-certifies BOTH the original and derived finite model;
the reward is a bounded heuristic describing this particular comparison,
not a general theorem about the strategy.

  prepare --root DIR --upstream FILE --state FILE --head SHA --day YYYY-MM-DD --output DIR
  receipt --root DIR --upstream FILE --state FILE --head SHA --evidence DIR --output FILE

No network, subprocess, arbitrary code eval, or file writes outside output.
"""
from __future__ import annotations

from collections import Counter
from datetime import date, timedelta
from hashlib import sha256
import argparse
import json
from pathlib import Path
import re
import sys

from tools.autonomy import finite_discovery as fd
from tools.autonomy import proof_forge as pf

SCHEMA = 1
MAX_RECEIPTS = 64
MAX_PROGRAM = 3
MAX_UPSTREAM_PARENTS = 8
MAX_CHILD_PARENTS = 16
MAX_CANDIDATES = 800
PROGRAM_OPS = (
    "bisimulation_quotient",
    "compose_first_action",
    "forget_last_observation",
    "remove_last_action",
    "split_hidden_readout",
    "append_distinguishing_probe",
    "duplicate_hidden_sheet",
    "perturb_one_transition",
    "change_observer_pair",
    "adjoin_absorbing_state",
)
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
STRATEGY_ID = re.compile(r"rule_[0-9a-f]{16}\Z")
STATE_KEYS = {"schema_version", "catalog_sha256", "last_utc_day", "receipts"}
RECEIPT_KEYS = {
    "id", "day", "head_sha", "catalog_sha256", "upstream_sha256",
    "source_id", "source_chain_sha256", "root_model",
    "root_fingerprint", "parent_rule", "program", "model",
    "model_fingerprint", "root_request_sha256", "request_sha256",
    "root_lean_sha256", "lean_sha256", "root_kind", "root_word",
    "outcome", "word", "objective", "reward", "status",
    "previous_sha256", "chain_sha256",
}
STATUS = "LEAN_VERIFIED_FINITE_PAIR_COMPARISON_ONLY"


def require(test, message):
    if not test:
        raise ValueError(message)


def canonical(obj):
    return json.dumps(obj, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":")).encode("utf-8")


def digest(obj):
    return sha256(canonical(obj)).hexdigest()


def load(path):
    require(path.is_file() and not path.is_symlink(),
            "missing non-symlink data file")
    require(path.stat().st_size <= 550_000, "data file size bound exceeded")
    return json.loads(path.read_text("utf-8"),
                      object_pairs_hook=pf.object_no_duplicates)


def save(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, ensure_ascii=False, sort_keys=True,
                               indent=2) + "\n", encoding="utf-8")


def day_check(day):
    require(type(day) is str and bool(re.fullmatch(r"\d{4}-\d{2}-\d{2}", day)),
            "invalid UTC day format")
    require(date.fromisoformat(day).isoformat() == day, "invalid calendar day")
    return day


def empty_state():
    return {"schema_version": SCHEMA, "catalog_sha256": None,
            "last_utc_day": None, "receipts": []}


def validate_program(program):
    require(type(program) is list and 1 <= len(program) <= MAX_PROGRAM,
            "strategy length out of bounds")
    require(all(type(op) is str and op in PROGRAM_OPS for op in program),
            "strategy contains an unreviewed executable primitive")
    return program


def solve_checked(model):
    fd.validate_model(model)
    answer = pf.solve(model)
    pf.validate_result(model, answer)
    return answer


def apply_program(root_model, program):
    """Interpret typed data, never run scripts or dynamically load operators."""
    validate_program(program)
    current = fd.validate_model(root_model)
    for op in program:
        current_result = solve_checked(current)
        options = dict(fd.mutate(current, current_result["kind"]))
        require(op in options, "program operation unavailable on this model")
        next_model = fd.rename_model(options[op])
        fd.validate_model(next_model)
        require(fd.model_fingerprint(next_model) != fd.model_fingerprint(current),
                "identity grammar step rejected")
        current = next_model
    return current


def score_models(root_model, derived_model):
    """Small finite empirical utility, *not* an assertion about all models."""
    old, new = solve_checked(root_model), solve_checked(derived_model)
    if old["kind"] != new["kind"]:
        return 12, "PAIR_DISTINGUISHABILITY_FLIPPED"
    if old["kind"] == "DISTINGUISHABLE":
        a, b = len(old["word"]), len(new["word"])
        if a != b:
            return 6 + min(4, abs(a - b)), "MINIMUM_NAMED_WORD_DEPTH_CHANGED"
    if len(root_model["observations"]) != len(derived_model["observations"]):
        return 3, "STATE_SPACE_SIZE_CHANGED"
    if len(root_model["transitions"]) != len(derived_model["transitions"]):
        return 2, "ACTION_VOCABULARY_CHANGED_NO_PAIR_FLIP"
    if old["kind"] == "EQUIVALENT":
        return 1, "PAIR_EQUIVALENCE_PRESERVED_IN_FINITE_MODEL"
    return 1, "PAIR_DISTINCTION_PRESERVED_IN_FINITE_MODEL"


def strategy_id(source_id, program, root_fp):
    return "rule_" + digest({"source": source_id,
                             "program": program,
                             "root_fingerprint": root_fp})[:16]


def roots(root, upstream):
    """Four exact reviewed seeds plus up to eight actual Lean-verified models."""
    catalog, reviewed = fd.seeds(root)
    items = [
        {"source_id": "reviewed:" + record["seed"],
         "source_chain_sha256": digest(record),
         "root_model": record["model"]}
        for record in reviewed
    ]
    for receipt in upstream["receipts"][-MAX_UPSTREAM_PARENTS:]:
        items.append({
            "source_id": "finite-discovery:" + receipt["name"],
            "source_chain_sha256": receipt["chain_sha256"],
            "root_model": receipt["model"],
        })
    for item in items:
        fd.validate_model(item["root_model"])
    return catalog, items


def validate_upstream(root, upstream):
    fd.validate_state(root, upstream)
    return digest(upstream)


def validate_state(root, state):
    require(type(state) is dict and set(state) == STATE_KEYS,
            "invalid strategy ledger keys")
    require(type(state["schema_version"]) is int and
            state["schema_version"] == SCHEMA, "invalid strategy schema")
    require(type(state["receipts"]) is list and
            len(state["receipts"]) <= MAX_RECEIPTS, "strategy ledger over bound")
    catalog, _ = fd.seeds(root)
    if not state["receipts"]:
        require(state["catalog_sha256"] is None and
                state["last_utc_day"] is None, "empty ledger must be empty")
        return state
    require(state["catalog_sha256"] == catalog, "reviewed source catalog mismatch")
    used_ids, previous_hash, last_date = {}, "0" * 64, None
    for receipt in state["receipts"]:
        require(type(receipt) is dict and set(receipt) == RECEIPT_KEYS,
                "malformed verified rule receipt")
        name = receipt["id"]
        require(type(name) is str and STRATEGY_ID.fullmatch(name),
                "invalid strategy id")
        require(name not in used_ids, "duplicate strategy id")
        require(type(receipt["source_id"]) is str and
                0 < len(receipt["source_id"]) <= 100, "invalid source id")
        require(type(receipt["program"]) is list, "invalid strategy program")
        validate_program(receipt["program"])
        root_model = fd.validate_model(receipt["root_model"])
        target_model = fd.validate_model(receipt["model"])
        root_fp = fd.model_fingerprint(root_model)
        require(receipt["root_fingerprint"] == root_fp and
                receipt["model_fingerprint"] == fd.model_fingerprint(target_model),
                "model fingerprint mismatch")
        require(name == strategy_id(receipt["source_id"], receipt["program"], root_fp),
                "strategy identity was modified")
        require(target_model == apply_program(root_model, receipt["program"]),
                "strategy is not the declared finite composition")
        parent = receipt["parent_rule"]
        if parent is None:
            require(len(receipt["program"]) == 1, "unparented composite strategy")
        else:
            require(parent in used_ids and len(receipt["program"]) > 1,
                    "missing verified parent strategy")
            inherited = used_ids[parent]
            require(receipt["program"][:-1] == inherited["program"] and
                    receipt["source_id"] == inherited["source_id"] and
                    root_model == inherited["root_model"] and
                    receipt["source_chain_sha256"] == inherited["source_chain_sha256"],
                    "strategy program does not extend its proven parent")
        old, new = solve_checked(root_model), solve_checked(target_model)
        score, objective = score_models(root_model, target_model)
        require(receipt["root_kind"] == old["kind"] and
                receipt["root_word"] == old.get("word") and
                receipt["outcome"] == new["kind"] and
                receipt["word"] == new.get("word") and
                receipt["reward"] == score and
                receipt["objective"] == objective,
                "finite model outcome/utility inconsistent")
        require(receipt["status"] == STATUS, "unverified strategy in ledger")
        day_check(receipt["day"])
        require(last_date is None or receipt["day"] > last_date,
                "receipt days not strictly increasing")
        last_date = receipt["day"]
        require(type(receipt["head_sha"]) is str and
                pf.HEAD.fullmatch(receipt["head_sha"]), "invalid head SHA")
        for key in ("catalog_sha256", "upstream_sha256", "source_chain_sha256",
                    "root_request_sha256", "request_sha256",
                    "root_lean_sha256", "lean_sha256", "previous_sha256",
                    "chain_sha256"):
            require(type(receipt[key]) is str and HEX64.fullmatch(receipt[key]),
                    "missing or invalid verification SHA")
        require(receipt["catalog_sha256"] == catalog and
                receipt["previous_sha256"] == previous_hash,
                "strategy chain/history mismatch")
        body = {k: v for k, v in receipt.items() if k != "chain_sha256"}
        require(receipt["chain_sha256"] == digest(body),
                "strategy receipt hash chain corrupted")
        previous_hash = receipt["chain_sha256"]
        used_ids[name] = receipt
    require(state["last_utc_day"] == last_date, "latest verified day mismatch")
    return state


def gather_candidates(root, upstream, state):
    catalog, active_roots = roots(root, upstream)
    used_ids = {r["id"] for r in state["receipts"]}
    used_models = {r["model_fingerprint"] for r in state["receipts"]}
    op_stats = {}
    for op in PROGRAM_OPS:
        matching = [r["reward"] for r in state["receipts"]
                    if r["program"][-1] == op]
        op_stats[op] = (len(matching), sum(matching))
    source_stats = Counter(r["source_id"] for r in state["receipts"])
    pool, offered = [], set()

    def attempt(source_id, source_chain, root_model, program, parent):
        if len(pool) >= MAX_CANDIDATES:
            return
        try:
            final_model = apply_program(root_model, program)
        except ValueError:
            return
        fp = fd.model_fingerprint(final_model)
        identity = strategy_id(source_id, program, fd.model_fingerprint(root_model))
        if identity in used_ids or fp in used_models or fp in offered or (
            fp == fd.model_fingerprint(root_model)
        ):
            return
        offered.add(fp)
        reward, goal = score_models(root_model, final_model)
        count, total = op_stats[program[-1]]
        # Verified policy feedback changes rankings; exploration remains
        # attractive for a mutation primitive not yet tested.
        learned = total // count if count else 0
        explore = 3 if count == 0 else (1 if count < 3 else 0)
        rank = (
            -(reward * 4 + learned + explore),
            source_stats[source_id],
            len(program),
            source_id, tuple(program), identity,
        )
        pool.append((rank, {
            "id": identity, "source_id": source_id,
            "source_chain_sha256": source_chain, "root_model": root_model,
            "root_fingerprint": fd.model_fingerprint(root_model),
            "program": program, "parent_rule": parent,
            "model": final_model, "model_fingerprint": fp,
            "objective": goal, "preview_reward": reward,
        }))

    for record in active_roots:
        model = record["root_model"]
        options = dict(fd.mutate(model, solve_checked(model)["kind"]))
        for op in PROGRAM_OPS:
            if op in options:
                attempt(record["source_id"], record["source_chain_sha256"],
                        model, [op], None)
    # Generate NEW RULES by extending *certified* earlier programs. No
    # composite program is admitted without a real verified parent.
    for r in state["receipts"][-MAX_CHILD_PARENTS:]:
        if len(r["program"]) >= MAX_PROGRAM:
            continue
        final = r["model"]
        options = dict(fd.mutate(final, solve_checked(final)["kind"]))
        for op in PROGRAM_OPS:
            if op in options:
                attempt(r["source_id"], r["source_chain_sha256"],
                        r["root_model"], r["program"]+[op], r["id"])
    if not pool:
        return None, catalog
    return min(pool, key=lambda item: item[0])[1], catalog


def plan(root, upstream, state, head, day):
    require(type(head) is str and pf.HEAD.fullmatch(head),
            "an exact checkout commit SHA is required")
    day_check(day)
    validate_upstream(root, upstream)
    validate_state(root, state)
    if state["last_utc_day"] is not None:
        require(day >= state["last_utc_day"], "UTC date precedes last verified day")
    if state["last_utc_day"] == day:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "ALREADY_VERIFIED_TODAY", "head_sha": head,
                "day": day}
    if len(state["receipts"]) >= MAX_RECEIPTS:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "VERIFIED_STRATEGY_BUDGET_EXHAUSTED",
                "head_sha": head, "day": day}
    chosen, catalog = gather_candidates(root, upstream, state)
    if chosen is None:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "TYPED_STRATEGY_SPACE_EXHAUSTED",
                "head_sha": head, "day": day}
    root_result = solve_checked(chosen["root_model"])
    derived_result = solve_checked(chosen["model"])
    return {
        "schema_version": SCHEMA, "candidate": True,
        "head_sha": head, "day": day, "catalog_sha256": catalog,
        "upstream_sha256": digest(upstream),
        **chosen,
        "root_python_observation": root_result,
        "python_observation": derived_result,
        "proof_status": "PENDING_KERNEL_VERIFICATION",
        "scope": "TWO_CONCRETE_FINITE_MODELS_NOT_UNIVERSAL_MUTATION_THEOREM",
    }


def prepare(root, upstream_file, state_file, head, day, output):
    upstream, state = load(upstream_file), load(state_file)
    require(not output.exists() or not any(output.iterdir()),
            "evidence output must start empty")
    selected = plan(root, upstream, state, head, day)
    output.mkdir(parents=True, exist_ok=True)
    if selected["candidate"]:
        req = output / "requests"
        req.mkdir()
        for model in (selected["root_model"], selected["model"]):
            path = req / (model["name"] + ".json")
            save(path, model)
            require(pf.read_request(path) == model,
                    "generated model rejected by Proof Forge")
        pf.generate(req, output / "proof", head)
    save(output / "plan.json", selected)
    print(json.dumps({"candidate": selected["candidate"],
                      "strategy": selected.get("id"),
                      "program": selected.get("program"),
                      "preview_reward": selected.get("preview_reward"),
                      "status": "UNVERIFIED_CANDIDATE" if selected["candidate"]
                      else selected["reason"]}))
    return selected


def receipt(root, upstream_file, state_file, head, evidence, output):
    upstream, state = load(upstream_file), load(state_file)
    submitted = load(evidence / "plan.json")
    require(submitted.get("candidate") is True, "no strategy candidate available")
    expected = plan(root, upstream, state, head, submitted.get("day"))
    require(submitted == expected and expected["candidate"],
            "stale or altered strategy plan; restart with current state")
    require(pf.audit(evidence / "proof") == 0,
            "Lean kernel or axiom evidence not verified")
    root_model, model = expected["root_model"], expected["model"]
    names = sorted([root_model["name"], model["name"]])
    manifest = load(evidence / "proof/manifest.json")
    require(manifest.get("passed") is True and
            manifest.get("checkout_sha") == head and
            manifest.get("models") == names,
            "both exact-head finite certificates are required")
    records = {}
    for m in (root_model, model):
        name = m["name"]
        file = evidence / "requests" / (name+".json")
        require(pf.read_request(file) == m,
                "source model differs from deterministic reviewed strategy")
        result = solve_checked(m)
        expected_source, theorem_names = pf.lean_source(m, result)
        src = evidence / "proof" / (name+".lean")
        require(src.is_file() and not src.is_symlink() and
                src.read_bytes() == expected_source.encode("utf-8"),
                "generated Lean bytes differ from reviewed generator")
        report = load(evidence / "proof" / (name+".json"))
        require(report.get("model") == name and report.get("checkout_sha") == head
                and report.get("status") == "LEAN_VERIFIED" and
                report.get("kernel_verified") is True and
                report.get("axiom_audit", {}).get("passed") is True
                and report.get("theorems") == theorem_names
                and report.get("python_result") == result
                and report.get("request_sha256") == sha256(file.read_bytes()).hexdigest()
                and report.get("generated_lean_sha256") == sha256(src.read_bytes()).hexdigest(),
                "certificate does not bind verified theorem to this finite model")
        exit_file = evidence / "proof" / (name+".exit")
        require(exit_file.is_file() and exit_file.read_text("utf-8").strip() == "0",
                "Lean compilation returned a nonzero exit code")
        records[name] = report
    previous = state["receipts"][-1]["chain_sha256"] if state["receipts"] else "0"*64
    old, new = solve_checked(root_model), solve_checked(model)
    score, objective = score_models(root_model, model)
    candidate = {
        "id": expected["id"], "day": expected["day"],
        "head_sha": head, "catalog_sha256": expected["catalog_sha256"],
        "upstream_sha256": expected["upstream_sha256"],
        "source_id": expected["source_id"],
        "source_chain_sha256": expected["source_chain_sha256"],
        "root_model": root_model,
        "root_fingerprint": expected["root_fingerprint"],
        "parent_rule": expected["parent_rule"],
        "program": expected["program"], "model": model,
        "model_fingerprint": expected["model_fingerprint"],
        "root_request_sha256": records[root_model["name"]]["request_sha256"],
        "request_sha256": records[model["name"]]["request_sha256"],
        "root_lean_sha256": records[root_model["name"]]["generated_lean_sha256"],
        "lean_sha256": records[model["name"]]["generated_lean_sha256"],
        "root_kind": old["kind"], "root_word": old.get("word"),
        "outcome": new["kind"], "word": new.get("word"),
        "objective": objective, "reward": score,
        "status": STATUS, "previous_sha256": previous,
    }
    candidate["chain_sha256"] = digest(candidate)
    state["receipts"].append(candidate)
    state["catalog_sha256"] = expected["catalog_sha256"]
    state["last_utc_day"] = expected["day"]
    validate_state(root, state)
    save(output, state)
    future = (date.fromisoformat(expected["day"]) + timedelta(days=1)).isoformat()
    next_plan = plan(root, upstream, state, head, future)
    print(json.dumps({"verified_strategy": candidate["id"],
                      "program": candidate["program"],
                      "reward": candidate["reward"],
                      "objective": objective,
                      "total": len(state["receipts"]),
                      "next_strategy": next_plan.get("id"),
                      "next_rule_length": len(next_plan.get("program", []))}))
    return candidate


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_subparsers(dest="mode", required=True)
    for command in ("prepare", "receipt"):
        p = modes.add_parser(command)
        p.add_argument("--root", required=True, type=Path)
        p.add_argument("--upstream", required=True, type=Path)
        p.add_argument("--state", required=True, type=Path)
        p.add_argument("--head", required=True)
        p.add_argument("--output", required=True, type=Path)
        if command == "prepare":
            p.add_argument("--day", required=True)
        else:
            p.add_argument("--evidence", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        if args.mode == "prepare":
            prepare(args.root.resolve(), args.upstream, args.state,
                    args.head, args.day, args.output)
        else:
            receipt(args.root.resolve(), args.upstream, args.state,
                    args.head, args.evidence, args.output)
    except (ValueError, OSError, TypeError, KeyError,
            UnicodeError, json.JSONDecodeError) as exc:
        print("STRATEGY_EVOLUTION_FAIL_CLOSED:", str(exc), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
