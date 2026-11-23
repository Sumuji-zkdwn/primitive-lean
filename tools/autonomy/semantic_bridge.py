#!/usr/bin/env python3
"""Proof-gated bridge: compose verified Generic macros with verified new semantics.

The Generic Forge and Semantic Foundry ledgers are strictly read-only data
inputs. The trusted adapter never executes code provided by a data branch.
New hybrid compositions are independently evaluated on all 256 signals.
"""
from __future__ import annotations

from datetime import date
from hashlib import sha256
import argparse
import json
from pathlib import Path
import re
import sys

from tools.autonomy import generic_forge as gf
from tools.autonomy import semantic_forge as sf

SCHEMA = 1
EVALUATOR = "semantic-bridge-v1-dual-exhaustive-composition"
STATUS = "VERIFIED_HYBRID_FINITE_SIGNAL_OPERATOR"
MAX_TOKENS = 5
MAX_RECEIPTS = 32
MAX_CANDIDATES = 200
ZERO = "0" * 64
STATE_KEYS = {"schema_version", "last_utc_day", "receipts"}
ROW_KEYS = {"id", "day", "head_sha", "parent", "recipe", "flattened",
            "source_generic", "source_semantic", "score", "behavior",
            "invariant", "evaluator", "status",
            "previous_sha256", "chain_sha256"}
HEAD40 = re.compile(r"[0-9a-f]{40}\Z")
HASH64 = re.compile(r"[0-9a-f]{64}\Z")
IDENT = re.compile(r"sb_[0-9a-f]{16}\Z")


def need(ok, reason):
    if not ok:
        raise ValueError(reason)


def canonical(obj):
    return json.dumps(obj, sort_keys=True, ensure_ascii=False,
                      separators=(",", ":")).encode("utf-8")


def digest(obj):
    return sha256(canonical(obj)).hexdigest()


def read(path):
    path = Path(path)
    need(path.is_file() and not path.is_symlink(), "missing plain JSON data")
    need(path.stat().st_size <= 550_000, "data exceeds input bound")
    return json.loads(path.read_text("utf-8"),
                      object_pairs_hook=gf.unique_json)


def write(path, item):
    path = Path(path)
    need(not path.is_symlink(), "symlink output is not allowed")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(item, sort_keys=True, ensure_ascii=False,
                               indent=2) + "\n", encoding="utf-8")


def empty_state():
    return {"schema_version": SCHEMA, "last_utc_day": None, "receipts": []}


def checked_upstream(generic, semantic):
    gf.validate_state(generic)
    sf.validate_state(semantic)
    need(generic["receipts"] and semantic["receipts"],
         "both upstream research systems require verified results")
    generic_map = {
        row["id"]: row for row in generic["receipts"]
        if row["domain"] == "signal4"
    }
    semantic_map = {row["id"]: row for row in semantic["receipts"]}
    need(generic_map and semantic_map, "no verified signal operator parent")
    return generic_map, semantic_map


def sources(generic, semantic):
    return (generic["receipts"][-1]["chain_sha256"],
            semantic["receipts"][-1]["chain_sha256"])


def validate_token(token, gmap, smap, prior, allow_bridge):
    need(type(token) is dict and set(token) == {"kind", "id"},
         "invalid typed operator token")
    kind, name = token["kind"], token["id"]
    need(type(kind) is str and type(name) is str,
         "operator token must use strings")
    if kind == "generic":
        need(name in gmap, "unverified Generic Forge macro")
    elif kind == "semantic":
        need(name in smap, "unverified Semantic Foundry operator")
    elif kind == "bridge" and allow_bridge:
        need(name in prior, "uncertified hybrid macro")
    else:
        raise ValueError("unapproved execution or token kind")
    return token


def flatten(recipe, gmap, smap, prior):
    need(type(recipe) is list and len(recipe) == 2, "hybrid recipe shape")
    output = []
    for token in recipe:
        validate_token(token, gmap, smap, prior, True)
        if token["kind"] == "bridge":
            output.extend(prior[token["id"]]["flattened"])
        else:
            output.append(token)
    need(2 <= len(output) <= MAX_TOKENS, "hybrid token limit exceeded")
    for token in output:
        validate_token(token, gmap, smap, {}, False)
    need(any(item["kind"] == "generic" for item in output) and
         any(item["kind"] == "semantic" for item in output),
         "hybrid must use both proven upstream vocabularies")
    return output


def execute_token(token, value, implementation, gmap, smap):
    if token["kind"] == "generic":
        macro = gmap[token["id"]]
        engine = (gf.reference_primitive if implementation == "readable"
                  else gf.independent_primitive)
        return gf.apply_program("signal4", macro["program"], value, engine)
    sem = smap[token["id"]]
    engine = (sf.reference_step if implementation == "readable"
              else sf.independent_step)
    return sf.apply_recipe(sem["recipe"], value, engine)


def execute(flattened, value, implementation, gmap, smap):
    v = value
    for token in flattened:
        v = execute_token(token, v, implementation, gmap, smap)
    return v


def evaluate(flattened, gmap, smap):
    """Two entirely separate interpreter paths over all 256 input signals."""
    results = []
    for value in range(256):
        a = execute(flattened, value, "readable", gmap, smap)
        b = execute(flattened, value, "packed", gmap, smap)
        need(a == b and type(a) is int and 0 <= a < 256,
             "independent hybrid interpreters disagree")
        results.append(a)
    constants = []
    for x in range(4):
        encoded = gf.encoded("signal4", [x] * 4)
        output = results[encoded]
        vals = gf.digits("signal4", output)
        if len(set(vals)) > 1:
            constants.append({"input": encoded, "output": output,
                              "input_values": [x] * 4,
                              "output_values": vals})
    bases = [results[1 << (2*i)] for i in range(4)]
    if not constants or len(set(bases)) < 4:
        return None
    table = bytes(results)
    return {
        "behavior_sha256": sha256(table).hexdigest(),
        "exhaustive_inputs": 256,
        "independent_implementations": 2,
        "changed_inputs": sum(x != y for x, y in enumerate(results)),
        "distinct_outputs": len(set(results)),
        "constant_counterexample": constants[0],
        "four_position_outputs": bases,
        "old_primitive_closure_excluded": True,
    }


def operator_id(parent, recipe, flattened):
    return "sb_" + digest({
        "parent": parent, "recipe": recipe, "flattened": flattened,
    })[:16]


def score(parent, flat, behavior):
    return ((14 if parent else 0) + 2 * min(16, behavior["distinct_outputs"])
            + min(8, behavior["changed_inputs"] // 32) - len(flat))


def suggestions(history, gmap, smap):
    """Initial compositions and later extensions from verified hybrid parents."""
    for g in gmap:
        for s in smap:
            yield None, [{"kind": "generic", "id": g},
                         {"kind": "semantic", "id": s}]
            yield None, [{"kind": "semantic", "id": s},
                         {"kind": "generic", "id": g}]
    for row in history[-8:]:
        for kind, lookup in (("generic", gmap), ("semantic", smap)):
            for ref in lookup:
                token = {"kind": kind, "id": ref}
                ancestor = {"kind": "bridge", "id": row["id"]}
                yield row["id"], [ancestor, token]
                yield row["id"], [token, ancestor]


def select(history, generic, semantic):
    gmap, smap = checked_upstream(generic, semantic)
    prior = {r["id"]: r for r in history}
    seen = {r["behavior"]["behavior_sha256"] for r in history}
    candidates = []
    examined = 0
    for parent, recipe in suggestions(history, gmap, smap):
        if examined >= MAX_CANDIDATES:
            break
        examined += 1
        try:
            flat = flatten(recipe, gmap, smap, prior)
        except ValueError as exc:
            if str(exc) == "hybrid token limit exceeded":
                continue
            raise
        behavior = evaluate(flat, gmap, smap)
        if behavior is None or behavior["behavior_sha256"] in seen:
            continue
        # A new hybrid reuses at least one verified semantic capability.
        value = score(parent, flat, behavior)
        record = {"parent": parent, "recipe": recipe, "flattened": flat,
                  "id": operator_id(parent, recipe, flat),
                  "score": value, "behavior": behavior,
                  "invariant": sf.primitive_closure_invariant()}
        key = (0 if parent else 1, -value, len(flat),
               canonical(recipe).decode("utf-8"))
        candidates.append((key, record))
    if not candidates:
        return None, examined
    candidates.sort(key=lambda v: v[0])
    return candidates[0][1], examined


def validate_state(state, generic, semantic):
    gmap, smap = checked_upstream(generic, semantic)
    need(type(state) is dict and set(state) == STATE_KEYS and
         type(state["schema_version"]) is int and state["schema_version"] == SCHEMA,
         "hybrid state schema drift")
    rows = state["receipts"]
    need(type(rows) is list and len(rows) <= MAX_RECEIPTS,
         "invalid hybrid receipt count")
    parentmap, seen, last, prev = {}, set(), None, ZERO
    gheads = {r["chain_sha256"] for r in generic["receipts"]}
    sheads = {r["chain_sha256"] for r in semantic["receipts"]}
    for row in rows:
        need(type(row) is dict and set(row) == ROW_KEYS,
             "hybrid receipt fields malformed")
        sf.day_check(row["day"])
        need(last is None or row["day"] > last,
             "hybrid history days not monotone")
        last = row["day"]
        need(type(row["head_sha"]) is str and HEAD40.fullmatch(row["head_sha"]),
             "not exact controller SHA")
        need(row["source_generic"] in gheads and row["source_semantic"] in sheads,
             "upstream proof ancestry missing")
        need(row["status"] == STATUS and row["evaluator"] == EVALUATOR,
             "self-asserted hybrid verification")
        if row["parent"] is not None:
            need(row["parent"] in parentmap, "unverified hybrid parent")
            need(any(x["kind"] == "bridge" and x["id"] == row["parent"]
                     for x in row["recipe"]), "claimed parent not used")
        else:
            need(all(x["kind"] != "bridge" for x in row["recipe"]),
                 "root recipe uses unverified bridge")
        flat = flatten(row["recipe"], gmap, smap, parentmap)
        need(flat == row["flattened"], "typed recipe expansion differs")
        need(operator_id(row["parent"], row["recipe"], flat) == row["id"]
             and IDENT.fullmatch(row["id"]) and row["id"] not in parentmap,
             "invalid hybrid operator ID")
        behavior = evaluate(flat, gmap, smap)
        need(behavior is not None and row["behavior"] == behavior and
             behavior["behavior_sha256"] not in seen,
             "hybrid behavior changed or duplicated")
        need(row["invariant"] == sf.primitive_closure_invariant(),
             "old-closure certificate mismatch")
        need(row["score"] == score(row["parent"], flat, behavior),
             "hybrid score drifted")
        need(row["previous_sha256"] == prev and
             type(row["chain_sha256"]) is str and
             HASH64.fullmatch(row["chain_sha256"]) and
             row["chain_sha256"] == digest({
                 k: v for k, v in row.items() if k != "chain_sha256"}),
             "hybrid receipt hash chain broken")
        prev = row["chain_sha256"]
        parentmap[row["id"]] = row
        seen.add(behavior["behavior_sha256"])
    need(state["last_utc_day"] == last, "hybrid UTC day mismatch")
    return state


def plan(state, generic, semantic, day, head):
    sf.day_check(day)
    need(type(head) is str and HEAD40.fullmatch(head),
         "exact trusted main SHA required")
    validate_state(state, generic, semantic)
    need(state["last_utc_day"] is None or day >= state["last_utc_day"],
         "UTC time moved backwards")
    if state["last_utc_day"] == day:
        return {"schema_version": SCHEMA, "candidate": False,
                "day": day, "head_sha": head, "reason": "ALREADY_VERIFIED_TODAY"}
    if len(state["receipts"]) >= MAX_RECEIPTS:
        return {"schema_version": SCHEMA, "candidate": False,
                "day": day, "head_sha": head, "reason": "HYBRID_BUDGET_EXHAUSTED"}
    selected, considered = select(state["receipts"], generic, semantic)
    if selected is None:
        return {"schema_version": SCHEMA, "candidate": False,
                "day": day, "head_sha": head, "reason": "NO_NEW_HYBRID"}
    return {"schema_version": SCHEMA, "candidate": True, "day": day,
            "head_sha": head,
            "source_generic": sources(generic, semantic)[0],
            "source_semantic": sources(generic, semantic)[1],
            "proposal": selected, "considered": considered,
            "status": "PENDING_FULL_DOMAIN_DUAL_EXECUTOR_CHECK"}


def prepare(generic_path, semantic_path, state_path, head, day, output):
    generic, semantic, state = (read(generic_path), read(semantic_path),
                                read(state_path))
    need(not output.exists() or not any(output.iterdir()),
         "nonempty output may contain stale evidence")
    proposed = plan(state, generic, semantic, day, head)
    output.mkdir(parents=True, exist_ok=True)
    write(output / "plan.json", proposed)
    print(json.dumps({"candidate": proposed["candidate"],
                      "id": proposed.get("proposal", {}).get("id"),
                      "parent": proposed.get("proposal", {}).get("parent"),
                      "considered": proposed.get("considered")}))
    return proposed


def seal(generic_path, semantic_path, state_path, head, evidence, output):
    generic, semantic, state = (read(generic_path), read(semantic_path),
                                read(state_path))
    submitted = read(evidence / "plan.json")
    expected = plan(state, generic, semantic, submitted["day"], head)
    need(expected == submitted and expected["candidate"] is True,
         "stale/tampered candidate; no verified write")
    item = expected["proposal"]
    gmap, smap = checked_upstream(generic, semantic)
    need(item["behavior"] == evaluate(item["flattened"], gmap, smap),
         "independent full-domain behavior mismatch")
    row = {**item, "day": expected["day"], "head_sha": head,
           "source_generic": expected["source_generic"],
           "source_semantic": expected["source_semantic"],
           "evaluator": EVALUATOR, "status": STATUS,
           "previous_sha256": (state["receipts"][-1]["chain_sha256"]
                               if state["receipts"] else ZERO)}
    row["chain_sha256"] = digest(row)
    result = {"schema_version": SCHEMA, "last_utc_day": expected["day"],
              "receipts": state["receipts"] + [row]}
    validate_state(result, generic, semantic)
    write(output, result)
    print(json.dumps({"verified": row["id"],
                      "parent": row["parent"],
                      "hybrid_tokens": len(row["flattened"]),
                      "full_domain_inputs": 256,
                      "strict_old_closure_separation": True}))
    return result


def use(generic, semantic, state, operator_id_text, values):
    validate_state(state, generic, semantic)
    need(type(operator_id_text) is str and IDENT.fullmatch(operator_id_text),
         "invalid verified hybrid id")
    found = [r for r in state["receipts"] if r["id"] == operator_id_text]
    need(len(found) == 1, "hybrid operator unverified")
    need(type(values) is list and len(values) == 4 and
         all(type(x) is int and 0 <= x <= 3 for x in values),
         "signal input must contain four two-bit samples")
    value = gf.encoded("signal4", values)
    gmap, smap = checked_upstream(generic, semantic)
    a = execute(found[0]["flattened"], value, "readable", gmap, smap)
    b = execute(found[0]["flattened"], value, "packed", gmap, smap)
    need(a == b, "hybrid execution disagreement")
    return {"operator_id": operator_id_text,
            "input": values, "output": gf.digits("signal4", a),
            "trusted_data_tokens": found[0]["flattened"],
            "old_primitive_closure_excluded": True}


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("command", choices=("prepare", "seal", "run"))
    p.add_argument("--generic", required=True, type=Path)
    p.add_argument("--semantic", required=True, type=Path)
    p.add_argument("--state", required=True, type=Path)
    p.add_argument("--head")
    p.add_argument("--day")
    p.add_argument("--output", type=Path)
    p.add_argument("--evidence", type=Path)
    p.add_argument("--operator-id")
    p.add_argument("--signal-json")
    args = p.parse_args(argv)
    try:
        if args.command == "prepare":
            need(args.head and args.day and args.output, "prepare args required")
            prepare(args.generic, args.semantic, args.state, args.head,
                    args.day, args.output)
        elif args.command == "seal":
            need(args.head and args.evidence and args.output,
                 "seal args required")
            seal(args.generic, args.semantic, args.state, args.head,
                 args.evidence, args.output)
        else:
            need(args.operator_id and args.signal_json, "run args required")
            signal = json.loads(args.signal_json,
                                object_pairs_hook=gf.unique_json)
            print(json.dumps(use(read(args.generic), read(args.semantic),
                                 read(args.state), args.operator_id, signal)))
        return 0
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError,
            IndexError) as exc:
        print("SEMANTIC_BRIDGE_ERROR: " + str(exc), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
