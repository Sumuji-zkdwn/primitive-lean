#!/usr/bin/env python3
"""Semantic Foundry: synthesize genuinely new bounded signal operators as data.

Contrast with Generic Forge, which composes a fixed primitive repertoire.
Here a typed *new semantic construction* (extremum location) is generated,
tested by independent interpreters, and differentiated from EVERY composition
of the old signal primitives by a closed invariant.

Signal4 is finite (4 samples of 2 bits = 256 inputs). This is NOT arbitrary
new executable code and not automatic invention of new physics or mathematics.
"""
from __future__ import annotations

from datetime import date
from functools import lru_cache
from hashlib import sha256
import argparse
import json
from pathlib import Path
import re
import sys

from tools.autonomy import generic_forge as gf

SCHEMA = 1
EVALUATOR = "semantic-foundry-v1-two-executors-and-closure-invariant"
STATUS = "EXHAUSTIVE_FINITE_SEMANTIC_SEPARATION"
STATE_KEYS = {"schema_version", "last_utc_day", "receipts"}
RECEIPT_KEYS = {
    "id", "day", "head_sha", "parent", "recipe", "score",
    "observation", "invariant", "evaluator", "status",
    "previous_sha256", "chain_sha256",
}
DOMAIN = "signal4"
MAX_STEPS = 5
MAX_RECEIPTS = 24
MAX_CANDIDATES = 120
MAX_PARENTS = 8
ZERO_HASH = "0" * 64
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
HEAD40 = re.compile(r"[0-9a-f]{40}\Z")
ID = re.compile(r"sf_[0-9a-f]{16}\Z")
ORDERS = ("max", "min")
TIES = ("first", "last")
LEVELS = (1, 2, 3)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":")).encode("utf-8")


def digest(value):
    return sha256(canonical(value)).hexdigest()


def json_pairs_unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "repeated JSON key")
        result[key] = value
    return result


def read(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), "missing plain JSON state")
    require(path.stat().st_size <= 500_000, "state input too large")
    return json.loads(path.read_text("utf-8"), object_pairs_hook=json_pairs_unique)


def write(path, value):
    path = Path(path)
    require(not path.is_symlink(), "output path is a symlink")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, indent=2,
                               ensure_ascii=False) + "\n", encoding="utf-8")


def day_check(day):
    require(type(day) is str and re.fullmatch(r"\d{4}-\d{2}-\d{2}", day),
            "UTC day format is YYYY-MM-DD")
    require(date.fromisoformat(day).isoformat() == day, "invalid UTC day")


def empty_state():
    return {"schema_version": SCHEMA, "last_utc_day": None, "receipts": []}


def validate_recipe(recipe):
    require(type(recipe) is list and 1 <= len(recipe) <= MAX_STEPS,
            "recipe length out of bounds")
    peaks = 0
    for item in recipe:
        require(type(item) is dict and type(item.get("kind")) is str,
                "invalid typed semantic step")
        if item["kind"] == "peak":
            require(set(item) == {"kind", "order", "tie", "level"}
                    and item["order"] in ORDERS and item["tie"] in TIES
                    and type(item["level"]) is int and item["level"] in LEVELS,
                    "invalid extremum semantics")
            peaks += 1
        elif item["kind"] == "existing":
            require(set(item) == {"kind", "name"} and
                    type(item["name"]) is str and
                    item["name"] in gf.DOMAINS[DOMAIN],
                    "unreviewed primitive execution name")
        else:
            raise ValueError("unapproved semantic operator category")
    require(peaks == 1, "exactly one new typed semantic construction required")
    return recipe


def reference_step(step, state):
    if step["kind"] == "existing":
        return gf.reference_primitive(DOMAIN, step["name"], state)
    vals = gf.digits(DOMAIN, state)
    target = max(vals) if step["order"] == "max" else min(vals)
    candidates = [i for i, val in enumerate(vals) if val == target]
    pos = candidates[0] if step["tie"] == "first" else candidates[-1]
    output = [0, 0, 0, 0]
    output[pos] = step["level"]
    return gf.encoded(DOMAIN, output)


def independent_step(step, state):
    """Packed-index reduction, separate from list/max/min implementation."""
    if step["kind"] == "existing":
        return gf.independent_primitive(DOMAIN, step["name"], state)
    mode, tie = step["order"], step["tie"]
    best, best_value = 0, state & 3
    for i in range(1, 4):
        current = (state >> (i * 2)) & 3
        better = (current > best_value if mode == "max"
                  else current < best_value)
        equal_last = current == best_value and tie == "last"
        if better or equal_last:
            best, best_value = i, current
    return step["level"] << (2 * best)


def apply_recipe(recipe, value, implementation):
    validate_recipe(recipe)
    require(type(value) is int and 0 <= value < 256,
            "input must be one of 256 signals")
    state = value
    for step in recipe:
        state = implementation(step, state)
    return state


@lru_cache(maxsize=1)
def primitive_closure_invariant():
    """Kernel of the separation argument: each old generator preserves CONST.

    Every composition also preserves CONST by mathematical induction.
    The finite base step is checked with both old independent executors
    on ALL four constant-valued signal inputs, not only a few samples.
    """
    checks = []
    for name in gf.DOMAINS[DOMAIN]:
        for value in range(4):
            x = gf.encoded(DOMAIN, [value] * 4)
            a = gf.reference_primitive(DOMAIN, name, x)
            b = gf.independent_primitive(DOMAIN, name, x)
            require(a == b, "original primitive implementation disagreement")
            out = gf.digits(DOMAIN, a)
            require(all(v == out[0] for v in out),
                    "OLD_CLOSURE_INVARIANT_FALSE_FOR_" + name)
            checks.append([name, value, a])
    return {"old_primitive_count": len(gf.DOMAINS[DOMAIN]),
            "constant_inputs_per_primitive": 4,
            "independent_base_checks": len(checks),
            "base_witness_sha256": digest(checks),
            "property": "all_constant_signals_map_to_constant_signals",
            "closure_argument":
                "composition_of_property_preserving_functions_preserves_property"}


@lru_cache(maxsize=8192)
def evaluate(recipe_json):
    """Exhaustively evaluate every signal input through two implementations."""
    recipe = json.loads(recipe_json, object_pairs_hook=json_pairs_unique)
    validate_recipe(recipe)
    out = []
    for x in range(gf.DOMAIN_SIZE[DOMAIN]):
        a = apply_recipe(recipe, x, reference_step)
        b = apply_recipe(recipe, x, independent_step)
        require(a == b and type(a) is int and 0 <= a < 256,
                "two semantic implementations disagree")
        out.append(a)
    constant_pairs = []
    for value in range(4):
        x = gf.encoded(DOMAIN, [value] * 4)
        y = out[x]
        cells = gf.digits(DOMAIN, y)
        if len(set(cells)) != 1:
            constant_pairs.append({"input": x, "output": y,
                                   "input_values": [value] * 4,
                                   "output_values": cells})
    basis = [1 << (2 * i) for i in range(4)]
    basis_outputs = [out[x] for x in basis]
    # Reject a fixed-position stamp disguised as 'new semantics'.
    if not constant_pairs or len(set(basis_outputs)) != 4:
        return None
    data = b"".join(y.to_bytes(1, "little") for y in out)
    return {"behavior_sha256": sha256(data).hexdigest(),
            "exhaustive_inputs": 256,
            "independent_implementations": 2,
            "changed_inputs": sum(x != y for x, y in enumerate(out)),
            "distinct_outputs": len(set(out)),
            "constant_counterexample": constant_pairs[0],
            "number_of_violating_constant_inputs": len(constant_pairs),
            "four_single_peak_outputs": basis_outputs,
            "nonfixed_position_response": len(set(basis_outputs)) == 4}


def certify(recipe):
    report = evaluate(canonical(recipe).decode("utf-8"))
    require(report is not None, "failed input-dependent closure separation")
    return report


def rule_id(recipe):
    return "sf_" + digest({"domain": DOMAIN, "recipe": validate_recipe(recipe)})[:16]


def candidates(history):
    """Generate candidates from typed parameters and *verified* descendants."""
    for mode in ORDERS:
        for tie in TIES:
            for level in LEVELS:
                yield None, [{"kind": "peak", "order": mode,
                              "tie": tie, "level": level}]
    for row in history[-MAX_PARENTS:]:
        if len(row["recipe"]) >= MAX_STEPS:
            continue
        for name in gf.DOMAINS[DOMAIN]:
            step = {"kind": "existing", "name": name}
            yield row["id"], row["recipe"] + [step]
            yield row["id"], [step] + row["recipe"]


def score(recipe, report, parent, history):
    """Optimization affects priority; *never* proof acceptance."""
    return (18 if parent is not None else 0) + \
           (2 * report["number_of_violating_constant_inputs"]) + \
           (4 * min(report["distinct_outputs"], 16)) + \
           (2 if len(recipe) == 1 else 0) - len(recipe)


def choose(history):
    seen_ids = {row["id"] for row in history}
    seen_behaviors = {row["observation"]["behavior_sha256"] for row in history}
    ranked, examined = [], 0
    for parent, recipe in candidates(history):
        if examined >= MAX_CANDIDATES:
            break
        examined += 1
        identifier = rule_id(recipe)
        if identifier in seen_ids:
            continue
        observed = evaluate(canonical(recipe).decode("utf-8"))
        if observed is None or observed["behavior_sha256"] in seen_behaviors:
            continue
        value = score(recipe, observed, parent, history)
        priority = (0 if parent else 1, -value, len(recipe),
                    canonical(recipe).decode("utf-8"))
        ranked.append((priority, {
            "id": identifier, "parent": parent, "recipe": recipe,
            "score": value, "observation": observed,
            "invariant": primitive_closure_invariant()}))
    if not ranked:
        return None, examined
    ranked.sort(key=lambda item: item[0])
    return ranked[0][1], examined


def validate_state(state):
    require(type(state) is dict and set(state) == STATE_KEYS and
            type(state.get("schema_version")) is int and
            state["schema_version"] == SCHEMA, "state schema drift")
    rows = state["receipts"]
    require(type(rows) is list and len(rows) <= MAX_RECEIPTS,
            "invalid verified recipe history size")
    previous, last_date, verified = ZERO_HASH, None, []
    seen = set()
    behaviors = set()
    for row in rows:
        require(type(row) is dict and set(row) == RECEIPT_KEYS,
                "unexpected semantic receipt fields")
        day_check(row["day"])
        require(last_date is None or row["day"] > last_date,
                "receipt UTC days must increase")
        last_date = row["day"]
        require(type(row["head_sha"]) is str and HEAD40.fullmatch(row["head_sha"]),
                "invalid source SHA")
        require(row["status"] == STATUS and row["evaluator"] == EVALUATOR,
                "unknown or self-asserted verifier")
        recipe = validate_recipe(row["recipe"])
        require(row["id"] == rule_id(recipe) and ID.fullmatch(row["id"])
                and row["id"] not in seen, "duplicate recipe identity")
        if row["parent"] is None:
            require(len(recipe) == 1 and recipe[0]["kind"] == "peak",
                    "root must be one generated peak expression")
        else:
            parents = [r for r in verified if r["id"] == row["parent"]]
            require(len(parents) == 1, "unverified semantic parent")
            parent = parents[0]["recipe"]
            require(len(recipe) == len(parent) + 1 and
                    (recipe[:len(parent)] == parent and
                     recipe[-1]["kind"] == "existing" or
                     recipe[1:] == parent and
                     recipe[0]["kind"] == "existing"),
                    "invalid expansion of verified semantic parent")
        independent = certify(recipe)
        require(row["observation"] == independent and
                row["invariant"] == primitive_closure_invariant(),
                "behavior or primitive closure invariant changed")
        require(independent["behavior_sha256"] not in behaviors,
                "no new observable behavior")
        require(type(row["score"]) is int and
                row["score"] == score(recipe, independent, row["parent"],
                                      verified),
                "candidate score drifted")
        require(row["previous_sha256"] == previous and
                type(row["chain_sha256"]) is str and
                HEX64.fullmatch(row["chain_sha256"]) and
                row["chain_sha256"] == digest({
                    key: value for key, value in row.items()
                    if key != "chain_sha256"
                }), "broken verified semantics chain")
        seen.add(row["id"])
        behaviors.add(independent["behavior_sha256"])
        previous = row["chain_sha256"]
        verified.append(row)
    require(state["last_utc_day"] == last_date,
            "last UTC day differs from final receipt")
    return state


def plan(state, day, head):
    day_check(day)
    require(type(head) is str and HEAD40.fullmatch(head),
            "exact repository source SHA required")
    validate_state(state)
    require(state["last_utc_day"] is None or day >= state["last_utc_day"],
            "UTC date moved backwards")
    if state["last_utc_day"] == day:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "ALREADY_VERIFIED_TODAY", "day": day,
                "head_sha": head}
    if len(state["receipts"]) >= MAX_RECEIPTS:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "MAINTENANCE_LIMIT", "day": day, "head_sha": head}
    proposed, examined = choose(state["receipts"])
    if proposed is None:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "BOUNDED_GRAMMAR_EXHAUSTED",
                "examined": examined, "day": day, "head_sha": head}
    return {"schema_version": SCHEMA, "candidate": True,
            "day": day, "head_sha": head, "proposal": proposed,
            "examined": examined,
            "guarantee": "FINITE_CONDITIONAL_SEPARATION_ONLY",
            "status": "AWAITING_INDEPENDENT_EVALUATION"}


def prepare(state_path, day, head, output):
    state = read(state_path)
    require(not output.exists() or not any(output.iterdir()),
            "nonempty evidence output: stale proof contamination")
    result = plan(state, day, head)
    output.mkdir(parents=True, exist_ok=True)
    write(output / "proposal.json", result)
    print(json.dumps({"candidate": result["candidate"],
                      "id": result.get("proposal", {}).get("id"),
                      "parent": result.get("proposal", {}).get("parent"),
                      "examined": result.get("examined"),
                      "verifier": EVALUATOR}))
    return result


def receipt(state_path, head, evidence, output):
    state = read(state_path)
    submitted = read(evidence / "proposal.json")
    expected = plan(state, submitted["day"], head)
    require(expected["candidate"] is True and expected == submitted,
            "stale/tampered candidate; refuse persistence")
    item = expected["proposal"]
    require(item["observation"] == certify(item["recipe"]) and
            item["invariant"] == primitive_closure_invariant(),
            "independent behavior/closure audit failed")
    row = {**item, "day": expected["day"], "head_sha": head,
           "evaluator": EVALUATOR, "status": STATUS,
           "previous_sha256": (state["receipts"][-1]["chain_sha256"]
                               if state["receipts"] else ZERO_HASH)}
    row["chain_sha256"] = digest(row)
    updated = {"schema_version": SCHEMA, "last_utc_day": expected["day"],
               "receipts": state["receipts"] + [row]}
    validate_state(updated)
    write(output, updated)
    print(json.dumps({"certified": row["id"],
                      "parent": row["parent"],
                      "exhaustively_checked": row["observation"]["exhaustive_inputs"],
                      "closure_invariant_violated": True,
                      "saved": len(updated["receipts"])}))
    return updated


def use(state, operator_id, signal):
    validate_state(state)
    require(type(operator_id) is str and ID.fullmatch(operator_id),
            "invalid certified operator ID")
    found = [r for r in state["receipts"] if r["id"] == operator_id]
    require(len(found) == 1, "unverified operator")
    require(type(signal) is list and len(signal) == 4 and
            all(type(x) is int and 0 <= x <= 3 for x in signal),
            "signal must be four values in 0..3")
    value = gf.encoded(DOMAIN, signal)
    a = apply_recipe(found[0]["recipe"], value, reference_step)
    b = apply_recipe(found[0]["recipe"], value, independent_step)
    require(a == b, "execution changed since independent certification")
    return {"operator_id": operator_id, "input": signal,
            "output": gf.digits(DOMAIN, a),
            "recipe": found[0]["recipe"],
            "outside_original_primitive_closure": True,
            "scope": "FOUR_SAMPLES_2_BITS_ONLY"}


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("command", choices=("prepare", "receipt", "run"))
    p.add_argument("--state", required=True, type=Path)
    p.add_argument("--day")
    p.add_argument("--head")
    p.add_argument("--evidence", type=Path)
    p.add_argument("--output", type=Path)
    p.add_argument("--operator-id")
    p.add_argument("--signal-json")
    args = p.parse_args(argv)
    try:
        if args.command == "prepare":
            require(args.day is not None and args.head is not None and
                    args.output is not None, "missing prepare arguments")
            prepare(args.state, args.day, args.head, args.output)
        elif args.command == "receipt":
            require(args.head is not None and args.evidence is not None and
                    args.output is not None, "missing receipt arguments")
            receipt(args.state, args.head, args.evidence, args.output)
        else:
            require(args.operator_id is not None and
                    args.signal_json is not None, "run input missing")
            signal = json.loads(args.signal_json, object_pairs_hook=json_pairs_unique)
            print(json.dumps(use(read(args.state), args.operator_id, signal)))
        return 0
    except (ValueError, KeyError, TypeError, OSError,
            json.JSONDecodeError, IndexError) as exc:
        print("SEMANTIC_FOUNDRY_ERROR: " + str(exc), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
