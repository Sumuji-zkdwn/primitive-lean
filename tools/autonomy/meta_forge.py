#!/usr/bin/env python3
"""Meta Forge: generate, test, save and reuse rules *that generate operators*.

A rule is a typed, non-executable transformation from a primitive program to
another primitive program. Rules are learned by composition of reviewed small
rewrite operations; only fully evaluated rules become parents of new rules.

The execution of image/signal programs is delegated to Generic Forge, which
independently checks each generated program on its entire finite domain.
"""
from __future__ import annotations

from collections import Counter
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
EVALUATOR = "meta-forge-v1-independent-rewrite-and-exhaustive-program"
STATUS = "EVALUATED_META_RULE_FINITE_ONLY"
ZERO = "0" * 64
MAX_RULE_STEPS = 4
MAX_HISTORY = 64
# The permanent MAX_HISTORY ceiling bounds unattended operation.
MAX_EVALUATIONS = 88
MAX_PARENT_RULES = 8
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
HEAD40 = re.compile(r"[0-9a-f]{40}\Z")
RULE_ID = re.compile(r"mf_[0-9a-f]{16}\Z")
STATE_KEYS = {"schema_version", "last_utc_day", "rules"}
RECEIPT_KEYS = {
    "id", "parent", "steps", "day", "head_sha", "evaluator",
    "fingerprint", "coverage", "score", "status",
    "previous_sha256", "chain_sha256",
}

# These are *interpreted transformations*, never runnable generated source.
OPS = ("reverse", "rotate_left", "duplicate_head", "duplicate_tail",
       "append", "prepend", "replace_head", "replace_tail",
       "wrap", "drop_head", "drop_tail")
PARAM_OPS = frozenset(("append", "prepend", "replace_head",
                       "replace_tail", "wrap"))
SLOT_COUNT = len(next(iter(gf.DOMAINS.values())))
assert all(len(names) == SLOT_COUNT for names in gf.DOMAINS.values())

# A separate challenge set probes other source programs. Because selection
# uses its outcomes, it is NOT a statistically blind holdout. Each generated
# operator is nevertheless exhaustively checked on ALL finite data inputs.
TRAIN = ((0,), (1, 2), (3, 0))
HOLDOUT = ((2, 4), (5, 1), (4, 0, 3))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(obj):
    return json.dumps(obj, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":")).encode("utf-8")


def digest(obj):
    return sha256(canonical(obj)).hexdigest()


def load(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(),
            "state must be an ordinary file")
    require(path.stat().st_size <= 450_000, "state size limit exceeded")
    return json.loads(path.read_text("utf-8"),
                      object_pairs_hook=gf.unique_json)


def save(path, obj):
    path = Path(path)
    require(not path.is_symlink(), "state destination cannot be symlink")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, ensure_ascii=False, sort_keys=True,
                               indent=2) + "\n", encoding="utf-8")


def empty_state():
    return {"schema_version": SCHEMA, "last_utc_day": None, "rules": []}


def check_day(value):
    # Use the same strictly parsed UTC slot format as Generic Forge.
    gf.check_day(value)


def step_atoms():
    """Small typed grammar; the *rules* are generated compositions of atoms."""
    for name in OPS:
        if name in PARAM_OPS:
            for slot in range(SLOT_COUNT):
                yield {"op": name, "slot": slot}
        else:
            yield {"op": name}


def check_steps(steps):
    require(type(steps) is list and 1 <= len(steps) <= MAX_RULE_STEPS,
            "meta-rule length outside trusted limits")
    for step in steps:
        require(type(step) is dict and type(step.get("op")) is str
                and step["op"] in OPS, "unrecognized meta-rule operation")
        op = step["op"]
        if op in PARAM_OPS:
            require(set(step) == {"op", "slot"} and
                    type(step["slot"]) is int and
                    0 <= step["slot"] < SLOT_COUNT,
                    "untrusted operation argument")
        else:
            require(set(step) == {"op"}, "unexpected operation parameters")
    return steps


def valid_program(domain, program):
    require(domain in gf.DOMAINS, "unknown environment domain")
    require(type(program) is list and 1 <= len(program) <= gf.MAX_PROGRAM
            and all(type(x) is str and x in gf.DOMAINS[domain]
                    for x in program), "invalid operator input")
    return program


def rewrite_reference(domain, steps, seed):
    """Simple list-based interpreter for a generated higher-order rule."""
    check_steps(steps)
    word = list(valid_program(domain, seed))
    names = gf.DOMAINS[domain]
    for atom in steps:
        op = atom["op"]
        token = names[atom["slot"]] if "slot" in atom else None
        if op == "reverse":
            word = word[::-1]
        elif op == "rotate_left":
            word = word[1:] + word[:1]
        elif op == "duplicate_head":
            word = [word[0]] + word
        elif op == "duplicate_tail":
            word = word + [word[-1]]
        elif op == "append":
            word = word + [token]
        elif op == "prepend":
            word = [token] + word
        elif op == "replace_head":
            word = [token] + word[1:]
        elif op == "replace_tail":
            word = word[:-1] + [token]
        elif op == "wrap":
            word = [token] + word + [token]
        elif op == "drop_head":
            word = word[1:]
        else:
            word = word[:-1]
        require(1 <= len(word) <= gf.MAX_PROGRAM,
                "generated program exceeds finite interpreter capacity")
    return valid_program(domain, word)


def rewrite_independent(domain, steps, seed):
    """A separately implemented index/deque interpreter, not a call above."""
    from collections import deque
    check_steps(steps)
    valid_program(domain, seed)
    names = gf.DOMAINS[domain]
    word = deque(seed)
    for atom in steps:
        op = atom["op"]
        token = names[atom["slot"]] if "slot" in atom else None
        if op == "reverse":
            word.reverse()
        elif op == "rotate_left":
            word.rotate(-1)
        elif op == "duplicate_head":
            word.appendleft(word[0])
        elif op == "duplicate_tail":
            word.append(word[-1])
        elif op == "append":
            word.append(token)
        elif op == "prepend":
            word.appendleft(token)
        elif op == "replace_head":
            word.popleft()
            word.appendleft(token)
        elif op == "replace_tail":
            word.pop()
            word.append(token)
        elif op == "wrap":
            word.appendleft(token)
            word.append(token)
        elif op == "drop_head":
            word.popleft()
        else:
            word.pop()
        require(1 <= len(word) <= gf.MAX_PROGRAM,
                "generated program exceeds finite interpreter capacity")
    return valid_program(domain, list(word))


def seed_program(domain, indices):
    return [gf.DOMAINS[domain][i] for i in indices]


@lru_cache(maxsize=4096)
def evaluate_steps(step_json):
    """Cross-domain behavior signatures; no training sample input shortcut.

    Every generated *program* is checked by GF's two independent executors
    over all 512 bitmap / 256 signal inputs, for all six source programs.
    """
    steps = json.loads(step_json)
    check_steps(steps)
    signatures, seen_fingerprints = [], set()
    train_changes = holdout_changes = changed_inputs = 0
    for domain in gf.DOMAINS:
        for collection, sequences in (("train", TRAIN), ("holdout", HOLDOUT)):
            for indices in sequences:
                before = seed_program(domain, indices)
                try:
                    result = rewrite_reference(domain, steps, before)
                    second = rewrite_independent(domain, steps, before)
                except ValueError:
                    return None
                require(result == second, "meta-interpreter implementations disagree")
                source = gf.audit(domain, tuple(before))
                target = gf.audit(domain, tuple(result))
                is_new = source["fingerprint"] != target["fingerprint"]
                if collection == "train":
                    train_changes += int(is_new)
                else:
                    holdout_changes += int(is_new)
                changed_inputs += target["changed_inputs"]
                signatures.append([domain, collection, list(indices),
                                   target["fingerprint"]])
                seen_fingerprints.add((domain, target["fingerprint"]))
    # Each domain must show a nontrivial effect on an unseen program.
    if train_changes < 2 or holdout_changes < 2:
        return None
    for domain in gf.DOMAINS:
        if not any(row[0] == domain and row[3] !=
                   gf.audit(domain, tuple(seed_program(domain, row[2])))["fingerprint"]
                   for row in signatures if row[1] == "holdout"):
            return None
    return {
        "fingerprint": digest(signatures),
        "train_changed": train_changes,
        "holdout_changed": holdout_changes,
        "distinct_semantics": len(seen_fingerprints),
        "total_source_programs": len(signatures),
        "data_inputs_exhaustively_checked":
            sum(gf.DOMAIN_SIZE[domain] * (len(TRAIN) + len(HOLDOUT))
                for domain in gf.DOMAINS),
    }


def fingerprint_for(steps):
    result = evaluate_steps(canonical(steps).decode("utf-8"))
    require(result is not None, "rule failed independent domain checks")
    return result


def rule_id(steps):
    return "mf_" + digest({"steps": check_steps(steps)})[:16]


def score(steps, coverage, parent, history):
    old = Counter(row["steps"][-1]["op"] for row in history)
    dom = coverage
    return (5 * dom["train_changed"] + 7 * dom["holdout_changed"]
            + 2 * dom["distinct_semantics"]
            + (18 if parent is not None else 0)
            + (9 if old[steps[-1]["op"]] == 0 else 0)
            - 2 * len(steps))


def generate(history):
    """Generate rule *descriptions* from verified earlier rule descriptions."""
    seen = {rule_id(row["steps"]) for row in history}
    candidates = []
    ancestors = history[-MAX_PARENT_RULES:]
    for atom in step_atoms():
        candidates.append((None, [atom]))
        for parent in ancestors:
            if len(parent["steps"]) < MAX_RULE_STEPS:
                candidates.append((parent["id"], parent["steps"] + [atom]))
    return [(parent, steps) for parent, steps in candidates
            if rule_id(steps) not in seen]


def choose(history):
    offered = generate(history)
    # Prefer a previously certified meta-rule as parent after the first
    # receipt, but fall back to a new root if none yields valid new behavior.
    ranked = []
    count = 0
    for parent, steps in offered:
        if count >= MAX_EVALUATIONS:
            break
        count += 1
        coverage = evaluate_steps(canonical(steps).decode("utf-8"))
        if coverage is None:
            continue
        if any(row["fingerprint"] == coverage["fingerprint"] for row in history):
            continue
        value = score(steps, coverage, parent, history)
        key = (0 if parent is not None else 1,
               -value, len(steps), canonical(steps).decode("utf-8"))
        ranked.append((key, {
            "id": rule_id(steps),
            "parent": parent, "steps": steps, "fingerprint": coverage["fingerprint"],
            "coverage": coverage, "score": value,
        }))
    if not ranked:
        return None, count
    ranked.sort(key=lambda x: x[0])
    return ranked[0][1], count


def validate_state(state):
    require(type(state) is dict and set(state) == STATE_KEYS
            and type(state["schema_version"]) is int
            and state["schema_version"] == SCHEMA, "state format drift")
    receipts = state["rules"]
    require(type(receipts) is list and len(receipts) <= MAX_HISTORY,
            "state exceeds receipt limit")
    previous, last_day = ZERO, None
    accepted, ids, behaviors = [], set(), set()
    for row in receipts:
        require(type(row) is dict and set(row) == RECEIPT_KEYS,
                "malformed rule receipt")
        check_day(row["day"])
        require(last_day is None or last_day < row["day"],
                "UTC days must be strictly increasing")
        last_day = row["day"]
        require(type(row["head_sha"]) is str and HEAD40.fullmatch(row["head_sha"]),
                "invalid exact controller source")
        require(row["evaluator"] == EVALUATOR and row["status"] == STATUS,
                "unknown evaluator or unverified rule")
        check_steps(row["steps"])
        require(row["id"] == rule_id(row["steps"]) and
                RULE_ID.fullmatch(row["id"]) and
                row["id"] not in ids, "rule ID is invalid or duplicated")
        if row["parent"] is not None:
            matches = [r for r in accepted if r["id"] == row["parent"]]
            require(len(matches) == 1 and
                    row["steps"][:-1] == matches[0]["steps"],
                    "rule does not descend from a verified parent")
        checks = fingerprint_for(row["steps"])
        require(row["coverage"] == checks and
                row["fingerprint"] == checks["fingerprint"] and
                checks["fingerprint"] not in behaviors,
                "rule does not have independently verified unique behavior")
        require(type(row["score"]) is int and
                row["score"] == score(row["steps"], checks,
                                      row["parent"], accepted),
                "meta-rule evaluation score drifted")
        require(row["previous_sha256"] == previous and
                type(row["chain_sha256"]) is str and
                HEX64.fullmatch(row["chain_sha256"]) and
                row["chain_sha256"] == digest({
                    key: val for key, val in row.items() if key != "chain_sha256"
                }), "broken rule evidence chain")
        previous = row["chain_sha256"]
        ids.add(row["id"])
        behaviors.add(row["fingerprint"])
        accepted.append(row)
    require(state["last_utc_day"] == last_day,
            "last day is inconsistent with receipts")
    return state


def plan(state, day, head):
    check_day(day)
    require(type(head) is str and HEAD40.fullmatch(head),
            "exact main commit SHA required")
    validate_state(state)
    require(state["last_utc_day"] is None or state["last_utc_day"] <= day,
            "clock moved backwards")
    if state["last_utc_day"] == day:
        return {"schema_version": SCHEMA, "candidate": False,
                "day": day, "head_sha": head, "reason": "ALREADY_EVALUATED_TODAY"}
    if len(state["rules"]) >= MAX_HISTORY:
        return {"schema_version": SCHEMA, "candidate": False,
                "day": day, "head_sha": head, "reason": "VERIFIED_RULE_LIMIT"}
    candidate, tested = choose(state["rules"])
    if candidate is None:
        return {"schema_version": SCHEMA, "candidate": False,
                "day": day, "head_sha": head, "reason": "NO_NEW_VERIFIABLE_RULE",
                "candidates_tested": tested}
    return {"schema_version": SCHEMA, "candidate": True, "day": day,
            "head_sha": head, "rule": candidate, "candidates_tested": tested,
            "status": "UNVERIFIED_META_RULE_CANDIDATE"}


def prepare(state_file, day, head, output):
    state = load(state_file)
    require(not output.exists() or not any(output.iterdir()),
            "output must start empty to prevent stale evidence")
    candidate = plan(state, day, head)
    output.mkdir(parents=True, exist_ok=True)
    save(output / "proposal.json", candidate)
    print(json.dumps({"candidate": candidate["candidate"],
                      "id": candidate.get("rule", {}).get("id"),
                      "parent": candidate.get("rule", {}).get("parent"),
                      "tested": candidate.get("candidates_tested"),
                      "reason": candidate.get("reason")}))
    return candidate


def receipt(state_file, head, evidence_dir, output):
    state = load(state_file)
    presented = load(evidence_dir / "proposal.json")
    expected = plan(state, presented["day"], head)
    require(expected == presented and expected["candidate"],
            "modified candidate or stale state: no receipt")
    entry = expected["rule"]
    verified = fingerprint_for(entry["steps"])
    require(verified == entry["coverage"], "independent rule verification failed")
    row = {
        **entry, "day": expected["day"], "head_sha": head,
        "evaluator": EVALUATOR, "status": STATUS,
        "previous_sha256": (state["rules"][-1]["chain_sha256"]
                            if state["rules"] else ZERO),
    }
    row["chain_sha256"] = digest(row)
    updated = {"schema_version": SCHEMA, "last_utc_day": expected["day"],
               "rules": state["rules"] + [row]}
    validate_state(updated)
    save(output, updated)
    print(json.dumps({"certified_meta_rule": row["id"],
                      "parent": row["parent"],
                      "steps": len(row["steps"]),
                      "exhaustive_data_inputs": verified["data_inputs_exhaustively_checked"],
                      "saved_rules": len(updated["rules"])}))
    return updated


def use_rule(state, rule_id_text, domain, source):
    """Use a certified higher-order rule to CREATE a runnable operator program."""
    validate_state(state)
    require(type(rule_id_text) is str and RULE_ID.fullmatch(rule_id_text),
            "invalid rule ID")
    matches = [row for row in state["rules"] if row["id"] == rule_id_text]
    require(len(matches) == 1, "rule not in verified library")
    seed = valid_program(domain, source)
    expanded = rewrite_reference(domain, matches[0]["steps"], seed)
    independent = rewrite_independent(domain, matches[0]["steps"], seed)
    require(expanded == independent, "generated operator differs between interpreters")
    # Independent execution of the constructed operator on every possible input.
    base_behavior = gf.audit(domain, tuple(seed))
    new_behavior = gf.audit(domain, tuple(expanded))
    return {
        "rule_id": rule_id_text, "domain": domain, "seed": seed,
        "generated_program": expanded,
        "source_behavior": base_behavior["fingerprint"],
        "generated_behavior": new_behavior["fingerprint"],
        "full_domain_inputs_checked": gf.DOMAIN_SIZE[domain],
        "behavior_changed": base_behavior["fingerprint"] != new_behavior["fingerprint"],
    }


def main(argv=None):
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("command", choices=("prepare", "receipt", "apply"))
    cli.add_argument("--state", required=True, type=Path)
    cli.add_argument("--day")
    cli.add_argument("--head")
    cli.add_argument("--output", type=Path)
    cli.add_argument("--evidence", type=Path)
    cli.add_argument("--rule-id")
    cli.add_argument("--domain")
    cli.add_argument("--program-json")
    args = cli.parse_args(argv)
    try:
        if args.command == "prepare":
            require(args.day is not None and args.head is not None
                    and args.output is not None, "prepare missing arguments")
            prepare(args.state, args.day, args.head, args.output)
        elif args.command == "receipt":
            require(args.head is not None and args.evidence is not None
                    and args.output is not None, "receipt missing arguments")
            receipt(args.state, args.head, args.evidence, args.output)
        else:
            require(args.rule_id and args.domain and args.program_json,
                    "apply requires --rule-id, --domain, --program-json")
            program = json.loads(args.program_json, object_pairs_hook=gf.unique_json)
            print(json.dumps(use_rule(load(args.state), args.rule_id,
                                     args.domain, program), ensure_ascii=False))
        return 0
    except (ValueError, TypeError, KeyError, OSError, IndexError,
            json.JSONDecodeError) as exc:
        print("META_FORGE_ERROR: " + str(exc), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
