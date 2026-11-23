#!/usr/bin/env python3
"""Generic Forge: typed, cross-domain operator creation with exhaustive auditing.

Generates reusable *data-defined* operators, not Python source.  Uses one
Generator / Environment / Evaluator interface for image patterns and short
quantized signals.  Verified macros become generator inputs in later runs.

No arbitrary eval, scripts, external AI API, Lean dependency, or main writes.
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

SCHEMA = 1
EVALUATOR = "generic-forge-v1-exhaustive-two-interpreters"
STATUS = "EXHAUSTIVELY_CHECKED_FINITE_OPERATOR"
DOMAINS = {
    "grid3": ("rotate_cw", "mirror_lr", "invert", "shift_right",
              "neighbor_xor", "dilate"),
    "signal4": ("reverse", "rotate_left", "add_one", "delta_xor",
                "clip_top", "swap_pairs"),
}
DOMAIN_SIZE = {"grid3": 512, "signal4": 256}
MAX_PROGRAM = 8
MAX_PARENTS_PER_DOMAIN = 10
MAX_RECORDS = 96
MAX_PROPOSALS = 1000
STATE_KEYS = {"schema_version", "last_utc_day", "receipts"}
RECEIPT_KEYS = {
    "id", "day", "head_sha", "domain", "left", "right", "program",
    "evaluator", "behavior", "score", "status",
    "previous_sha256", "chain_sha256",
}
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
HEAD40 = re.compile(r"[0-9a-f]{40}\Z")
IDENT = re.compile(r"gf_[0-9a-f]{16}\Z")
ZERO = "0" * 64


def require(value, message):
    if not value:
        raise ValueError(message)


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False,
                      separators=(",", ":")).encode("utf-8")


def digest(value):
    return sha256(canonical(value)).hexdigest()


def read(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), "missing regular JSON")
    require(path.stat().st_size <= 500_000, "state file over size bound")
    return json.loads(path.read_text(encoding="utf-8"),
                      object_pairs_hook=unique_json)


def unique_json(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key")
        result[key] = value
    return result


def save(path, data):
    path = Path(path)
    require(not path.is_symlink(), "symlink output forbidden")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, sort_keys=True, ensure_ascii=False,
                               indent=2) + "\n", encoding="utf-8")


def empty_state():
    return {"schema_version": SCHEMA, "last_utc_day": None, "receipts": []}


def check_day(value):
    require(type(value) is str and
            re.fullmatch(r"\d{4}-\d{2}-\d{2}", value),
            "UTC date format")
    require(date.fromisoformat(value).isoformat() == value, "invalid date")


def digits(domain, integer):
    require(domain in DOMAINS and type(integer) is int and
            0 <= integer < DOMAIN_SIZE[domain], "bad environment input")
    if domain == "grid3":
        return [(integer >> i) & 1 for i in range(9)]
    return [(integer >> (2 * i)) & 3 for i in range(4)]


def encoded(domain, values):
    width = 1 if domain == "grid3" else 2
    return sum(int(value) << (width * i) for i, value in enumerate(values))


def reference_primitive(domain, op, value):
    """Readable cell-based reference environment."""
    require(op in DOMAINS[domain], "unknown primitive operation")
    v = digits(domain, value)
    if domain == "grid3":
        def at(r, c):
            return v[r * 3 + c] if 0 <= r < 3 and 0 <= c < 3 else 0
        out = [0] * 9
        for r in range(3):
            for c in range(3):
                i = r * 3 + c
                if op == "rotate_cw":
                    out[c * 3 + 2 - r] = v[i]
                elif op == "mirror_lr":
                    out[r * 3 + 2 - c] = v[i]
                elif op == "invert":
                    out[i] = 1 - v[i]
                elif op == "shift_right":
                    if c + 1 < 3:
                        out[r * 3 + c + 1] = v[i]
                elif op == "neighbor_xor":
                    out[i] = (v[i] ^ at(r - 1, c) ^ at(r + 1, c)
                              ^ at(r, c - 1) ^ at(r, c + 1))
                elif op == "dilate":
                    out[i] = int(any((v[i], at(r-1, c), at(r+1, c),
                                      at(r, c-1), at(r, c+1))))
        return encoded(domain, out)
    if op == "reverse":
        out = list(reversed(v))
    elif op == "rotate_left":
        out = v[1:] + v[:1]
    elif op == "add_one":
        out = [(x + 1) % 4 for x in v]
    elif op == "delta_xor":
        out = [x ^ v[(i + 1) % 4] for i, x in enumerate(v)]
    elif op == "clip_top":
        out = [int(x >= 2) for x in v]
    else:
        out = [v[1], v[0], v[3], v[2]]
    return encoded(domain, out)


def independent_primitive(domain, op, value):
    """Separate integer/bit-mask implementation used as a finite oracle."""
    require(op in DOMAINS[domain], "unknown primitive operation")
    if domain == "grid3":
        bit = lambda r, c: ((value >> (3*r + c)) & 1
                            if 0 <= r < 3 and 0 <= c < 3 else 0)
        if op == "invert":
            return value ^ 511
        if op == "shift_right":
            return sum((((value >> (3*r)) & 7) << 1 & 7) << (3*r)
                       for r in range(3))
        result = 0
        for r in range(3):
            for c in range(3):
                if op == "rotate_cw":
                    b = bit(2 - c, r)
                elif op == "mirror_lr":
                    b = bit(r, 2 - c)
                else:
                    neighbors = (bit(r-1,c), bit(r+1,c),
                                 bit(r,c-1), bit(r,c+1))
                    if op == "neighbor_xor":
                        b = bit(r, c)
                        for x in neighbors:
                            b ^= x
                    else:
                        b = int(bit(r,c) == 1 or 1 in neighbors)
                result |= b << (3*r + c)
        return result
    get = lambda i: (value >> (2 * (i % 4))) & 3
    result = 0
    for i in range(4):
        if op == "reverse":
            x = get(3-i)
        elif op == "rotate_left":
            x = get(i+1)
        elif op == "add_one":
            x = (get(i) + 1) & 3
        elif op == "delta_xor":
            x = get(i) ^ get(i+1)
        elif op == "clip_top":
            x = 1 if get(i) & 2 else 0
        else:
            x = get(i ^ 1)
        result |= x << (2*i)
    return result


def check_program(domain, program):
    require(domain in DOMAINS, "unknown environment")
    require(type(program) is list and 1 <= len(program) <= MAX_PROGRAM,
            "invalid typed program length")
    require(all(type(x) is str and x in DOMAINS[domain] for x in program),
            "program includes unapproved executable operation")
    return program


def apply_program(domain, program, start, implementation):
    current = start
    for op in program:
        current = implementation(domain, op, current)
    return current


@lru_cache(maxsize=4096)
def audit(domain, ops):
    """Exhaustively compare two implementations on EVERY input in the domain."""
    program = list(ops)
    check_program(domain, program)
    n = DOMAIN_SIZE[domain]
    outputs = []
    for x in range(n):
        actual = apply_program(domain, program, x, reference_primitive)
        independent = apply_program(domain, program, x, independent_primitive)
        require(actual == independent and type(actual) is int
                and 0 <= actual < n, "independent environment check failed")
        outputs.append(actual)
    data = b"".join(x.to_bytes(2, "little") for x in outputs)
    return {
        "fingerprint": sha256(data).hexdigest(),
        "inputs_exhaustively_checked": n,
        "changed_inputs": sum(x != y for x, y in enumerate(outputs)),
        "distinct_outputs": len(set(outputs)),
        "sample_outputs": [outputs[i] for i in sorted(set((0, 1, 3, n//2, n-1)))],
    }


def primitive_tokens(domain):
    return [("p:" + op, [op]) for op in DOMAINS[domain]]


def verified_tokens(domain, history, *, all_parents=False):
    macros = [( "m:" + r["id"], r["program"])
              for r in history if r["domain"] == domain]
    return macros if all_parents else macros[-MAX_PARENTS_PER_DOMAIN:]


def token_lookup(domain, history, *, all_parents=False):
    return dict(primitive_tokens(domain) +
                verified_tokens(domain, history, all_parents=all_parents))


def make_id(domain, left, right, program):
    return "gf_" + digest({"domain": domain, "left": left,
                           "right": right, "program": program})[:16]


def score_candidate(domain, left, right, program, behavior, history):
    count_domain = sum(r["domain"] == domain for r in history)
    macro_parent = int(left.startswith("m:")) + int(right.startswith("m:"))
    size = DOMAIN_SIZE[domain]
    # A heuristic for *experimentation*, not a claim of creative merit.
    return (12 * macro_parent
            + 8 * int(behavior["distinct_outputs"] >= size // 4)
            + 4 * min(4, behavior["changed_inputs"] * 4 // size)
            + 5 * int(count_domain == 0)
            - max(0, len(program) - 3))


def choose(history):
    """Build fresh candidates from verified macros, not a fixed model catalog."""
    counts = Counter(r["domain"] for r in history)
    seen = {(r["domain"], r["behavior"]["fingerprint"]) for r in history}
    best = None
    examined = 0
    for domain in DOMAINS:
        # The one-step identity is derived explicitly (not an operator token).
        identity_hash = sha256(b"".join(
            x.to_bytes(2, "little") for x in range(DOMAIN_SIZE[domain]))).hexdigest()
        tokens = primitive_tokens(domain) + verified_tokens(domain, history)
        for left, left_ops in tokens:
            for right, right_ops in tokens:
                if examined >= MAX_PROPOSALS:
                    break
                program = left_ops + right_ops
                if len(program) > MAX_PROGRAM:
                    continue
                examined += 1
                behavior = audit(domain, tuple(program))
                if (domain, behavior["fingerprint"]) in seen or \
                        behavior["fingerprint"] == identity_hash or \
                        behavior["changed_inputs"] == 0:
                    continue
                novelty = score_candidate(domain, left, right, program,
                                          behavior, history)
                rank = (counts[domain], -novelty, len(program), domain, left, right)
                candidate = {"domain": domain, "left": left, "right": right,
                             "program": program, "behavior": behavior,
                             "score": novelty,
                             "id": make_id(domain, left, right, program)}
                if best is None or rank < best[0]:
                    best = (rank, candidate)
            if examined >= MAX_PROPOSALS:
                break
    return (best[1] if best is not None else None), examined


def validate_state(state):
    require(type(state) is dict and set(state) == STATE_KEYS and
            type(state["schema_version"]) is int and
            state["schema_version"] == SCHEMA, "invalid state schema")
    rows = state["receipts"]
    require(type(rows) is list and len(rows) <= MAX_RECORDS,
            "receipt limit reached or wrong type")
    previous, prev_date = ZERO, None
    accepted = []
    fingerprints = set()
    for row in rows:
        require(type(row) is dict and set(row) == RECEIPT_KEYS,
                "malformed accepted operator")
        check_day(row["day"])
        require(prev_date is None or prev_date < row["day"],
                "receipt days out of order")
        prev_date = row["day"]
        require(type(row["head_sha"]) is str and HEAD40.fullmatch(row["head_sha"]),
                "invalid source commit")
        domain = row["domain"]
        check_program(domain, row["program"])
        require(row["status"] == STATUS and row["evaluator"] == EVALUATOR,
                "unverified receipt or evaluator drift")
        available = token_lookup(domain, accepted, all_parents=True)
        require(row["left"] in available and row["right"] in available,
                "operator relies on unverified parent")
        require(row["program"] == available[row["left"]] + available[row["right"]],
                "operator program does not match declared composition")
        require(row["id"] == make_id(domain, row["left"], row["right"],
                                     row["program"]) and
                IDENT.fullmatch(row["id"]),
                "operator identity tampered")
        behavior = audit(domain, tuple(row["program"]))
        require(behavior == row["behavior"], "full-domain result changed")
        identity_hash = sha256(b"".join(
            x.to_bytes(2, "little") for x in range(DOMAIN_SIZE[domain]))).hexdigest()
        fp = (domain, behavior["fingerprint"])
        require(fp not in fingerprints and behavior["fingerprint"] != identity_hash,
                "duplicate or inert operator accepted")
        fingerprints.add(fp)
        require(type(row["score"]) is int and
                row["score"] == score_candidate(
                    domain, row["left"], row["right"],
                    row["program"], behavior, accepted),
                "operator score drifted")
        require(row["previous_sha256"] == previous and
                type(row["chain_sha256"]) is str and
                HEX64.fullmatch(row["chain_sha256"]) and
                row["chain_sha256"] == digest({
                    key: val for key, val in row.items() if key != "chain_sha256"}),
                "invalid hash-linked evidence history")
        previous = row["chain_sha256"]
        accepted.append(row)
    require(state["last_utc_day"] == prev_date,
            "last successful UTC day differs from history")
    return state


def plan(state, day, head):
    check_day(day)
    require(type(head) is str and HEAD40.fullmatch(head),
            "exact main SHA required")
    validate_state(state)
    require(state["last_utc_day"] is None or day >= state["last_utc_day"],
            "UTC date moved backwards")
    if state["last_utc_day"] == day:
        return {"schema_version": SCHEMA, "candidate": False,
                "day": day, "head_sha": head, "reason": "ALREADY_CERTIFIED_TODAY"}
    if len(state["receipts"]) >= MAX_RECORDS:
        return {"schema_version": SCHEMA, "candidate": False,
                "day": day, "head_sha": head, "reason": "SAFETY_BUDGET_REACHED"}
    candidate, examined = choose(state["receipts"])
    if candidate is None:
        return {"schema_version": SCHEMA, "candidate": False,
                "day": day, "head_sha": head,
                "reason": "NO_BEHAVIORALLY_NEW_OPERATOR_ON_FRONTIER",
                "candidates_checked": examined}
    return {"schema_version": SCHEMA, "candidate": True,
            "day": day, "head_sha": head, "operator": candidate,
            "candidates_checked": examined,
            "status": "CANDIDATE_AWAITING_INDEPENDENT_VERIFICATION"}


def prepare(state_path, day, head, output):
    state = read(state_path)
    require(not output.exists() or not any(output.iterdir()),
            "output folder must be empty")
    result = plan(state, day, head)
    output.mkdir(parents=True, exist_ok=True)
    save(output / "plan.json", result)
    print(json.dumps({"candidate": result["candidate"],
                      "domain": result.get("operator", {}).get("domain"),
                      "id": result.get("operator", {}).get("id"),
                      "candidates_checked": result.get("candidates_checked")}))
    return result


def receipt(state_path, head, evidence_dir, output):
    state = read(state_path)
    submitted = read(evidence_dir / "plan.json")
    expected = plan(state, submitted["day"], head)
    require(expected == submitted and expected["candidate"] is True,
            "stale or altered plan, no operator may be accepted")
    proposal = expected["operator"]
    domain = proposal["domain"]
    verified = audit(domain, tuple(proposal["program"]))
    require(verified == proposal["behavior"], "independent full-domain audit failed")
    record = {
        **proposal, "day": expected["day"], "head_sha": head,
        "evaluator": EVALUATOR, "status": STATUS,
        "previous_sha256": (state["receipts"][-1]["chain_sha256"]
                            if state["receipts"] else ZERO),
    }
    record["chain_sha256"] = digest(record)
    updated = {"schema_version": SCHEMA, "last_utc_day": expected["day"],
               "receipts": state["receipts"] + [record]}
    validate_state(updated)
    save(output, updated)
    print(json.dumps({"certified": record["id"], "domain": domain,
                      "operations": len(record["program"]),
                      "checked": verified["inputs_exhaustively_checked"],
                      "macros_saved": len(updated["receipts"])}))
    return updated


def display_value(domain, value):
    cells = digits(domain, value)
    if domain == "grid3":
        return ["".join("#" if cells[3*r + c] else "." for c in range(3))
                for r in range(3)]
    return cells


def use_operator(state, operator_id, value):
    """Apply a *previously certified* operator as a practical image/signal tool."""
    validate_state(state)
    require(type(operator_id) is str and IDENT.fullmatch(operator_id),
            "invalid operator identifier")
    matches = [r for r in state["receipts"] if r["id"] == operator_id]
    require(len(matches) == 1, "operator is not in the certified library")
    row = matches[0]
    domain = row["domain"]
    require(type(value) is int and 0 <= value < DOMAIN_SIZE[domain],
            "input outside operator's finite environment")
    actual = apply_program(domain, row["program"], value, reference_primitive)
    independent = apply_program(domain, row["program"], value,
                                independent_primitive)
    require(actual == independent, "operator semantics mismatch")
    return {"operator_id": operator_id, "domain": domain,
            "program": row["program"], "input": value, "output": actual,
            "input_view": display_value(domain, value),
            "output_view": display_value(domain, actual),
            "verified_by": row["evaluator"]}


def main(argv=None):
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("command", choices=("prepare", "receipt", "run"))
    cli.add_argument("--state", required=True, type=Path)
    cli.add_argument("--head")
    cli.add_argument("--day")
    cli.add_argument("--output", required=True, type=Path)
    cli.add_argument("--evidence", type=Path)
    cli.add_argument("--operator-id")
    cli.add_argument("--value", type=int)
    args = cli.parse_args(argv)
    try:
        if args.command == "prepare":
            require(args.day is not None, "--day required")
            prepare(args.state, args.day, args.head, args.output)
        elif args.command == "receipt":
            require(args.evidence is not None, "evidence required")
            receipt(args.state, args.head, args.evidence, args.output)
        else:
            require(args.operator_id is not None and args.value is not None,
                    "--operator-id and --value required")
            print(json.dumps(use_operator(read(args.state), args.operator_id,
                                          args.value), ensure_ascii=False))
        return 0
    except (ValueError, OSError, TypeError, KeyError, IndexError) as exc:
        print("GENERIC_FORGE_ERROR: " + str(exc), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
